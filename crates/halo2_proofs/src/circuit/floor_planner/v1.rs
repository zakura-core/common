use std::{
    collections::HashMap,
    fmt,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use ff::Field;
use maybe_rayon::prelude::*;

use crate::{
    circuit::{
        Cell, Layouter, Region, RegionIndex, RegionStart, Table, TableLayouter, Value,
        layouter::{RegionColumn, RegionLayouter, RegionShape},
        table_layouter::{SimpleTableLayouter, compute_table_lengths},
    },
    plonk::{
        Advice, Any, Assigned, Assignment, Circuit, Column, Error, Fixed, FloorPlan, FloorPlanner,
        Instance, Selector, TableColumn,
    },
};

mod strategy;

/// The version 1 [`FloorPlanner`] provided by `halo2`.
///
/// - No column optimizations are performed. Circuit configuration is left entirely to the
///   circuit designer.
/// - A dual-pass layouter is used to measures regions prior to assignment.
/// - Regions are measured as rectangles, bounded on the cells they assign.
/// - Regions are laid out using a greedy first-fit strategy, after sorting regions by
///   their "advice area" (number of advice columns * rows).
#[derive(Debug)]
pub struct V1;

/// A [`V1`] floor planner that assigns regions to their planned locations by
/// fully-qualified annotation instead of synthesis order.
///
/// This lets witness assignment reorder independent regions while preserving
/// the circuit layout captured by a proving key. Region annotations and their
/// order among identically-named siblings are circuit-critical when using this
/// planner.
#[derive(Debug)]
pub struct V1Named;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RegionPath {
    namespace: Vec<String>,
    name: String,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RegionId {
    path: RegionPath,
    occurrence: usize,
}

#[derive(Debug, Default)]
struct RegionNameTracker {
    namespace: Vec<String>,
    occurrences: HashMap<RegionPath, usize>,
}

impl RegionNameTracker {
    fn next(&mut self, name: String) -> RegionId {
        let path = RegionPath {
            namespace: self.namespace.clone(),
            name,
        };
        let occurrence = self.occurrences.entry(path.clone()).or_default();
        let id = RegionId {
            path,
            occurrence: *occurrence,
        };
        *occurrence += 1;
        id
    }

    fn push_namespace(&mut self, name: String) {
        self.namespace.push(name);
    }

    fn pop_namespace(&mut self) {
        self.namespace.pop();
    }
}

#[derive(Debug)]
struct RegionLookup {
    namespace_children: Vec<HashMap<String, usize>>,
    region_indices: Vec<HashMap<String, Vec<RegionIndex>>>,
    region_count: usize,
}

impl RegionLookup {
    fn new(region_ids: Vec<RegionId>) -> Self {
        let mut lookup = Self {
            namespace_children: vec![HashMap::new()],
            region_indices: vec![HashMap::new()],
            region_count: region_ids.len(),
        };

        for (index, id) in region_ids.into_iter().enumerate() {
            let mut namespace = 0;
            for name in id.path.namespace {
                namespace = if let Some(child) = lookup.namespace_children[namespace].get(&name) {
                    *child
                } else {
                    let child = lookup.namespace_children.len();
                    lookup.namespace_children.push(HashMap::new());
                    lookup.region_indices.push(HashMap::new());
                    lookup.namespace_children[namespace].insert(name, child);
                    child
                };
            }

            let occurrences = lookup.region_indices[namespace]
                .entry(id.path.name)
                .or_default();
            debug_assert_eq!(occurrences.len(), id.occurrence);
            occurrences.push(index.into());
        }

        lookup
    }

    fn len(&self) -> usize {
        self.region_count
    }
}

struct V1Layout {
    /// Stores the starting row for each region.
    regions: Vec<RegionStart>,
    /// Maps each region's identity to its index in `regions`.
    region_lookup: RegionLookup,
    /// Stores the occupied rows in each global-constant column.
    fixed_allocations: Vec<(Column<Fixed>, strategy::Allocations)>,
    /// Stores the first row after all planned regions.
    first_unassigned_row: usize,
}

struct V1Plan<'a, F: Field, CS: Assignment<F> + 'a> {
    cs: &'a mut CS,
    /// Stores the starting row for each region.
    regions: Vec<RegionStart>,
    /// Stores the constants to be assigned, and the cells to which they are copied.
    constants: Vec<(Assigned<F>, Cell)>,
    /// Stores the table fixed columns.
    table_columns: Vec<TableColumn>,
}

impl<'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for V1Plan<'a, F, CS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("floor_planner::V1Plan").finish()
    }
}

impl<'a, F: Field, CS: Assignment<F>> V1Plan<'a, F, CS> {
    /// Creates a new v1 layouter.
    fn new(cs: &'a mut CS, regions: Vec<RegionStart>) -> Result<Self, Error> {
        let ret = V1Plan {
            cs,
            regions,
            constants: vec![],
            table_columns: vec![],
        };
        Ok(ret)
    }
}

impl FloorPlanner for V1 {
    fn synthesize<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<(), Error> {
        let layout = Self::plan::<F, CS, C>(circuit, config.clone(), &constants)?;
        Self::assign(cs, circuit, config, &layout, true)
    }

    fn synthesize_batch<F: Field, CS: Assignment<F> + Send, C: Circuit<F> + Sync>(
        assignments: &mut [CS],
        circuits: &[C],
        config: C::Config,
        constants: &[Column<Fixed>],
        floor_plan: Option<&FloorPlan>,
    ) -> Result<Option<FloorPlan>, Error>
    where
        C::Config: Send,
    {
        debug_assert_eq!(assignments.len(), circuits.len());
        let Some(first_circuit) = circuits.first() else {
            return Ok(None);
        };

        let (layout, is_new) =
            Self::cached_or_plan::<F, CS, C>(floor_plan, first_circuit, config.clone(), constants)?;
        let new_plan = is_new.then(|| FloorPlan::from_arc(layout.clone()));
        // A recognized plan was retained while its proving key's fixed columns
        // were assigned, so only a newly-created plan needs table assignments.
        let assign_tables = is_new;
        if circuits.len() == 1 {
            Self::assign(
                &mut assignments[0],
                first_circuit,
                config,
                &layout,
                assign_tables,
            )?;
            return Ok(new_plan);
        }

        // Workers share the immutable layout; each one owns its assignment
        // target and a clone of the configuration.
        let configs = (0..circuits.len())
            .map(|_| config.clone())
            .collect::<Vec<_>>();
        assignments
            .into_par_iter()
            .zip(circuits.into_par_iter())
            .zip(configs.into_par_iter())
            .try_for_each(|((assignment, circuit), config)| {
                Self::assign(assignment, circuit, config, &layout, assign_tables)
            })?;

        Ok(new_plan)
    }
}

impl FloorPlanner for V1Named {
    fn synthesize<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<(), Error> {
        let layout = V1::plan::<F, CS, C>(circuit, config.clone(), &constants)?;
        V1::assign_named(cs, circuit, config, &layout, true)
    }

    fn synthesize_batch<F: Field, CS: Assignment<F> + Send, C: Circuit<F> + Sync>(
        assignments: &mut [CS],
        circuits: &[C],
        config: C::Config,
        constants: &[Column<Fixed>],
        floor_plan: Option<&FloorPlan>,
    ) -> Result<Option<FloorPlan>, Error>
    where
        C::Config: Send,
    {
        debug_assert_eq!(assignments.len(), circuits.len());
        let Some(first_circuit) = circuits.first() else {
            return Ok(None);
        };

        let (layout, is_new) =
            V1::cached_or_plan::<F, CS, C>(floor_plan, first_circuit, config.clone(), constants)?;
        let new_plan = is_new.then(|| FloorPlan::from_arc(layout.clone()));
        let assign_tables = is_new;
        if circuits.len() == 1 {
            V1::assign_named(
                &mut assignments[0],
                first_circuit,
                config,
                &layout,
                assign_tables,
            )?;
            return Ok(new_plan);
        }

        let configs = (0..circuits.len())
            .map(|_| config.clone())
            .collect::<Vec<_>>();
        assignments
            .into_par_iter()
            .zip(circuits.into_par_iter())
            .zip(configs.into_par_iter())
            .try_for_each(|((assignment, circuit), config)| {
                V1::assign_named(assignment, circuit, config, &layout, assign_tables)
            })?;

        Ok(new_plan)
    }
}

impl V1 {
    fn cached_or_plan<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        floor_plan: Option<&FloorPlan>,
        circuit: &C,
        config: C::Config,
        constants: &[Column<Fixed>],
    ) -> Result<(Arc<V1Layout>, bool), Error> {
        if let Some(layout) = floor_plan.and_then(|plan| plan.downcast::<V1Layout>()) {
            return Ok((layout, false));
        }

        Self::plan::<F, CS, C>(circuit, config, constants)
            .map(Arc::new)
            .map(|layout| (layout, true))
    }

    fn plan<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        circuit: &C,
        config: C::Config,
        constants: &[Column<Fixed>],
    ) -> Result<V1Layout, Error> {
        // First pass: measure the regions within the circuit.
        let mut measure = MeasurementPass::new();
        {
            let pass = &mut measure;
            circuit
                .without_witnesses()
                .synthesize(config.clone(), V1Pass::<_, CS>::measure(pass))?;
        }

        // Planning:
        // - Position the regions.
        let (regions, column_allocations) = strategy::slot_in_biggest_advice_first(measure.regions);
        // - Determine how many rows our planned circuit will require.
        let first_unassigned_row = column_allocations
            .values()
            .map(|a| a.unbounded_interval_start())
            .max()
            .unwrap_or(0);

        // - Position the constants within those rows.
        let fixed_allocations = constants
            .iter()
            .map(|&column| {
                let allocation = column_allocations
                    .get(&Column::<Any>::from(column).into())
                    .cloned()
                    .unwrap_or_default();
                (column, allocation)
            })
            .collect();

        let region_lookup = RegionLookup::new(measure.region_ids);

        Ok(V1Layout {
            regions,
            region_lookup,
            fixed_allocations,
            first_unassigned_row,
        })
    }

    fn assign<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        layout: &V1Layout,
        assign_tables: bool,
    ) -> Result<(), Error> {
        let mut plan = V1Plan::new(cs, layout.regions.clone())?;

        // Second pass:
        // - Assign the regions.
        let mut assign = AssignmentPass::new(&mut plan, assign_tables);
        {
            let pass = &mut assign;
            circuit.synthesize(config, V1Pass::assign(pass))?;
        }

        Self::finish_assignment(plan, layout)
    }

    fn assign_named<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        layout: &V1Layout,
        assign_tables: bool,
    ) -> Result<(), Error> {
        let mut plan = V1Plan::new(cs, layout.regions.clone())?;

        let assigned = AtomicUsize::new(0);
        let mut assign =
            NamedAssignmentPass::new(&mut plan, &layout.region_lookup, &assigned, assign_tables);
        {
            let pass = &mut assign;
            circuit.synthesize(config, V1Pass::assign_named(pass))?;
        }
        if assigned.load(Ordering::Relaxed) != layout.region_lookup.len() {
            return Err(Error::Synthesis);
        }

        Self::finish_assignment(plan, layout)
    }

    fn finish_assignment<F: Field, CS: Assignment<F>>(
        plan: V1Plan<'_, F, CS>,
        layout: &V1Layout,
    ) -> Result<(), Error> {
        let constant_positions = || {
            layout
                .fixed_allocations
                .iter()
                .flat_map(|(column, allocation)| {
                    let column = *column;
                    allocation
                        .free_intervals(0, Some(layout.first_unassigned_row))
                        .flat_map(move |empty| empty.range().unwrap().map(move |row| (column, row)))
                })
        };
        if constant_positions().count() < plan.constants.len() {
            return Err(Error::NotEnoughColumnsForConstants);
        }
        for ((fixed_column, fixed_row), (value, advice)) in constant_positions().zip(plan.constants)
        {
            plan.cs.assign_fixed(
                || format!("Constant({:?})", value.evaluate()),
                fixed_column,
                fixed_row,
                || Value::known(value),
            )?;
            plan.cs.copy(
                fixed_column.into(),
                fixed_row,
                advice.column,
                *plan.regions[*advice.region_index] + advice.row_offset,
            )?;
        }

        Ok(())
    }
}

#[derive(Debug)]
enum Pass<'p, 'a, F: Field, CS: Assignment<F> + 'a> {
    Measurement(&'p mut MeasurementPass),
    Assignment(&'p mut AssignmentPass<'p, 'a, F, CS>),
    NamedAssignment(&'p mut NamedAssignmentPass<'p, 'a, F, CS>),
}

/// A single pass of the [`V1`] layouter.
#[derive(Debug)]
pub struct V1Pass<'p, 'a, F: Field, CS: Assignment<F> + 'a>(Pass<'p, 'a, F, CS>);

impl<'p, 'a, F: Field, CS: Assignment<F> + 'a> V1Pass<'p, 'a, F, CS> {
    fn measure(pass: &'p mut MeasurementPass) -> Self {
        V1Pass(Pass::Measurement(pass))
    }

    fn assign(pass: &'p mut AssignmentPass<'p, 'a, F, CS>) -> Self {
        V1Pass(Pass::Assignment(pass))
    }

    fn assign_named(pass: &'p mut NamedAssignmentPass<'p, 'a, F, CS>) -> Self {
        V1Pass(Pass::NamedAssignment(pass))
    }
}

impl<'p, 'a, F: Field, CS: Assignment<F> + 'a> Layouter<F> for V1Pass<'p, 'a, F, CS> {
    type Root = Self;

    fn assign_region<A, AR, N, NR>(&mut self, name: N, assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        match &mut self.0 {
            Pass::Measurement(pass) => pass.assign_region(name, assignment),
            Pass::Assignment(pass) => pass.assign_region(name, assignment),
            Pass::NamedAssignment(pass) => pass.assign_region(name, assignment),
        }
    }

    fn assign_table<A, N, NR>(&mut self, name: N, assignment: A) -> Result<(), Error>
    where
        A: FnMut(Table<'_, F>) -> Result<(), Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        match &mut self.0 {
            Pass::Measurement(_) => Ok(()),
            Pass::Assignment(pass) if !pass.assign_tables => Ok(()),
            Pass::Assignment(pass) => pass.assign_table(name, assignment),
            Pass::NamedAssignment(pass) if !pass.assign_tables => Ok(()),
            Pass::NamedAssignment(pass) => pass.assign_table(name, assignment),
        }
    }

    fn constrain_instance(
        &mut self,
        cell: Cell,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<(), Error> {
        match &mut self.0 {
            Pass::Measurement(_) => Ok(()),
            Pass::Assignment(pass) => pass.constrain_instance(cell, instance, row),
            Pass::NamedAssignment(pass) => pass.constrain_instance(cell, instance, row),
        }
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        match &mut self.0 {
            Pass::Measurement(pass) => pass.names.push_namespace(name_fn().into()),
            Pass::Assignment(pass) => pass.plan.cs.push_namespace(name_fn),
            Pass::NamedAssignment(pass) => {
                let name = name_fn().into();
                pass.push_namespace(name);
            }
        }
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        match &mut self.0 {
            Pass::Measurement(pass) => pass.names.pop_namespace(),
            Pass::Assignment(pass) => pass.plan.cs.pop_namespace(gadget_name),
            Pass::NamedAssignment(pass) => pass.pop_namespace(gadget_name),
        }
    }
}

/// Measures the circuit.
#[derive(Debug)]
pub struct MeasurementPass {
    regions: Vec<RegionShape>,
    region_ids: Vec<RegionId>,
    names: RegionNameTracker,
}

impl MeasurementPass {
    fn new() -> Self {
        MeasurementPass {
            regions: vec![],
            region_ids: vec![],
            names: RegionNameTracker::default(),
        }
    }

    fn assign_region<F: Field, A, AR, N, NR>(
        &mut self,
        name: N,
        mut assignment: A,
    ) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let region_index = self.regions.len();

        // Get shape of the region.
        let mut shape = RegionShape::new(region_index.into());
        let result = {
            let region: &mut dyn RegionLayouter<F> = &mut shape;
            assignment(region.into())
        }?;
        self.regions.push(shape);
        self.region_ids.push(self.names.next(name().into()));

        Ok(result)
    }
}

/// Assigns the circuit.
#[derive(Debug)]
pub struct AssignmentPass<'p, 'a, F: Field, CS: Assignment<F> + 'a> {
    plan: &'p mut V1Plan<'a, F, CS>,
    /// Counter tracking which region we need to assign next.
    region_index: usize,
    /// Whether to assign fixed lookup tables during this pass.
    assign_tables: bool,
}

impl<'p, 'a, F: Field, CS: Assignment<F> + 'a> AssignmentPass<'p, 'a, F, CS> {
    fn new(plan: &'p mut V1Plan<'a, F, CS>, assign_tables: bool) -> Self {
        AssignmentPass {
            plan,
            region_index: 0,
            assign_tables,
        }
    }

    fn assign_region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        // Get the next region we are assigning.
        let region_index = self.region_index;
        self.region_index += 1;

        self.plan.cs.enter_region(name);
        let mut region = V1Region::new(self.plan, region_index.into());
        let result = {
            let region: &mut dyn RegionLayouter<F> = &mut region;
            assignment(region.into())
        }?;
        self.plan.cs.exit_region();

        Ok(result)
    }

    fn assign_table<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Table<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        // Maintenance hazard: there is near-duplicate code in `SingleChipLayouter::assign_table`.

        // Assign table cells.
        self.plan.cs.enter_region(name);
        let mut table = SimpleTableLayouter::new(self.plan.cs, &self.plan.table_columns);
        let result = {
            let table: &mut dyn TableLayouter<F> = &mut table;
            assignment(table.into())
        }?;
        let default_and_assigned = table.default_and_assigned;
        self.plan.cs.exit_region();

        // Check that all table columns have the same length `first_unused`,
        // and all cells up to that length are assigned.
        let first_unused = compute_table_lengths(&default_and_assigned)?;

        // Record these columns so that we can prevent them from being used again.
        for column in default_and_assigned.keys() {
            self.plan.table_columns.push(*column);
        }

        for (col, (default_val, _)) in default_and_assigned {
            // default_val must be Some because we must have assigned
            // at least one cell in each column, and in that case we checked
            // that all cells up to first_unused were assigned.
            self.plan
                .cs
                .fill_from_row(col.inner(), first_unused, default_val.unwrap())?;
        }

        Ok(result)
    }

    fn constrain_instance(
        &mut self,
        cell: Cell,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<(), Error> {
        self.plan.cs.copy(
            cell.column,
            *self.plan.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        )
    }
}

/// Assigns regions by their measured annotation rather than call order.
#[derive(Debug)]
struct NamedAssignmentPass<'p, 'a, F: Field, CS: Assignment<F> + 'a> {
    plan: &'p mut V1Plan<'a, F, CS>,
    region_lookup: &'p RegionLookup,
    namespace_stack: Vec<Option<usize>>,
    occurrences: Vec<HashMap<&'p str, usize>>,
    assigned: &'p AtomicUsize,
    assign_tables: bool,
}

impl<'p, 'a, F: Field, CS: Assignment<F> + 'a> NamedAssignmentPass<'p, 'a, F, CS> {
    fn new(
        plan: &'p mut V1Plan<'a, F, CS>,
        region_lookup: &'p RegionLookup,
        assigned: &'p AtomicUsize,
        assign_tables: bool,
    ) -> Self {
        let occurrences = (0..region_lookup.region_indices.len())
            .map(|_| HashMap::new())
            .collect();
        Self {
            plan,
            region_lookup,
            namespace_stack: vec![Some(0)],
            occurrences,
            assigned,
            assign_tables,
        }
    }

    fn push_namespace(&mut self, name: String) {
        let namespace = self
            .namespace_stack
            .last()
            .copied()
            .flatten()
            .and_then(|namespace| {
                self.region_lookup.namespace_children[namespace]
                    .get(name.as_str())
                    .copied()
            });
        self.namespace_stack.push(namespace);
        self.plan.cs.push_namespace(|| name);
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        self.namespace_stack.pop();
        self.plan.cs.pop_namespace(gadget_name);
    }

    fn assign_region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Region<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let name = name().into();
        let namespace = self
            .namespace_stack
            .last()
            .copied()
            .flatten()
            .ok_or(Error::Synthesis)?;
        let (planned_name, region_indices) = self.region_lookup.region_indices[namespace]
            .get_key_value(name.as_str())
            .ok_or(Error::Synthesis)?;
        let occurrence = self.occurrences[namespace]
            .entry(planned_name.as_str())
            .or_default();
        let region_index = *region_indices.get(*occurrence).ok_or(Error::Synthesis)?;
        *occurrence += 1;
        self.assigned.fetch_add(1, Ordering::Relaxed);

        self.plan.cs.enter_region(|| name);
        let mut region = V1Region::new(self.plan, region_index);
        let result = {
            let region: &mut dyn RegionLayouter<F> = &mut region;
            assignment(region.into())
        }?;
        self.plan.cs.exit_region();

        Ok(result)
    }

    fn assign_table<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
    where
        A: FnMut(Table<'_, F>) -> Result<AR, Error>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        self.plan.cs.enter_region(name);
        let mut table = SimpleTableLayouter::new(self.plan.cs, &self.plan.table_columns);
        let result = {
            let table: &mut dyn TableLayouter<F> = &mut table;
            assignment(table.into())
        }?;
        let default_and_assigned = table.default_and_assigned;
        self.plan.cs.exit_region();

        let first_unused = compute_table_lengths(&default_and_assigned)?;
        for column in default_and_assigned.keys() {
            self.plan.table_columns.push(*column);
        }
        for (col, (default_val, _)) in default_and_assigned {
            self.plan
                .cs
                .fill_from_row(col.inner(), first_unused, default_val.unwrap())?;
        }

        Ok(result)
    }

    fn constrain_instance(
        &mut self,
        cell: Cell,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<(), Error> {
        self.plan.cs.copy(
            cell.column,
            *self.plan.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        )
    }
}

struct V1Region<'r, 'a, F: Field, CS: Assignment<F> + 'a> {
    plan: &'r mut V1Plan<'a, F, CS>,
    region_index: RegionIndex,
}

impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for V1Region<'r, 'a, F, CS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("V1Region")
            .field("plan", &self.plan)
            .field("region_index", &self.region_index)
            .finish()
    }
}

impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> V1Region<'r, 'a, F, CS> {
    fn new(plan: &'r mut V1Plan<'a, F, CS>, region_index: RegionIndex) -> Self {
        V1Region { plan, region_index }
    }
}

impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> RegionLayouter<F> for V1Region<'r, 'a, F, CS> {
    fn enable_selector<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        selector: &Selector,
        offset: usize,
    ) -> Result<(), Error> {
        self.plan.cs.enable_selector(
            annotation,
            selector,
            *self.plan.regions[*self.region_index] + offset,
        )
    }

    fn assign_advice<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.plan.cs.assign_advice(
            annotation,
            column,
            *self.plan.regions[*self.region_index] + offset,
            to,
        )?;

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn assign_advice_batch<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn(usize) -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        len: usize,
        to: &'v mut (dyn FnMut(usize) -> Value<Assigned<F>> + 'v),
    ) -> Result<(), Error> {
        if len == 0 {
            return Ok(());
        }

        let offset = self.plan.regions[*self.region_index]
            .checked_add(offset)
            .ok_or(Error::BoundsFailure)?;
        self.plan
            .cs
            .assign_advice_batch(annotation, column, offset, len, to)
    }

    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: Assigned<F>,
    ) -> Result<Cell, Error> {
        let advice =
            self.assign_advice(annotation, column, offset, &mut || Value::known(constant))?;
        self.constrain_constant(advice, constant)?;

        Ok(advice)
    }

    fn assign_advice_from_instance<'v>(
        &mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        instance: Column<Instance>,
        row: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Value<F>), Error> {
        let value = self.plan.cs.query_instance(instance, row)?;

        let cell = self.assign_advice(annotation, advice, offset, &mut || value.to_field())?;

        self.plan.cs.copy(
            cell.column,
            *self.plan.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        )?;

        Ok((cell, value))
    }

    fn instance_value(
        &mut self,
        instance: Column<Instance>,
        row: usize,
    ) -> Result<Value<F>, Error> {
        self.plan.cs.query_instance(instance, row)
    }

    fn assign_fixed<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.plan.cs.assign_fixed(
            annotation,
            column,
            *self.plan.regions[*self.region_index] + offset,
            to,
        )?;

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn constrain_constant(&mut self, cell: Cell, constant: Assigned<F>) -> Result<(), Error> {
        self.plan.constants.push((constant, cell));
        Ok(())
    }

    fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), Error> {
        self.plan.cs.copy(
            left.column,
            *self.plan.regions[*left.region_index] + left.row_offset,
            right.column,
            *self.plan.regions[*right.region_index] + right.row_offset,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use pasta_curves::vesta;

    use crate::{
        circuit::{Layouter, Value},
        dev::MockProver,
        plonk::{Advice, Circuit, Column, Error},
    };

    #[derive(Clone)]
    struct NamedCircuit {
        reverse: bool,
        rename: bool,
    }

    impl Circuit<vesta::Scalar> for NamedCircuit {
        type Config = Column<Advice>;
        type FloorPlanner = super::V1Named;

        fn without_witnesses(&self) -> Self {
            Self {
                reverse: false,
                rename: false,
            }
        }

        fn configure(meta: &mut crate::plonk::ConstraintSystem<vesta::Scalar>) -> Self::Config {
            meta.advice_column()
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<vesta::Scalar>,
        ) -> Result<(), Error> {
            let namespaces = if self.reverse {
                ["second namespace", "first namespace"]
            } else if self.rename {
                ["renamed namespace", "second namespace"]
            } else {
                ["first namespace", "second namespace"]
            };

            for (offset, namespace) in namespaces.into_iter().enumerate() {
                layouter.namespace(|| namespace).assign_region(
                    || "value region",
                    |mut region| {
                        region.assign_advice(
                            || "value",
                            config,
                            offset,
                            || Value::known(vesta::Scalar::from(offset as u64)),
                        )
                    },
                )?;
            }

            Ok(())
        }
    }

    #[test]
    fn named_assignment_supports_reordered_regions() {
        let circuit = NamedCircuit {
            reverse: true,
            rename: false,
        };
        MockProver::run(4, &circuit, vec![]).unwrap();
    }

    #[test]
    fn named_assignment_rejects_changed_region_names() {
        let circuit = NamedCircuit {
            reverse: false,
            rename: true,
        };
        assert!(matches!(
            MockProver::run(4, &circuit, vec![]).unwrap_err(),
            Error::Synthesis,
        ));
    }

    #[test]
    fn not_enough_columns_for_constants() {
        struct MyCircuit {}

        impl Circuit<vesta::Scalar> for MyCircuit {
            type Config = Column<Advice>;
            type FloorPlanner = super::V1;

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut crate::plonk::ConstraintSystem<vesta::Scalar>) -> Self::Config {
                meta.advice_column()
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl crate::circuit::Layouter<vesta::Scalar>,
            ) -> Result<(), crate::plonk::Error> {
                layouter.assign_region(
                    || "assign constant",
                    |mut region| {
                        region.assign_advice_from_constant(
                            || "one",
                            config,
                            0,
                            vesta::Scalar::one(),
                        )
                    },
                )?;

                Ok(())
            }
        }

        let circuit = MyCircuit {};
        assert!(matches!(
            MockProver::run(3, &circuit, vec![]).unwrap_err(),
            Error::NotEnoughColumnsForConstants,
        ));
    }
}
