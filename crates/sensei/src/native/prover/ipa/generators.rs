//! Periodic materialization of the virtual IPA generator vector.

use crate::{
    Error,
    native::{
        buffer::{Buffer, BufferPool},
        commitment::CompactGenerators,
        worker::Execution,
    },
};
use alloc::vec::Vec;
use udon::{
    curve::{PreparedAffinePoint, Vesta, VestaAffine, VestaPoint, VestaProjective},
    exec::{ExecutionOptions, TaskBudget},
    field::{Fp, Fq},
    msm::{Bases, PreparedScalars, ScalarStorage, Scratch, SharedScalarInput},
};

#[cfg(test)]
mod tests;

/// Folded generators may cancel, unlike the fixed nonidentity SRS entries.
pub(super) enum Generators {
    Prepared(Buffer<PreparedAffinePoint<Vesta>>),
    Points(Buffer<VestaPoint>),
    Compact(CompactGenerators),
}
impl Generators {
    pub(super) fn bases(&self) -> Bases<'_, Vesta> {
        match self {
            Self::Prepared(points) => Bases::Prepared(points),
            Self::Points(points) => Bases::Points(points),
            Self::Compact(points) => points.bases(),
        }
    }
}

#[derive(Default)]
pub(super) struct Workspace {
    records: Vec<ScalarStorage<Vesta>>,
    projective: Vec<VestaProjective>,
    normalization: Vec<Fq>,
    workers: Vec<Worker>,
    points: BufferPool<VestaPoint>,
    prepared: BufferPool<PreparedAffinePoint<Vesta>>,
}
#[derive(Default)]
struct Worker {
    scalars: Vec<ScalarStorage<Vesta>>,
    digits: Vec<u8>,
    affine: Vec<VestaAffine>,
    projective: Vec<VestaProjective>,
    field: Vec<Fq>,
    indices: Vec<usize>,
}
fn grow<T: Clone>(values: &mut Vec<T>, len: usize, value: T) {
    values.resize(values.len().max(len), value);
}

/// Materializes `G'[i] = sum_j weights[j] * G[i + j * outputs]`.
///
/// Scratch grows before dispatch. Each admitted row group runs serially on its
/// worker, while output leases keep the previous generator bank alive.
pub(super) fn materialize(
    workspace: &mut Workspace,
    bases: Bases<'_, Vesta>,
    weights: &[Fp],
    execution: Execution<'_>,
) -> Result<Generators, Error> {
    if weights.is_empty() || bases.is_empty() || !bases.len().is_multiple_of(weights.len()) {
        return Err(Error::InternalInvariant);
    }
    let count = bases.len() / weights.len();
    grow(&mut workspace.records, weights.len(), ScalarStorage::ZERO);
    let prepared = PreparedScalars::prepare(
        weights,
        &mut workspace.records[..weights.len()],
        execution.budget,
        &execution,
    );
    let chunk_len = count.div_ceil(execution.budget.get());
    let chunks = count.div_ceil(chunk_len);
    grow(&mut workspace.projective, count, VestaProjective::IDENTITY);
    grow(&mut workspace.normalization, count, Fq::ZERO);
    workspace
        .workers
        .resize_with(workspace.workers.len().max(chunks), Worker::default);
    let input = |chunk, len| {
        let start = chunk * chunk_len;
        let bases = bases.range(start..bases.len());
        // Divisibility above and chunk bounds give one in-bank base per weight.
        SharedScalarInput::new(bases, prepared, len, 1, count).map_err(|_| Error::InternalInvariant)
    };
    let options = ExecutionOptions::default().with_task_budget(TaskBudget::SERIAL);
    for (chunk, worker) in workspace.workers[..chunks].iter_mut().enumerate() {
        let len = chunk_len.min(count - chunk * chunk_len);
        // The phase bank is bounded by N; its scratch sizes must be representable.
        let requirements = input(chunk, len)?
            .requirements(options)
            .map_err(|_| Error::InternalInvariant)?;
        grow(
            &mut worker.scalars,
            requirements.scalars(),
            ScalarStorage::ZERO,
        );
        grow(&mut worker.digits, requirements.digits(), 0);
        grow(
            &mut worker.affine,
            requirements.affine(),
            VestaAffine::GENERATOR,
        );
        grow(
            &mut worker.projective,
            requirements.projective(),
            VestaProjective::IDENTITY,
        );
        grow(&mut worker.field, requirements.field(), Fq::ZERO);
        grow(&mut worker.indices, requirements.indices(), 0);
    }
    let rows = execution.map(
        workspace.projective[..count]
            .chunks_mut(chunk_len)
            .enumerate()
            .zip(&mut workspace.workers[..chunks]),
        |((chunk, output), worker), execution| {
            let scratch = Scratch::new(
                &mut worker.scalars,
                &mut worker.digits,
                &mut worker.affine,
                &mut worker.projective,
                &mut worker.field,
                &mut worker.indices,
            );
            // The same input/options sized these scratch buffers before dispatch.
            input(chunk, output.len())?
                .execute(output, options, &execution.serial(), scratch)
                .map_err(|_| Error::InternalInvariant)
        },
    );
    for row in rows {
        row?;
    }
    let mut points = workspace.points.take(count, VestaPoint::IDENTITY, false);
    udon::curve::batch_normalize(
        &workspace.projective[..count],
        &mut points,
        &mut workspace.normalization[..count],
    );
    if points.iter().any(VestaPoint::is_identity) {
        return Ok(Generators::Points(points));
    }
    let mut output = workspace.prepared.take(
        count,
        PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR),
        false,
    );
    for (output, point) in output.iter_mut().zip(&points) {
        *output = PreparedAffinePoint::from_affine(point.as_affine().expect("nonidentity output"));
    }
    if crate::tuning::IPA_COMPACT_FOLDED && count <= 32 {
        Ok(Generators::Compact(CompactGenerators::new(&output)))
    } else {
        Ok(Generators::Prepared(output))
    }
}

#[cfg(test)]
impl Workspace {
    pub(super) fn capacities(&self) -> Vec<usize> {
        let mut result = alloc::vec![
            self.records.capacity(),
            self.projective.capacity(),
            self.normalization.capacity(),
            self.workers.capacity()
        ];
        for worker in &self.workers {
            result.extend([
                worker.scalars.capacity(),
                worker.digits.capacity(),
                worker.affine.capacity(),
                worker.projective.capacity(),
                worker.field.capacity(),
                worker.indices.capacity(),
            ]);
        }
        for inventory in [self.points.inventory(), self.prepared.inventory()] {
            result.extend([inventory.allocations, inventory.buffers, inventory.bytes]);
        }
        result
    }
    #[cfg(feature = "verifier")]
    pub(super) fn retained_bytes(&self) -> usize {
        self.records.capacity() * size_of::<ScalarStorage<Vesta>>()
            + self.projective.capacity() * size_of::<VestaProjective>()
            + self.normalization.capacity() * size_of::<Fq>()
            + self.workers.capacity() * size_of::<Worker>()
            + self.points.inventory().bytes
            + self.prepared.inventory().bytes
            + self
                .workers
                .iter()
                .map(|worker| {
                    worker.scalars.capacity() * size_of::<ScalarStorage<Vesta>>()
                        + worker.digits.capacity()
                        + worker.affine.capacity() * size_of::<VestaAffine>()
                        + worker.projective.capacity() * size_of::<VestaProjective>()
                        + worker.field.capacity() * size_of::<Fq>()
                        + worker.indices.capacity() * size_of::<usize>()
                })
                .sum::<usize>()
    }
    pub(super) fn dirty(&mut self) {
        self.records.fill(ScalarStorage::ZERO);
        self.projective.fill(VestaProjective::GENERATOR);
        self.normalization.fill(Fq::from_u64(17));
        self.points.dirty(VestaPoint::IDENTITY);
        self.prepared
            .dirty(PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR));
        for worker in &mut self.workers {
            worker.scalars.fill(ScalarStorage::ZERO);
            worker.digits.fill(u8::MAX);
            worker.affine.fill(VestaAffine::GENERATOR);
            worker.projective.fill(VestaProjective::GENERATOR);
            worker.field.fill(Fq::from_u64(19));
            worker.indices.fill(usize::MAX);
        }
    }
}
