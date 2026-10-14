use std::fmt::Write;

use ff::Field;

use crate::{
    circuit::Value,
    plonk::{
        Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed,
        FloorPlanner, Instance, Selector,
    },
};

pub mod layout;

/// Builds a dot graph string representing the given circuit.
///
/// The graph is built from calls to [`Layouter::namespace`] both within the circuit, and
/// inside the gadgets and chips that it uses.
///
/// [`Layouter::namespace`]: crate::circuit::Layouter#method.namespace
pub fn circuit_dot_graph<F: Field, ConcreteCircuit: Circuit<F>>(
    circuit: &ConcreteCircuit,
) -> String {
    // Collect the graph details.
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);
    let mut graph = Graph::default();
    ConcreteCircuit::FloorPlanner::synthesize(&mut graph, circuit, config, cs.constants).unwrap();

    graph.render_dot()
}

#[derive(Default)]
struct Graph {
    /// Graph nodes in the namespace, structured as `(name, gadget_name)`.
    nodes: Vec<(String, Option<String>)>,

    /// Directed edges in the graph, as pairs of indices into `nodes`.
    edges: Vec<(usize, usize)>,

    /// The current namespace, as indices into `nodes`.
    current_namespace: Vec<usize>,
}

impl Graph {
    /// Renders the collected namespaces as a directed DOT graph named `circuit`.
    ///
    /// Each namespace becomes a node identified by its index in `nodes`, labelled with
    /// its name (prefixed by `[gadget_name]` when one was recorded), and each
    /// parent-to-child relation becomes an edge, both in collection order.
    fn render_dot(self) -> String {
        let mut dot = String::from("digraph circuit{");
        for (id, (name, gadget_name)) in self.nodes.into_iter().enumerate() {
            let label = if let Some(gadget_name) = gadget_name {
                format!("[{}] {}", gadget_name, name)
            } else {
                name
            };
            write!(dot, "{}[label=\"{}\";];", id, escape_label(&label)).unwrap();
        }
        for (parent, child) in self.edges {
            write!(dot, "{}->{};", parent, child).unwrap();
        }
        dot.push('}');
        dot
    }
}

/// Escapes `label` for use inside a double-quoted DOT label.
///
/// Quotes and backslashes are escaped so they appear literally, and line feeds become
/// Graphviz's `\n` line break. Every other character, including non-ASCII text, is
/// written as-is, since DOT strings are UTF-8.
fn escape_label(label: &str) -> String {
    let mut escaped = String::with_capacity(label.len());
    for c in label.chars() {
        match c {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            c => escaped.push(c),
        }
    }
    escaped
}

impl<F: Field> Assignment<F> for Graph {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing; we don't care about cells in this context.
        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, _: usize) -> Result<Value<F>, Error> {
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing; we don't care about cells in this context.
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing; we don't care about cells in this context.
        Ok(())
    }

    fn copy(
        &mut self,
        _: Column<Any>,
        _: usize,
        _: Column<Any>,
        _: usize,
    ) -> Result<(), crate::plonk::Error> {
        // Do nothing; we don't care about permutations in this context.
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Store the new node.
        let new_node = self.nodes.len();
        self.nodes.push((name_fn().into(), None));

        // Create an edge from the parent, if any.
        if let Some(parent) = self.current_namespace.last() {
            self.edges.push((*parent, new_node));
        }

        // Push the new namespace.
        self.current_namespace.push(new_node);
    }

    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        // Store the gadget name that was extracted, if any.
        let node = self
            .current_namespace
            .last()
            .expect("pop_namespace should never be called on the root");
        self.nodes[*node].1 = gadget_name;

        // Pop the namespace.
        self.current_namespace.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::{Graph, circuit_dot_graph};
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner},
        pasta::Fp,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    fn graph(nodes: &[(&str, Option<&str>)], edges: &[(usize, usize)]) -> Graph {
        Graph {
            nodes: nodes
                .iter()
                .map(|(name, gadget)| (name.to_string(), gadget.map(str::to_string)))
                .collect(),
            edges: edges.to_vec(),
            current_namespace: vec![],
        }
    }

    /// A circuit that only opens nested namespaces.
    #[derive(Default)]
    struct Namespaces;

    impl Circuit<Fp> for Namespaces {
        type Config = ();
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Namespaces
        }

        fn configure(_: &mut ConstraintSystem<Fp>) {}

        fn synthesize(&self, _: (), mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
            let mut outer = layouter.namespace(|| "outer");
            {
                let mut inner = outer.namespace(|| "inner");
                let _leaf = inner.namespace(|| "leaf");
            }
            let _sibling = outer.namespace(|| "sibling");
            drop(_sibling);
            drop(outer);
            let _second_root = layouter.namespace(|| "second root");
            Ok(())
        }
    }

    fn cases() -> Vec<(&'static str, Graph)> {
        vec![
            ("empty", graph(&[], &[])),
            ("single", graph(&[("root", None)], &[])),
            (
                "nested",
                graph(
                    &[
                        ("root", None),
                        ("load", Some("halo2_gadgets::ecc::chip::EccChip<F>::add")),
                        ("inner", None),
                        ("sibling", Some("Chip")),
                        ("second root", None),
                    ],
                    &[(0, 1), (1, 2), (0, 3)],
                ),
            ),
            (
                "escaping",
                graph(
                    &[
                        ("say \"hi\"", None),
                        ("back\\slash", Some("gadget \"q\"")),
                        ("two\nlines", None),
                        ("unicode é λ 🙂 漢字", None),
                        ("punct a;b[c]{d}=e -> f, g", None),
                        ("", None),
                    ],
                    &[(0, 1), (1, 2), (2, 3)],
                ),
            ),
        ]
    }

    #[test]
    fn renders_like_the_previous_renderer() {
        let expected = [
            "digraph circuit{}",
            "digraph circuit{0[label=\"root\";];}",
            "digraph circuit{0[label=\"root\";];\
             1[label=\"[halo2_gadgets::ecc::chip::EccChip<F>::add] load\";];\
             2[label=\"inner\";];3[label=\"[Chip] sibling\";];4[label=\"second root\";];\
             0->1;1->2;0->3;}",
            "digraph circuit{0[label=\"say \\\"hi\\\"\";];\
             1[label=\"[gadget \\\"q\\\"] back\\\\slash\";];2[label=\"two\\nlines\";];\
             3[label=\"unicode é λ 🙂 漢字\";];4[label=\"punct a;b[c]{d}=e -> f, g\";];\
             5[label=\"\";];0->1;1->2;2->3;}",
        ];
        for ((name, graph), expected) in cases().into_iter().zip(expected) {
            assert_eq!(graph.render_dot(), expected, "{name}");
        }
    }

    #[test]
    fn escapes_quotes_backslashes_and_newlines() {
        // In a quoted DOT string, `\"` is a literal quote, `\\` a literal backslash and
        // `\n` a line break; nothing else needs escaping.
        let dot = graph(&[(r#"a "b" \c" \"#, Some("x\ny"))], &[]).render_dot();
        assert_eq!(
            dot,
            r#"digraph circuit{0[label="[x\ny] a \"b\" \\c\" \\";];}"#
        );
    }

    #[test]
    fn keeps_other_characters_verbatim() {
        // The previous renderer used Rust debug escaping, which wrote tabs and combining
        // marks as `\t` and `\u{301}`; DOT does not interpret those escapes.
        let dot = graph(&[("tab\there", None), ("e\u{301} \u{7f}", None)], &[]).render_dot();
        assert_eq!(
            dot,
            "digraph circuit{0[label=\"tab\there\";];1[label=\"e\u{301} \u{7f}\";];}"
        );
    }

    #[test]
    fn renders_nested_circuit_namespaces() {
        let dot = circuit_dot_graph::<Fp, _>(&Namespaces);
        // Gadget traces add the caller's symbol name to each label.
        #[cfg(not(feature = "gadget-traces"))]
        assert_eq!(
            dot,
            "digraph circuit{0[label=\"outer\";];1[label=\"inner\";];2[label=\"leaf\";];\
             3[label=\"sibling\";];4[label=\"second root\";];0->1;1->2;0->3;}"
        );
        assert!(dot.starts_with("digraph circuit{0[label=\""));
        assert!(dot.ends_with("second root\";];0->1;1->2;0->3;}"));
    }
}
