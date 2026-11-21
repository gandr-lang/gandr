//! Terms by name, their text, and the classes of an e-graph as sets of texts,
//! so that two e-graphs whose tables number their terms apart compare.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;

use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_e_graphs::Analysis;
use gandr_theory_e_graphs::EGraph;

/// The names of the operations of a signature, by their places.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Names(pub &'static [&'static str]);

/// The operation `operation` applied to `children` in `table`.
///
/// # Specification
/// trivial.
pub fn op(
    table: &mut TermTable,
    operation: Operation,
    children: &[TermPlace],
) -> TermPlace
{
    table
        .op(operation, children.to_vec())
        .expect("each child is in the table")
}

/// The variable `variable` in `table`.
///
/// # Specification
/// trivial.
pub fn var(
    table: &mut TermTable,
    variable: Variable,
) -> TermPlace
{
    table.var(variable)
}

/// One unit of the walk that writes a term.
enum Write
{
    /// Write the term at the place.
    Term(TermPlace),
    /// Write the text.
    Text(&'static str),
}

/// The text of the term at `place`, each operation by its name in `names`
/// and each variable as `x` and its place.
///
/// # Specification
/// trivial.
pub fn text(
    table: &TermTable,
    names: Names,
    place: TermPlace,
) -> String
{
    let mut out = String::new();
    let mut pending = vec![Write::Term(place)];
    while let Some(next) = pending.pop() {
        match next {
            Write::Text(text) => out.push_str(text),
            Write::Term(place) => {
                let node = table.node(place).expect("a place of the table");
                match node.head {
                    TermHead::Var(variable) => {
                        out.push('x');
                        write!(out, "{}", usize::from(variable)).expect("a string takes the text");
                    },
                    TermHead::Op(operation) => {
                        out.push_str(names.0.get(usize::from(operation)).copied().unwrap_or("?"));
                        if !node.children.is_empty() {
                            out.push('(');
                            pending.push(Write::Text(")"));
                            for (index, &child) in node.children.iter().enumerate().rev() {
                                pending.push(Write::Term(child));
                                if index > 0 {
                                    pending.push(Write::Text(","));
                                }
                            }
                        }
                    },
                }
            },
        }
    }
    out
}

/// The classes of `graph`, each as the set of its members' texts.
///
/// # Specification
/// trivial.
pub fn classes<A>(
    graph: &EGraph<A>,
    names: Names,
) -> BTreeSet<BTreeSet<String>>
where
    A: Analysis,
{
    graph
        .classes()
        .map(|class| {
            graph
                .members(class)
                .expect("a class's root is held")
                .map(|member| text(graph.table(), names, member))
                .collect()
        })
        .collect()
}

/// The places of the members of the class of `place`, in order.
///
/// # Specification
/// trivial.
pub fn members<A>(
    graph: &EGraph<A>,
    place: TermPlace,
) -> Vec<TermPlace>
where
    A: Analysis,
{
    let mut found: Vec<TermPlace> = graph.members(place).expect("the term is held").collect();
    found.sort_unstable();
    found
}
