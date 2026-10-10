//! Measures proof-producing entailment on linear syntax with growing support.

use core::fmt;
use core::hint::black_box;
use core::time::Duration;
use std::io;
use std::io::Write as _;
use std::time::Instant;

use gandr_theory_shapes::affine::Endpoint;
use gandr_theory_shapes::boundary::DimensionCount;
use gandr_theory_shapes::boundary::NodeId;
use gandr_theory_shapes::boundary::ShapeError;
use gandr_theory_shapes::boundary::Variable;
use gandr_theory_shapes::formula::Formula;
use gandr_theory_shapes::formula::Node;
use gandr_theory_shapes::formula::Problem;
use gandr_theory_shapes::formula::Shape;
use gandr_theory_shapes::oracle::Evidence;
use gandr_theory_shapes::oracle::decide;

/// A benchmark family, rather than a user-supplied expression parser.
#[derive(Clone, Copy, Debug)]
enum Family
{
    /// Endpoint coverage entails the even-or-odd parity partition.
    BoundaryParity,
    /// One atomic endpoint face entails itself in a large unused context.
    AtomicAmbient,
}

impl fmt::Display for Family
{
    /// Writes the table label.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::BoundaryParity => "boundary parity",
            | Self::AtomicAmbient => "atomic ambient",
        })
    }
}

/// A failed measurement, including oracle errors and an unexpected refutation.
#[derive(Debug)]
enum RunError
{
    /// An invalid input or evidence from the shape calculus.
    Shape(ShapeError),
    /// Output could not be written.
    Output(io::Error),
    /// A valid query was refuted or the sample inventory was empty.
    Invariant,
}

impl fmt::Display for RunError
{
    /// Renders the underlying failure without erasing its category.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Shape(ref error) => error.fmt(f),
            | Self::Output(ref error) => error.fmt(f),
            | Self::Invariant => f.write_str("measurement invariant failed"),
        }
    }
}
impl core::error::Error for RunError
{
}

impl From<ShapeError> for RunError
{
    /// Preserves a shape failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: ShapeError) -> Self
    {
        Self::Shape(error)
    }
}
impl From<io::Error> for RunError
{
    /// Preserves an output failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: io::Error) -> Self
    {
        Self::Output(error)
    }
}

/// Constructs a valid query with a declared syntax and context size.
///
/// # Specification
/// - requires: positive dimension count.
/// - provides: `boundary parity` has endpoint coverage implying even-or-odd
///   parity; `atomic ambient` mentions only the last dimension.
/// - fails: malformed generated syntax is reported as a shape failure.
/// - panics: none.
///
/// # Errors
/// Returns [`ShapeError`] for malformed generated syntax.
///
/// # Adequacy
/// - hypothesis: L1 every timed query must produce independently validated
///   positive evidence; the command observes this for both families at each
///   printed size.
/// - witness: `tests::measurements_replay`
fn query(
    family: Family,
    dimensions: DimensionCount,
) -> Result<Problem, ShapeError>
{
    let dimensions = usize::from(dimensions);
    let mut nodes = Vec::new();
    match family {
        | Family::AtomicAmbient => nodes.push(Node::Endpoint(
            Variable::from(dimensions.saturating_sub(1)),
            Endpoint::Zero,
        )),
        | Family::BoundaryParity => {
            let mut root = NodeId::from(0);
            for index in 0 .. dimensions {
                let zero = NodeId::from(nodes.len());
                nodes.push(Node::Endpoint(Variable::from(index), Endpoint::Zero));
                let one = NodeId::from(nodes.len());
                nodes.push(Node::Endpoint(Variable::from(index), Endpoint::One));
                let boundary = NodeId::from(nodes.len());
                nodes.push(Node::Or(zero, one));
                if index == 0 {
                    root = boundary;
                }
                else {
                    let next = NodeId::from(nodes.len());
                    nodes.push(Node::And(root, boundary));
                    root = next;
                }
            }
        },
    }
    let formula = Formula::new(nodes)?;
    let conclusion = match family {
        | Family::AtomicAmbient => formula.clone(),
        | Family::BoundaryParity => {
            let mut parity = vec![Node::Top, Node::Bottom];
            let mut even = NodeId::from(0);
            let mut odd = NodeId::from(1);
            let mut append = |node| {
                let id = NodeId::from(parity.len());
                parity.push(node);
                id
            };
            for index in 0 .. dimensions {
                let zero = append(Node::Endpoint(Variable::from(index), Endpoint::Zero));
                let one = append(Node::Endpoint(Variable::from(index), Endpoint::One));
                let even_zero = append(Node::And(even, zero));
                let odd_one = append(Node::And(odd, one));
                let even_one = append(Node::And(even, one));
                let odd_zero = append(Node::And(odd, zero));
                even = append(Node::Or(even_zero, odd_one));
                odd = append(Node::Or(even_one, odd_zero));
            }
            append(Node::Or(even, odd));
            Formula::new(parity)?
        },
    };
    Problem::new(vec![Shape::Bridge; dimensions], formula, conclusion)
}

/// A measurement row; times exclude construction, replay, and evidence drop.
#[derive(Debug)]
struct Row
{
    /// Total nodes across the two input formula tables.
    nodes: NodeId,
    /// Rules in the last validated proof.
    rules: NodeId,
    /// Median of five oracle invocations after one warmup.
    median: Duration,
}

/// Measures a query and independently validates every warmup and sample proof.
///
/// # Specification
/// - provides: median elapsed wall time of five proof-producing decisions.
/// - fails: query construction, oracle, replay, or positive-result
///   expectations.
/// - panics: none.
///
/// # Errors
/// Returns [`RunError::Shape`] or [`RunError::Invariant`].
///
/// # Adequacy
/// - hypothesis: L1 command execution exercises both search and replay with
///   actual timing output; malformed evidence cannot silently contribute a
///   timing row.
/// - witness: `tests::measurements_replay`
fn measure(
    family: Family,
    dimensions: DimensionCount,
) -> Result<Row, RunError>
{
    let problem = query(family, dimensions)?;
    let mut samples = Vec::with_capacity(5);
    let mut rules = NodeId::from(0);
    for sample in 0_usize .. 6 {
        let start = Instant::now();
        let evidence = black_box(decide(black_box(&problem)))?;
        let elapsed = start.elapsed();
        match evidence {
            | Evidence::Holds(proof) => {
                proof.validate(&problem)?;
                rules = NodeId::from(proof.rules.len());
            },
            | Evidence::Refuted(_) => return Err(RunError::Invariant),
        }
        if sample != 0 {
            samples.push(elapsed);
        }
    }
    samples.sort_unstable();
    let median = *samples.get(2).ok_or(RunError::Invariant)?;
    let (_, left, right) = problem.parts();
    Ok(Row {
        nodes: NodeId::from(left.nodes().len().saturating_add(right.nodes().len())),
        rules,
        median,
    })
}

/// Runs both measurement families and writes a Markdown table.
///
/// # Specification
/// - provides: reproducible input families and measured, validated evidence.
/// - fails: output failure or any measurement refusal is returned to the
///   process.
/// - panics: none.
///
/// # Errors
/// Returns the exact [`RunError`] encountered.
///
/// # Adequacy
/// - hypothesis: L1 the release command is the measurement observer; its rows
///   name the input sizes and evidence sizes so timings are not correctness
///   claims.
/// - witness: `tests::measurements_replay`
fn main() -> Result<(), RunError>
{
    let mut output = io::stdout().lock();
    writeln!(
        output,
        "| Family | Dimensions | Formula nodes | Proof rules | Median ns |"
    )?;
    writeln!(output, "| --- | ---: | ---: | ---: | ---: |")?;
    for (family, sizes) in [
        (Family::BoundaryParity, &[4_usize, 8, 12, 16, 18][..]),
        (Family::AtomicAmbient, &[16_usize, 64, 256, 1024, 4096][..]),
    ] {
        for &dimensions in sizes {
            let row = measure(family, DimensionCount::from(dimensions))?;
            writeln!(
                output,
                "| {family} | {dimensions} | {} | {} | {} |",
                usize::from(row.nodes),
                usize::from(row.rules),
                row.median.as_nanos()
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use super::DimensionCount;
    use super::Evidence;
    use super::Family;
    use super::Formula;
    use super::Node;
    use super::Problem;
    use super::decide;
    use super::query;

    #[test]
    fn measurements_replay()
    {
        for family in [Family::BoundaryParity, Family::AtomicAmbient] {
            let problem = query(family, DimensionCount::from(4)).expect("query");
            let Evidence::Holds(proof) = decide(&problem).expect("decision")
            else {
                panic!("valid entailment");
            };
            assert_eq!(proof.validate(&problem), Ok(()));
            let (context, _, conclusion) = problem.parts();
            let unguarded = Problem::new(
                context.to_vec(),
                Formula::new(vec![Node::Top]).expect("top"),
                conclusion.clone(),
            )
            .expect("unguarded");
            let Evidence::Refuted(model) = decide(&unguarded).expect("decision")
            else {
                panic!("endpoint coverage is not global");
            };
            assert_eq!(model.validate(&unguarded), Ok(()));
        }
    }
}
