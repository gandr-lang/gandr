//! Runs every condition of the site at its bound and prints each outcome as
//! a Markdown table row: the condition, the bound, the verdict, the cases
//! examined and the smallest counter-example.
//!
//! Conditions on single maps run over the shapes of size at most five;
//! conditions on composable pairs and spans over size at most four.
//!
//! Run it with `cargo run --release -p gandr-theory-sites --example suites`.

use core::fmt::Display;
use std::io::Write;
use std::io::stdout;

use gandr_theory_sites::Catalogue;
use gandr_theory_sites::GeneratorBound;
use gandr_theory_sites::Outcome;
use gandr_theory_sites::Part;
use gandr_theory_sites::Scope;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::closure;
use gandr_theory_sites::codegeneracies;
use gandr_theory_sites::core_decomposition;
use gandr_theory_sites::corolla;
use gandr_theory_sites::degree_order;
use gandr_theory_sites::deletion_classes;
use gandr_theory_sites::direct_core;
use gandr_theory_sites::dual_rigidity;
use gandr_theory_sites::factorization;
use gandr_theory_sites::grounded_stratum;
use gandr_theory_sites::identities;
use gandr_theory_sites::intersection;
use gandr_theory_sites::invertibility;
use gandr_theory_sites::latching;
use gandr_theory_sites::pushouts;
use gandr_theory_sites::rigidity;
use gandr_theory_sites::split_lowering;
use gandr_theory_sites::unit_property;

/// Why the run stops: a shape the constructors refused, or the output.
enum RunError
{
    /// Building a catalogue or the scalars was refused.
    Shape(ShapeObstruction),
    /// Writing a row failed.
    Write(std::io::Error),
}

impl core::fmt::Debug for RunError
{
    /// Writes the cause, which `main` prints when it returns the error.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Shape(ref refusal) => write!(f, "a shape was refused: {refusal}"),
            | Self::Write(ref failure) => write!(f, "the output failed: {failure}"),
        }
    }
}

impl From<ShapeObstruction> for RunError
{
    /// Wraps the refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(refusal: ShapeObstruction) -> Self
    {
        Self::Shape(refusal)
    }
}

impl From<std::io::Error> for RunError
{
    /// Wraps the write failure.
    ///
    /// # Specification
    /// trivial.
    fn from(failure: std::io::Error) -> Self
    {
        Self::Write(failure)
    }
}

/// One table row: the condition, the bound and the outcome.
///
/// # Specification
/// trivial.
fn row<Witness>(
    out: &mut impl Write,
    condition: &impl Display,
    bound: ShapeSize,
    outcome: &Outcome<Witness>,
) -> std::io::Result<()>
where
    Witness: Display,
{
    let witness = match outcome.witness() {
        | quenchant_shape::shape::Maybe::Present(witness) => format!("`{witness}`"),
        | quenchant_shape::shape::Maybe::Absent(_) => "—".to_owned(),
    };
    writeln!(
        out,
        "| {condition} | ≤ {} | {} | {} | {witness} |",
        usize::from(bound),
        outcome.verdict(),
        usize::from(outcome.cases()),
    )
}

/// The header of an outcome table.
///
/// # Specification
/// trivial.
fn header(out: &mut impl Write) -> std::io::Result<()>
{
    writeln!(
        out,
        "| Condition | Size | Verdict | Cases | Smallest counter-example |"
    )?;
    writeln!(
        out,
        "| --------- | ---- | ------- | ----- | ------------------------ |"
    )
}

/// Runs every condition and prints its row.
///
/// # Specification
/// trivial.
fn main() -> Result<(), RunError>
{
    let mut out = stdout().lock();
    let (one, two) = (ShapeSize::from(5_usize), ShapeSize::from(4_usize));
    let single = Catalogue::build(one)?;
    let paired = Catalogue::build(two)?;
    let wide = Site::new(&single);
    let narrow = Site::new(&paired);
    writeln!(
        out,
        "shape classes: {} at size ≤ {}, {} at size ≤ {}",
        single.shapes().len(),
        usize::from(one),
        paired.shapes().len(),
        usize::from(two)
    )?;
    writeln!(out)?;
    header(&mut out)?;
    row(&mut out, &"identities", one, &identities(&wide))?;
    for (name, part) in [
        ("closure", Part::Whole),
        ("closure of the raising maps", Part::Raising),
        ("closure of the lowering maps", Part::Lowering),
    ] {
        row(&mut out, &name, two, &closure(&narrow, part))?;
    }
    row(
        &mut out,
        &"raising ∩ lowering = isomorphisms",
        one,
        &intersection(&wide),
    )?;
    row(
        &mut out,
        &"invertible ⇔ two-sided inverse",
        one,
        &invertibility(&wide),
    )?;
    row(
        &mut out,
        &"degree orders the raising maps",
        one,
        &degree_order(&wide, Scope::Raising),
    )?;
    row(
        &mut out,
        &"degree orders both classes",
        one,
        &degree_order(&wide, Scope::Both),
    )?;
    row(
        &mut out,
        &"point-free core is direct",
        one,
        &direct_core(&wide),
    )?;
    row(
        &mut out,
        &"latching categories are finite",
        one,
        &latching(&wide),
    )?;
    row(
        &mut out,
        &"factorization, unique up to unique iso",
        one,
        &factorization(&wide),
    )?;
    row(&mut out, &"rigidity (iv)", one, &rigidity(&wide))?;
    row(&mut out, &"dual rigidity (iv′)", one, &dual_rigidity(&wide))?;
    row(
        &mut out,
        &"lowering maps split",
        one,
        &split_lowering(&wide),
    )?;
    let pushed = pushouts(&narrow);
    row(
        &mut out,
        &"pushout along a deletion exists",
        two,
        &pushed.existence,
    )?;
    row(
        &mut out,
        &"pushed-out map is raising",
        two,
        &pushed.stability,
    )?;
    row(
        &mut out,
        &"deletions addressed by kernels",
        one,
        &deletion_classes(&wide),
    )?;
    row(
        &mut out,
        &"deletions as codegeneracies",
        one,
        &codegeneracies(&wide),
    )?;
    row(
        &mut out,
        &"point reaches each point once",
        one,
        &corolla(&wide),
    )?;
    row(
        &mut out,
        &"core beside points, uniquely",
        one,
        &core_decomposition(&single),
    )?;
    row(
        &mut out,
        &"grounded = zero points",
        one,
        &grounded_stratum(&single),
    )?;
    let units = unit_property(GeneratorBound::from(4_usize), &paired)?;
    writeln!(out)?;
    writeln!(
        out,
        "scalars of at most 4 generators: {}; units found: {}",
        usize::from(units.scalars),
        units.units.len()
    )?;
    for unit in &units.units {
        writeln!(out, "unit: `{unit}`")?;
    }
    writeln!(out)?;
    header(&mut out)?;
    row(
        &mut out,
        &"the unit is two-sided on every labelled diagram",
        two,
        &units.two_sided,
    )?;
    row(
        &mut out,
        &"no unit without the empty diagram",
        two,
        &units.content,
    )?;
    Ok(())
}
