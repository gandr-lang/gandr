//! Witnesses for reading a `sign` description as a graphical species.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;

use super::*;

/// Text a fixture spells: a name or a label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled<'text>(&'text str);

/// The input and output leg counts of a corolla.
#[derive(Clone, Copy, Debug)]
struct Legs(usize, usize);

/// An operation over the sort `M` named `name`, with one input leg per
/// entry of `inputs` and one output.
///
/// # Specification
/// trivial.
fn oper(
    Spelled(name): Spelled<'_>,
    inputs: &[Spelled<'_>],
) -> OperDesc
{
    OperDesc::new(
        name,
        BridgeArity::single_output(
            inputs
                .iter()
                .map(|&Spelled(input)| SortRef::new(input, "M"))
                .collect::<Vec<_>>(),
            SortRef::new("z", "M"),
        ),
        Attrs::empty(),
    )
}

/// A `sign` description named `Magma`, declaring the sort `M` and `opers`.
///
/// # Specification
/// trivial.
fn sign(opers: Vec<OperDesc>) -> SignDesc<()>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Magma"),
        Vec::new(),
        Vec::new(),
        opers,
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts([SortDesc::new("M", DeclPolarity::Data)])
}

/// The profile of a corolla with the legs `legs` counts.
///
/// # Specification
/// trivial.
fn profile(Legs(inputs, outputs): Legs) -> Profile
{
    Profile {
        inputs: PortCount::from(inputs),
        outputs: PortCount::from(outputs),
    }
}

/// A record label spelled `text`.
///
/// # Specification
/// trivial.
fn label(Spelled(text): Spelled<'_>) -> FieldLabel
{
    FieldLabel::from(String::from(text))
}

#[test]
fn a_sign_reads_as_its_generators_in_written_order()
{
    let description = Description::read(&sign(alloc::vec![
        oper(Spelled("times"), &[Spelled("x"), Spelled("y")]),
        oper(Spelled("one"), &[]),
        oper(Spelled("plus"), &[Spelled("x"), Spelled("y")]),
    ]))
    .unwrap();
    assert_eq!(description.name.as_ref(), "Magma");
    let read: Vec<_> = description
        .generators
        .iter()
        .map(|generator| (generator.label.as_ref(), generator.profile))
        .collect();
    assert_eq!(read, [
        ("times", profile(Legs(2, 1))),
        ("one", profile(Legs(0, 1))),
        ("plus", profile(Legs(2, 1))),
    ]);
    let species = description.species();
    assert_eq!(usize::from(species.count(profile(Legs(2, 1)))), 2);
    assert_eq!(usize::from(species.count(profile(Legs(0, 1)))), 1);
    assert_eq!(usize::from(species.count(profile(Legs(1, 2)))), 0);
    assert_eq!(
        description.generator(&label(Spelled("plus"))),
        Maybe::Present(&Generator {
            label: label(Spelled("plus")),
            profile: profile(Legs(2, 1)),
        })
    );
    assert_eq!(
        description.generator(&label(Spelled("minus"))),
        Maybe::Absent(generator::Absent::Unlisted)
    );
}

#[test]
fn a_description_outside_the_stratum_is_refused()
{
    let two_sorted = sign(Vec::new()).with_sorts([
        SortDesc::new("M", DeclPolarity::Data),
        SortDesc::new("N", DeclPolarity::Data),
    ]);
    assert_eq!(Description::read(&two_sorted), Err(Unread::Sorts));
    let mut ruled = sign(alloc::vec![oper(Spelled("times"), &[
        Spelled("x"),
        Spelled("y")
    ])]);
    ruled.rules = alloc::boxed::Box::from([RuleFace::new(
        FreeTerm::var("x"),
        FreeTerm::var("x"),
        Vec::new(),
        SurfaceSpan::default(),
    )]);
    assert_eq!(Description::read(&ruled), Err(Unread::Rules));
    let foreign = sign(alloc::vec![OperDesc::new(
        "size",
        BridgeArity::single_output([SortRef::new("x", "M")], SortRef::new("n", "Nat")),
        Attrs::empty(),
    )]);
    assert_eq!(
        Description::read(&foreign),
        Err(Unread::Leg {
            generator: Name::from("size"),
        })
    );
}
