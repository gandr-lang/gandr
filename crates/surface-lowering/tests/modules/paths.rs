//! Paths between signatures, lowered (#3487): a path is a module of two
//! functions between packed models and one round trip for each value member,
//! its bodies templates no declaration reaches the kernel from, and every way
//! out of that shape is refused by name.

use gandr_surface_lowering::LoweringRefusal;

use super::Amounts;
use super::Role;
use super::lower;
use super::name;
use super::rows;
use super::span_of;

/// The two signatures the path tests translate between.
const VERSIONS: &str = include_str!("functors/unformatted/versions.gandr");

#[test]
fn a_path_lowers_to_its_functions_and_its_round_trips_3487()
{
    let source = [
        VERSIONS,
        "path versions : Older <~> Newer where { into where { def reply = answer ; def tag = \
         tag ; } from where { def answer = reply ; def tag = tag ; } }\n",
    ]
    .concat();
    let found = rows(&lower(source.as_str()));
    let declared: Vec<(&str, Role)> = found
        .iter()
        .filter(|&&(ref path, ..)| path.starts_with("versions."))
        .map(|&(ref path, role, _)| (path.as_str(), role))
        .collect();
    assert_eq!(
        declared,
        [
            ("versions.into", Role::Declared),
            ("versions.from", Role::Declared),
            ("versions.answer", Role::Witness),
            ("versions.tag", Role::Witness),
            ("versions.reply", Role::Witness),
            ("versions.tag", Role::Witness),
        ],
        "the module declares its two functions, then one round trip for each value member \
         of the domain and of the codomain; the bodies are templates: {found:?}"
    );
    assert!(
        found
            .iter()
            .filter(|&&(ref path, ..)| path.starts_with("versions."))
            .all(|&(_, _, amounts)| amounts == Amounts::Completed),
        "each function and each round trip is a completed declaration: {found:?}"
    );
}

/// A body that moves a sort states it by a type member, and the path holds a
/// round trip for each sort beside each operation.
#[test]
fn a_path_that_moves_a_sort_states_its_round_trip_3487()
{
    let source = include_str!("functors/unformatted/moved-sort.gandr");
    let found = rows(&lower(source));
    let declared: Vec<(&str, Role)> = found
        .iter()
        .filter(|&&(ref path, ..)| path.starts_with("renamed."))
        .map(|&(ref path, role, _)| (path.as_str(), role))
        .collect();
    assert_eq!(
        declared,
        [
            ("renamed.into", Role::Declared),
            ("renamed.from", Role::Declared),
            ("renamed.M", Role::Witness),
            ("renamed.mul", Role::Witness),
            ("renamed.C", Role::Witness),
            ("renamed.times", Role::Witness),
        ],
        "each sort has its round trip beside each operation: {found:?}"
    );
    assert!(
        found
            .iter()
            .filter(|&&(ref path, ..)| path.starts_with("renamed."))
            .all(|&(_, _, amounts)| amounts == Amounts::Completed),
        "each function and each round trip is a completed declaration: {found:?}"
    );
}

#[test]
fn a_path_from_no_theory_is_refused_under_its_name_3487()
{
    let source = [
        VERSIONS,
        "path lost : Nowhere <~> Newer where { into where { def reply = 1 ; def tag = 2 ; } \
         from where { def answer = reply ; def tag = tag ; } }\n",
    ]
    .concat();
    let found = rows(&lower(source.as_str()));
    assert!(
        found.iter().any(|&(ref path, _, amounts)| path == "lost"
            && matches!(
                amounts,
                Amounts::Refused(LoweringRefusal::UnresolvedTypeHead { span, name: named, .. })
                    if named == name("Nowhere") && span == span_of(source.as_str(), "Nowhere", 0_usize)
            )),
        "a domain naming no theory refuses the path under its name, at the domain: {found:?}"
    );
}

#[test]
fn a_path_named_twice_is_refused_3487()
{
    let path = "path twice : Older <~> Newer where { into where { def reply = answer ; def tag = \
                tag ; } from where { def answer = reply ; def tag = tag ; } }\n";
    let source = [VERSIONS, path, path].concat();
    let found = rows(&lower(source.as_str()));
    assert!(
        found.iter().any(|&(_, _, amounts)| amounts
            == Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                span: span_of(source.as_str(), "twice", 1_usize),
                name: name("twice"),
                first: span_of(source.as_str(), "twice", 0_usize),
            })),
        "the second path of one name is refused at its name: {found:?}"
    );
}
