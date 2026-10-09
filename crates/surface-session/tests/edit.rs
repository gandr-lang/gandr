//! Edit-action reconstruction: the localized diff of two revisions' lowered
//! core, its adjoint `apply`, and the localizer.
//!
//! Five groups, after the engine suite they port: single changes, each one
//! action at an exact path; coarse fallback, a changed former replaced
//! wholesale; localization, a source range mapped to the smallest enclosing
//! term with the diff inside it; application, `apply` as the diff's adjoint;
//! and the oracle, `apply` of a diff reproducing the new revision over
//! generated pairs.

use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::Occurrence;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_lowering::OriginTable;
use gandr_surface_session::Action;
use gandr_surface_session::ChildSlot;
use gandr_surface_session::CorePath;
use gandr_surface_session::EditScript;
use gandr_surface_session::Snapshot;
use gandr_surface_session::SourceEdit;
use gandr_surface_session::apply;
use gandr_surface_session::diff;
use gandr_surface_session::program;
use gandr_surface_session::resumed;
use gandr_surface_syntax::SourceText;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert;
use proptest::prop_assert_eq;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::grammar;
use crate::common::session;
use crate::common::submit;
use crate::generate::CASES;
use crate::generate::render;

/// The incremental fixture pair: one literal of a function tail changed.
const BASE: &str = include_str!("fixtures/incremental-base.gandr");
/// The edited half of the incremental fixture pair.
const EDITED: &str = include_str!("fixtures/incremental-edited.gandr");

/// The snapshot of `text`, which the lowering must read as a module.
///
/// # Specification
/// trivial.
fn snapshot<'text>(text: impl Into<Text<'text>>) -> Snapshot
{
    let text = text.into().0;
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let lowering = lower_source(&grammar, SourceText::from(text), &mut lowerings)
        .expect("the revision lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the lowering reads a module: {text:?}");
    };
    let program = program(&module, arena).expect("positions ascend");
    Snapshot::of(&program, module.origins())
}

/// The diff of `old` into `new`, asserted to apply back to `new`.
///
/// # Specification
/// trivial.
fn diff_sound(
    old: &Snapshot,
    new: &Snapshot,
) -> EditScript
{
    let script = diff(old, new);
    assert_eq!(
        apply(old.items(), &script),
        new.items(),
        "apply reproduces the new revision from {script:?}"
    );
    script
}

/// The integer literal written `text`.
///
/// # Specification
/// trivial.
fn integer(text: Text<'_>) -> Literal
{
    let magnitude =
        Magnitude::from_decimal_text(String::from(text.0)).expect("the text is decimal digits");
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
}

/// The child slots at these positions.
macro_rules! slots {
    ($($position:expr),* $(,)?) => {
        vec![$(ChildSlot::from({
            let position: usize = $position;
            position
        })),*]
    };
}

/// Whether `inner` sits under `outer`: the same item, `outer`'s slots a
/// prefix of `inner`'s.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nested(bool);

/// Whether `inner` sits under `outer`.
///
/// # Specification
/// trivial.
fn nested(
    outer: &CorePath,
    inner: &CorePath,
) -> Nested
{
    Nested(outer.item() == inner.item() && inner.slots().starts_with(outer.slots()))
}

/// The first reference of the declaration named `name`.
///
/// # Specification
/// trivial.
fn reference(name: Text<'_>) -> Reference
{
    Reference::Item {
        key: ItemKey::from(name.0),
        occurrence: Occurrence::from(0_usize),
    }
}

#[test]
fn literal_edit_is_one_set_int()
{
    let (base, edited) = (snapshot(BASE), snapshot(EDITED));
    let script = diff_sound(&base, &edited);
    let [
        Action::SetLiteral {
            ref path,
            ref from,
            ref to,
        },
    ] = *script.actions()
    else {
        panic!("exactly one in-place literal action: {script:?}");
    };
    assert_eq!(
        *path,
        CorePath::new(ItemOrdinal::from(0_usize), slots![0, 0, 0]),
        "the literal under the thunk, the lambda and the return"
    );
    assert_eq!(
        (from, to),
        (&integer(Text("1")), &integer(Text("2"))),
        "1 became 2"
    );
}

#[test]
fn item_insertion_leaves_neighbours_untouched()
{
    let base = snapshot(include_str!("fixtures/stale-relocation-base.gandr"));
    let edited = snapshot(include_str!("fixtures/stale-relocation-edited.gandr"));
    let script = diff_sound(&base, &edited);
    let inserted: Vec<&Action> = script
        .actions()
        .iter()
        .filter(|action| matches!(**action, Action::InsertItem { .. }))
        .collect();
    let [&Action::InsertItem { at, ref item }] = *inserted
    else {
        panic!("exactly one insertion: {script:?}");
    };
    assert_eq!(
        (at, item.reference()),
        (ItemOrdinal::from(0_usize), &reference(Text("inserted"))),
        "the new declaration enters at the front of the new list"
    );
    assert!(
        script
            .actions()
            .iter()
            .all(|action| !matches!(*action, Action::DeleteItem { .. })),
        "nothing is deleted: {script:?}"
    );
    for action in script.actions() {
        if let Maybe::Present(changed) = action.path() {
            assert_eq!(
                changed.item(),
                ItemOrdinal::from(0_usize),
                "only `alpha`, old item 0, is touched; the byte-shifted `target` and \
                 `omega` are never named: {script:?}"
            );
        }
    }
}

#[test]
fn hole_fill_and_erase()
{
    let owed = snapshot("def answer : Integer ;\n");
    let filled = snapshot("def answer : Integer ;\ndef answer = 42 ;\n");

    let fill = diff_sound(&owed, &filled);
    let [Action::FillHole { at, ref to }] = *fill.actions()
    else {
        panic!("filling the owed body is one FillHole: {fill:?}");
    };
    assert_eq!(at, ItemOrdinal::from(0_usize), "the one declaration");
    assert_eq!(
        to.nodes(),
        [ContentNode::Literal(integer(Text("42")))],
        "the hole is filled with the literal"
    );

    let erase = diff_sound(&filled, &owed);
    assert!(
        matches!(*erase.actions(), [Action::EraseToHole { at }] if at == ItemOrdinal::from(0_usize)),
        "dropping the definition erases the body to a hole: {erase:?}"
    );
}

#[test]
fn item_ascription_change_is_one_set_item_ascription()
{
    let base = snapshot("def f : Integer ;\ndef f = 1 ;\n");
    let edited = snapshot("def f : String ;\ndef f = 1 ;\n");
    let script = diff_sound(&base, &edited);
    assert!(
        matches!(*script.actions(), [Action::SetSignature { at, .. }] if at == ItemOrdinal::from(0_usize)),
        "the changed signature is one SetSignature on the kept item: {script:?}"
    );
}

#[test]
fn constructor_change_is_one_replace()
{
    let base = snapshot("def v = 1 ;\n");
    let edited = snapshot("def v = thunk { ret 1 } ;\n");
    let script = diff_sound(&base, &edited);
    let [Action::Replace { ref path, ref to }] = *script.actions()
    else {
        panic!("a changed value former is one coarse Replace: {script:?}");
    };
    assert_eq!(
        *path,
        CorePath::new(ItemOrdinal::from(0_usize), Vec::new()),
        "the body root"
    );
    assert!(
        matches!(to.nodes().first(), Some(&ContentNode::Thunk(_))),
        "the replacement is the thunk: {to:?}"
    );
}

#[test]
fn comp_constructor_change_is_one_replace()
{
    let function = "def f(x: Integer) -> F Integer { ret x }\n";
    let base = snapshot(&format!("{function}def v = thunk {{ ret 1 }} ;\n"));
    let edited = snapshot(&format!("{function}def v = thunk {{ (force f)(1) }} ;\n"));
    let script = diff_sound(&base, &edited);
    let [Action::Replace { ref path, ref to }] = *script.actions()
    else {
        panic!("a changed computation former is one coarse Replace: {script:?}");
    };
    assert_eq!(
        *path,
        CorePath::new(ItemOrdinal::from(1_usize), slots![0]),
        "the computation under the thunk, not the thunk"
    );
    assert!(
        matches!(to.nodes().first(), Some(&ContentNode::Application(..))),
        "the replacement is the application: {to:?}"
    );
}

#[test]
fn item_deletion_is_one_delete()
{
    let base = snapshot("def a = 1 ;\ndef b = 2 ;\n");
    let edited = snapshot("def a = 1 ;\n");
    let script = diff_sound(&base, &edited);
    assert!(
        matches!(*script.actions(), [Action::DeleteItem { at }] if at == ItemOrdinal::from(1_usize)),
        "deleting the second declaration is DeleteItem at old ordinal 1: {script:?}"
    );
}

#[test]
fn localize_finds_smallest_enclosing_term()
{
    let base = snapshot(BASE);
    let literal = CorePath::new(ItemOrdinal::from(0_usize), slots![0, 0, 0]);
    let Maybe::Present(span) = base.span(&literal)
    else {
        panic!("the literal has a span");
    };
    let Maybe::Present(exact) = base.localize(span)
    else {
        panic!("the literal's span localizes");
    };
    assert_eq!(exact, literal, "the literal localizes to itself");

    let root = CorePath::new(ItemOrdinal::from(0_usize), Vec::new());
    let Maybe::Present(body) = base.span(&root)
    else {
        panic!("the body has a span");
    };
    let Maybe::Present(wide) = base.localize(body)
    else {
        panic!("the body's span localizes");
    };
    assert!(
        wide.slots().len() < exact.slots().len(),
        "the whole body localizes higher than the literal: {wide:?}"
    );
    assert_eq!(
        nested(&wide, &exact),
        Nested(true),
        "the literal's locus {exact:?} nests inside the body's {wide:?}"
    );
}

#[test]
fn edit_locus_contains_the_diff()
{
    let (base, edited) = (snapshot(BASE), snapshot(EDITED));
    let literal = CorePath::new(ItemOrdinal::from(0_usize), slots![0, 0, 0]);
    let Maybe::Present(span) = base.span(&literal)
    else {
        panic!("the literal has a span");
    };
    // The edit turning `1` into `2`: one byte replaced by one byte.
    let Maybe::Present(locus) = base.edit_locus(SourceEdit::new(span, span.end()))
    else {
        panic!("the edit localizes");
    };
    assert_eq!(locus, literal, "the edit's locus is the literal");
    for action in diff(&base, &edited).actions() {
        if let Maybe::Present(changed) = action.path() {
            assert_eq!(
                nested(&locus, changed),
                Nested(true),
                "the changed path {changed:?} sits within the locus {locus:?}"
            );
        }
    }
}

#[test]
fn multi_point_edit_localizes_to_the_common_ancestor()
{
    let functions = "def f(x: Integer) -> F Integer { ret x }\n\
                     def g(x: Integer) -> F Integer { ret x }\n\
                     def shown : U (F Integer) ;\n";
    let base = snapshot(&format!(
        "{functions}def shown = thunk {{ (force f)(1) }} ;\n"
    ));
    let edited = snapshot(&format!(
        "{functions}def shown = thunk {{ (force g)(2) }} ;\n"
    ));
    // The application is the smallest term spanning both the callee and the
    // argument; its span is the edit's range.
    let application = CorePath::new(ItemOrdinal::from(2_usize), slots![0]);
    let Maybe::Present(span) = base.span(&application)
    else {
        panic!("the application has a span");
    };
    let Maybe::Present(locus) = base.localize(span)
    else {
        panic!("the application's span localizes");
    };
    assert_eq!(locus, application, "the locus is the application");

    let script = diff_sound(&base, &edited);
    let changed: Vec<&CorePath> = script
        .actions()
        .iter()
        .filter_map(|action| match action.path() {
            | Maybe::Present(changed) => Some(changed),
            | Maybe::Absent(_) => None,
        })
        .collect();
    assert_eq!(changed.len(), 2_usize, "two nodes change: {script:?}");
    for changed in &changed {
        assert_eq!(
            nested(&locus, changed),
            Nested(true),
            "the changed path {changed:?} sits within the common ancestor {locus:?}"
        );
    }
    assert!(
        script.actions().iter().any(|action| matches!(
            *action,
            Action::SetConstant { ref from, ref to, .. }
                if *from == reference(Text("f")) && *to == reference(Text("g"))
        )),
        "the callee changes from `f` to `g`: {script:?}"
    );
    assert!(
        script.actions().iter().any(|action| matches!(
            *action,
            Action::SetLiteral { ref from, ref to, .. }
                if *from == integer(Text("1")) && *to == integer(Text("2"))
        )),
        "the argument changes from 1 to 2: {script:?}"
    );
}

#[test]
fn self_diff_is_empty_and_apply_is_identity()
{
    let base = snapshot(BASE);
    let script = diff(&base, &base);
    assert_eq!(script.actions(), [], "a self-diff has no actions");
    assert_eq!(
        apply(base.items(), &script),
        base.items(),
        "applying the empty script is the identity"
    );
}

/// Which leaf of [`hand_built`] a revision changes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Leaf(usize);

/// One item over a hand-built arena whose body holds every multi-child
/// former of the body sorts, leaves 0 to 5 distinct string literals and leaf
/// 6 the innermost bound variable, the leaf `changed` names reading
/// `"changed"`, or the next variable out:
///
/// `thunk (case (pair "0" (inl "1")) (bind (ret "2") ((λ ret "3") "4"))
/// (force (pair "5" #0)))`.
///
/// # Specification
/// trivial.
fn hand_built(changed: Option<Leaf>) -> Snapshot
{
    let mut arena = CoreArena::new();
    let leaf = |arena: &mut CoreArena, at: Leaf| arena.value_literal(leaf_content(at, changed));
    let zero = leaf(&mut arena, Leaf(0_usize));
    let one = leaf(&mut arena, Leaf(1_usize));
    let injected = arena.value_injection(Side::Left, one);
    let scrutinee = arena.value_pair(zero, injected);
    let two = leaf(&mut arena, Leaf(2_usize));
    let bound = arena.computation_return(two);
    let three = leaf(&mut arena, Leaf(3_usize));
    let returned = arena.computation_return(three);
    let lambda = arena.computation_lambda(returned);
    let four = leaf(&mut arena, Leaf(4_usize));
    let applied = arena.computation_application(lambda, four);
    let on_left = arena.computation_bind(bound, applied);
    let five = leaf(&mut arena, Leaf(5_usize));
    let index = u32::from(changed == Some(Leaf(6_usize)));
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
    let forced = arena.value_pair(five, variable);
    let on_right = arena.computation_force(forced);
    let case = arena.computation_case(scrutinee, on_left, on_right);
    let body = arena.value_thunk(case);
    let declaration = Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(body),
        OriginToken::from(0_usize),
    );
    let program = Program::new(arena, vec![Item::new(ItemKey::from("hand"), declaration)])
        .expect("one item is ordered");
    Snapshot::of(&program, &OriginTable::new())
}

/// The literal leaf `at` of [`hand_built`] holds when `changed` is changed.
///
/// # Specification
/// trivial.
fn leaf_content(
    at: Leaf,
    changed: Option<Leaf>,
) -> Literal
{
    let content = if changed == Some(at) {
        String::from("changed")
    }
    else {
        format!("{}", at.0)
    };
    Literal::Text(StringLiteral::new(content))
}

#[test]
fn step_comp_child_order_matches_diff_and_rebuild()
{
    let item = ItemOrdinal::from(0_usize);
    let old = hand_built(None);
    for (leaf, written) in [
        (Leaf(0_usize), slots![0, 0, 0]),
        (Leaf(1_usize), slots![0, 0, 1, 0]),
        (Leaf(2_usize), slots![0, 1, 0, 0]),
        (Leaf(3_usize), slots![0, 1, 1, 0, 0, 0]),
        (Leaf(4_usize), slots![0, 1, 1, 1]),
        (Leaf(5_usize), slots![0, 2, 0, 0]),
    ] {
        let expected = CorePath::new(item, written);
        assert_eq!(
            old.node(&expected),
            Maybe::Present(&ContentNode::Literal(leaf_content(leaf, None))),
            "the path written for leaf {leaf:?} reads that leaf"
        );
        let script = diff_sound(&old, &hand_built(Some(leaf)));
        assert!(
            matches!(*script.actions(), [Action::SetLiteral { ref path, .. }] if *path == expected),
            "changing leaf {leaf:?} alone is one SetLiteral at {expected:?}: {script:?}"
        );
    }
    let variable = CorePath::new(item, slots![0, 2, 0, 1]);
    let innermost = (Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    assert_eq!(
        old.node(&variable),
        Maybe::Present(&ContentNode::Variable {
            zone: innermost.0,
            index: innermost.1,
        }),
        "the path written for the variable reads it"
    );
    let script = diff_sound(&old, &hand_built(Some(Leaf(6_usize))));
    assert_eq!(
        script.actions(),
        [Action::SetVariable {
            path: variable,
            from: innermost,
            to: (Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
        }],
        "changing the variable alone is one SetVariable"
    );
}

#[test]
fn a_submission_carries_the_edits_from_the_last_accepted_revision()
{
    let mut session = session(SourceRoot::Fixture);
    let first = submit(&mut session, BASE);
    let Maybe::Present(edits) = first.edits()
    else {
        panic!("an accepted revision carries edits");
    };
    assert_eq!(
        edits.actions().len(),
        2_usize,
        "the first revision inserts both declarations into nothing: {edits:?}"
    );
    assert!(
        edits
            .actions()
            .iter()
            .all(|action| matches!(*action, Action::InsertItem { .. })),
        "every edit from nothing is an insertion: {edits:?}"
    );

    let second = submit(&mut session, EDITED);
    assert_eq!(
        second.edits(),
        Maybe::Present(&diff(&snapshot(BASE), &snapshot(EDITED))),
        "the next revision carries the literal edit from the first"
    );

    let refused = submit(&mut session, "def a = 1 ;\nret a");
    assert_eq!(
        refused.edits(),
        Maybe::Absent(resumed::Absent::RefusedWhole),
        "a revision refused whole carries no edits"
    );
    assert_eq!(
        *session.snapshot(),
        snapshot(EDITED),
        "and leaves the latest accepted snapshot"
    );

    let third = submit(&mut session, BASE);
    assert_eq!(
        third.edits(),
        Maybe::Present(&diff(&snapshot(EDITED), &snapshot(BASE))),
        "the edits run from the latest accepted revision, past the refused one"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(CASES))]

    /// For generated revision pairs, `apply` of the diff reproduces the new
    /// revision's own snapshot: soundness holds even where localization
    /// falls back to a coarse replacement.
    #[test]
    fn apply_of_diff_reproduces_new(
        old in crate::generate::program(),
        new in crate::generate::program(),
    ) {
        let (old, new) = (snapshot(&render(&old)), snapshot(&render(&new)));
        let script = diff(&old, &new);
        prop_assert_eq!(apply(old.items(), &script), new.items(), "from {:?}", script);
    }

    /// A generated revision's self-diff is empty, and applying it is the
    /// identity.
    #[test]
    fn self_diff_is_identity(statements in crate::generate::program()) {
        let revision = snapshot(&render(&statements));
        let script = diff(&revision, &revision);
        prop_assert!(script.actions().is_empty(), "a self-diff is empty: {:?}", script);
        prop_assert_eq!(apply(revision.items(), &script), revision.items());
    }
}
