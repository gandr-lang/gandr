//! The namespace engine, driven through the design's worked cases: selective
//! import, qualified import as a renaming of the root, the deep patch that
//! merges instead of capturing, re-export control and typo resistance; the
//! visible/export split under sections; all three events under a permissive,
//! a rejecting and a rewriting policy; the import lowering that binds an alias
//! through `alias_as`; and the claim that no walk of the engine recurses.
//!
//! The namespace engine's cases, in a `cfg(test)` module so the crate's lint
//! wall reads them as test code rather than as shipping code.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::CoreArena;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::ImportBinding;
use gandr_surface_lowering::ImportDeclaration;
use gandr_surface_lowering::ImportIndex;
use gandr_surface_lowering::ImportResolution;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::ImportUri;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::ModuleImports;
use gandr_surface_lowering::Onto;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_lowering::circuit::SignatureFault;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::description::DescriptionFault;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Binding;
use gandr_surface_lowering::namespace::Collision;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::EventKind;
use gandr_surface_lowering::namespace::EventRejection;
use gandr_surface_lowering::namespace::Modifier;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::NamespaceEvent;
use gandr_surface_lowering::namespace::NamespaceEventHandler;
use gandr_surface_lowering::namespace::PermissiveHandler;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering::namespace::RejectionReason;
use gandr_surface_lowering::namespace::Scope;
use gandr_surface_lowering::namespace::ScopeError;
use gandr_surface_lowering::namespace::Segment;
use gandr_surface_lowering::namespace::SegmentCount;
use gandr_surface_lowering::namespace::Trie;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

/// The depth of the chain the iteration claim is made over.
const DEPTH: usize = 100_000;

/// Half of [`DEPTH`], where the chain is cut and grafted back.
const HALF_DEPTH: usize = 50_000;

/// A stack far too small for a walk recursing once per segment of the
/// chain, and ample for one whose worklists live on the heap.
const SMALL_STACK_BYTES: usize = 64 * 1024;

/// The payload a test binds: a marker standing in for whatever an
/// elaborator resolves a path to.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Payload(u32);

/// The hook vocabulary these tests give meaning to.
///
/// # Specification
/// - requires: interpreted by the rewriting handler when used as an action.
/// - ensures: drop requests an empty result and keep requests the existing
///   namespace; another handler may instead treat the label as event data.
/// - provides: a closed hook vocabulary independent of the namespace engine.
/// - fails: none as a label.
/// - panics: none.
/// - executable: none — the subject and interpreting handler are not retained;
///   the hook callback specifies the actual transition.
///
/// # Adequacy
/// - hypothesis: L3 — one engine and two labels produce empty and unchanged
///   namespaces under the rewriting policy.
/// - witness: `tests::namespace::a_hook_can_replace_the_namespace`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HookLabel
{
    /// Replace the namespace the hook reached with the empty one.
    DropEverything,
    /// Leave the namespace the hook reached alone.
    KeepEverything,
}

/// One entry of a test namespace: a dotted path and the payload it binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Entry
{
    /// The dotted rendering of the bound path.
    path: DottedName<'static>,
    /// The payload bound there.
    payload: Payload,
}

/// A policy that refuses every event it is asked about: the counterpart
/// to [`PermissiveHandler`], under which the engine core is identical.
///
/// # Specification
/// - requires: nothing.
/// - ensures: missing selections, collisions and hooks are rejected at their
///   accumulated paths.
/// - provides: a rejecting policy without changing the namespace engine.
/// - fails: each callback returns its event-specific rejection.
/// - panics: none.
/// - executable: none — the policy has no runtime state or event input on the
///   type; its three callbacks specify their rejection kind and path.
///
/// # Adequacy
/// - hypothesis: L3 — real modifier and scope operations distinguish missing
///   selection, shadow and nested hook rejection, including transactionality.
/// - witness: `tests::namespace::a_rejecting_handler_refuses_a_missing_renaming_source`
/// - witness: `tests::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
/// - witness: `tests::namespace::a_refused_nested_hook_preserves_the_namespace_transaction`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct RejectingHandler;

impl NamespaceEventHandler<Payload, ()> for RejectingHandler
{
    type Label = HookLabel;

    /// Refuse: a missing selection is a typo.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: rejection names the missing-selection event and the exact
    ///   accumulated path.
    /// - provides: the rejecting counterpart to the permissive namespace
    ///   policy.
    /// - fails: always returns a not-found rejection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing rename is refused at its requested source
    ///   path rather than accepted as an empty import.
    /// - witness: `tests::namespace::a_rejecting_handler_refuses_a_missing_renaming_source`
    #[spec(
            ensures: |ret| matches!(ret, Err(ref rejection) if rejection.kind() == EventKind::NotFound && rejection.path() == path),
        )]
    fn not_found(
        &mut self,
        path: &NamePath,
    ) -> Result<(), EventRejection>
    {
        Err(EventRejection::new(
            EventKind::NotFound,
            path.clone(),
            RejectionReason::from("nothing matched here; check for a typo"),
        ))
    }

    /// Refuse: this policy forbids shadowing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: rejection names shadowing and the collision’s accumulated
    ///   path.
    /// - provides: a policy that does not silently select either colliding
    ///   binding.
    /// - fails: always returns a shadow rejection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refused multi-entry imports and section merges expose
    ///   their collision path and preserve the specified prior state.
    /// - witness: `tests::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
    /// - witness: `tests::namespace::a_refused_closing_merge_keeps_its_prefix_and_closes_the_section`
    #[spec(
            ensures: |ret| matches!(ret, Err(ref rejection) if rejection.kind() == EventKind::Shadow && rejection.path() == path),
        )]
    fn shadow(
        &mut self,
        path: &NamePath,
        _collision: Collision<Payload, ()>,
    ) -> Result<Binding<Payload, ()>, EventRejection>
    {
        Err(EventRejection::new(
            EventKind::Shadow,
            path.clone(),
            RejectionReason::from("this policy forbids shadowing"),
        ))
    }

    /// Refuse: this policy recognizes no hooks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: rejection names the hook event and its accumulated path.
    /// - provides: an explicit policy refusal rather than an unrecognized no-op
    ///   hook.
    /// - fails: always returns a hook rejection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested hook refuses after an intermediate
    ///   relocation, and the scoped transaction retains the original namespace.
    /// - witness: `tests::namespace::a_refused_nested_hook_preserves_the_namespace_transaction`
    #[spec(
            ensures: |ret| matches!(ret, Err(ref rejection) if rejection.kind() == EventKind::Hook && rejection.path() == path),
        )]
    fn hook(
        &mut self,
        path: &NamePath,
        _label: &HookLabel,
        _subject: Trie<Payload, ()>,
    ) -> Result<Trie<Payload, ()>, EventRejection>
    {
        Err(EventRejection::new(
            EventKind::Hook,
            path.clone(),
            RejectionReason::from("this policy recognizes no hooks"),
        ))
    }
}

/// A permissive policy whose hooks do something.
///
/// # Specification
/// - requires: nothing.
/// - ensures: missing selections continue, later bindings win collisions, and
///   hooks interpret the supplied label.
/// - provides: an independently chosen permissive rewriting policy.
/// - fails: never rejects an event.
/// - panics: none.
/// - executable: none — the policy type retains no event input; its callbacks
///   carry the executable event and transition relations.
///
/// # Adequacy
/// - hypothesis: L3 — a miss followed by a collision distinguishes continuation
///   and right bias; two hook labels distinguish replacement from identity.
/// - witness: `tests::namespace::rewriting_policy_continues_after_a_miss_and_keeps_the_later_collision`
/// - witness: `tests::namespace::a_hook_can_replace_the_namespace`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct RewritingHandler;

impl NamespaceEventHandler<Payload, ()> for RewritingHandler
{
    type Label = HookLabel;

    /// Continue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a missing selection is accepted.
    /// - provides: permissive continuation for the rewriting policy.
    /// - fails: never rejects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing selection precedes two colliding union
    ///   branches; the later branch’s distinct payload wins after permissive
    ///   continuation.
    /// - witness: `tests::namespace::rewriting_policy_continues_after_a_miss_and_keeps_the_later_collision`
    #[spec(
            ensures: |ret| ret == Ok(()),
        )]
    fn not_found(
        &mut self,
        _path: &NamePath,
    ) -> Result<(), EventRejection>
    {
        Ok(())
    }

    /// Keep the later binding.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the later binding’s payload wins the collision.
    /// - provides: deterministic right-biased rewriting.
    /// - fails: never rejects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing selection precedes two colliding union
    ///   branches; the later branch’s distinct payload wins after permissive
    ///   continuation.
    /// - witness: `tests::namespace::rewriting_policy_continues_after_a_miss_and_keeps_the_later_collision`
    #[spec(
            captures: expected = collision.latter.data,
            ensures: |ret| matches!(ret, Ok(ref binding) if binding.data == expected),
        )]
    fn shadow(
        &mut self,
        _path: &NamePath,
        collision: Collision<Payload, ()>,
    ) -> Result<Binding<Payload, ()>, EventRejection>
    {
        Ok(collision.latter)
    }

    /// Drop or keep the namespace, as the label says.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the drop label returns the empty namespace and the keep label
    ///   returns the supplied namespace.
    /// - provides: two observable hook interpretations over the same engine.
    /// - fails: never rejects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — drop and keep distinguish namespace replacement from
    ///   identity on the named nonempty fixture.
    /// - witness: `tests::namespace::a_hook_can_replace_the_namespace`
    #[spec(
            captures: before = subject.binding_count(),
            ensures: |ret| match *label {
                | HookLabel::DropEverything => {
                    matches!(ret, Ok(ref namespace) if usize::from(namespace.binding_count()) == 0)
                },
                | HookLabel::KeepEverything => {
                    matches!(ret, Ok(ref namespace) if namespace.binding_count() == before)
                },
            },
        )]
    fn hook(
        &mut self,
        _path: &NamePath,
        label: &HookLabel,
        subject: Trie<Payload, ()>,
    ) -> Result<Trie<Payload, ()>, EventRejection>
    {
        match *label {
            HookLabel::DropEverything => Ok(Trie::empty()),
            HookLabel::KeepEverything => Ok(subject),
        }
    }
}

/// The path `text` renders as.
///
/// # Specification
/// trivial.
fn path<Text>(text: Text) -> NamePath
where
    Text: Into<DottedName<'static>>,
{
    NamePath::from(text.into())
}

/// The entry binding `payload` at the path `text` renders as.
///
/// # Specification
/// trivial.
fn entry<Text>(
    text: Text,
    payload: Payload,
) -> Entry
where
    Text: Into<DottedName<'static>>,
{
    Entry {
        path: text.into(),
        payload,
    }
}

/// The namespace binding each of `entries`.
///
/// # Specification
/// - requires: the dotted strings describe the fixture’s intended paths.
/// - ensures: each distinct path is bound to the last entry for that path, with
///   no additional bindings.
/// - provides: the input namespace for semantic modifier witnesses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the worked namespace inventories retain distinct payloads
///   and paths before selection, relocation and collision.
/// - witness: `tests::namespace::a_deep_patch_merges_instead_of_capturing`
/// - witness: `tests::namespace::renaming_drops_whatever_was_at_the_target`
/// - witness: `tests::namespace::rewriting_policy_continues_after_a_miss_and_keeps_the_later_collision`
#[spec(
        ensures: |ret| {
            let mut distinct = 0_usize;
            entries.iter().enumerate().all(|(index, entry)| { if entries.iter().skip(index.saturating_add(1)).any(|later| later.path == entry.path) { return true; } distinct = distinct.saturating_add(1); matches!(ret.get(&path(entry.path)), Maybe::Present(binding) if binding.data == entry.payload) }) && usize::from(ret.binding_count()) == distinct
        },
    )]
fn namespace(entries: &[Entry]) -> Trie<Payload, ()>
{
    entries
        .iter()
        .map(|item| (path(item.path), Binding::new(item.payload, ())))
        .collect()
}

/// The namespace's dotted paths with their payloads, in ascending order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every binding is rendered in trie order with its own payload; the
///   root renders as a period.
/// - provides: the semantic namespace observer used by the worked cases.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the listed worked cases — distinct path and payload
///   inventories distinguish selection, relocation and right-biased merging.
/// - witness: `tests::namespace::only_keeps_the_named_subtree_and_drops_the_rest`
/// - witness: `tests::namespace::a_deep_patch_merges_instead_of_capturing`
#[spec(
        ensures: |ret| {
            ret.len() == usize::from(subject.binding_count())
                && ret.iter().zip(subject.iter()).all(
                    |(&(ref rendered, payload), (bound, binding))| {
                        payload == binding.data && {
                            if bound.segments().is_empty() {
                                rendered == "."
                            }
                            else {
                                rendered
                                    .chars()
                                    .eq(bound.segments().iter().enumerate().flat_map(
                                        |(index, segment)| {
                                            (index != 0)
                                                .then_some('.')
                                                .into_iter()
                                                .chain(segment.as_ref().chars())
                                        },
                                    ))
                            }
                        }
                    },
                )
        },
    )]
fn listing(subject: &Trie<Payload, ()>) -> Vec<(String, Payload)>
{
    subject
        .iter()
        .map(|(bound, binding)| (format!("{bound}"), binding.data))
        .collect()
}

/// The listing `entries` spell.
///
/// # Specification
/// - requires: entries are supplied in the order expected by the witness.
/// - ensures: paths and payloads are copied in that order without sorting or
///   namespace interpretation.
/// - provides: a literal expected inventory independent of trie traversal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the named worked cases — the literal inventory is
///   compared with the separately traversed namespace after each operation.
/// - witness: `tests::namespace::a_deep_patch_merges_instead_of_capturing`
/// - witness: `tests::namespace::renaming_drops_whatever_was_at_the_target`
#[spec(
        ensures: |ret| {
            ret.len() == entries.len()
                && ret
                    .iter()
                    .zip(entries)
                    .all(|(&(ref rendered, payload), entry)| {
                        rendered == entry.path.as_ref() && payload == entry.payload
                    })
        },
    )]
fn expected(entries: &[Entry]) -> Vec<(String, Payload)>
{
    entries
        .iter()
        .map(|item| (String::from(item.path.as_ref()), item.payload))
        .collect()
}

/// `modifier` run over `subject` under the warn-and-allow policy, beside
/// the events it performed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the modifier’s result and ordered event journal under the
///   permissive policy.
/// - provides: the shared runner for worked modifier cases.
/// - fails: no policy rejection is possible.
/// - panics: if the permissive-policy guarantee is violated.
/// - executable: none — the original namespace is consumed and the modifier’s
///   constructors are opaque here; checking the full transition and event order
///   would require another owned execution.
///
/// # Adequacy
/// - hypothesis: L2 on the listed worked cases — exact output inventories and
///   event sequences distinguish selection, relocation, union and nested
///   event-path accumulation under the permissive policy.
/// - witness: `tests::namespace::each_union_branch_runs_on_the_original_namespace`
/// - witness: `tests::namespace::a_nested_event_reports_the_accumulated_prefix`
/// - witness: `tests::namespace::a_nested_shadow_reports_the_accumulated_prefix`
fn permissive(
    modifier: &Modifier<HookLabel>,
    subject: Trie<Payload, ()>,
) -> (Trie<Payload, ()>, Vec<NamespaceEvent<HookLabel>>)
{
    let mut handler = PermissiveHandler::<HookLabel>::new();
    let outcome = modifier
        .apply(subject, &mut handler)
        .expect("the permissive policy rejects nothing");
    (outcome, handler.events().to_vec())
}

/// The `arith` namespace the design's import examples use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the three arithmetic example bindings have their specified
///   distinct payloads.
/// - provides: a nontrivial input tree for the worked modifier cases.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the worked cases — selecting and patching the natural
///   and integer subtrees distinguish their shared leaf spellings.
/// - witness: `tests::namespace::only_keeps_the_named_subtree_and_drops_the_rest`
/// - witness: `tests::namespace::a_deep_patch_merges_instead_of_capturing`
#[spec(
        ensures: |ret| {
            usize::from(ret.binding_count()) == 3 && [("nat.plus.assoc", Payload(1)), ("nat.times.assoc", Payload(2)), ("int.plus.assoc", Payload(3))].iter().all(|&(name, payload)| matches!(ret.get(&path(name)), Maybe::Present(binding) if binding.data == payload))
        },
    )]
fn arith() -> Trie<Payload, ()>
{
    namespace(&[
        entry("nat.plus.assoc", Payload(1)),
        entry("nat.times.assoc", Payload(2)),
        entry("int.plus.assoc", Payload(3)),
    ])
}

/// The shape a seeded prelude takes as an initial visible namespace.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the three prelude-shaped namespaces retain their distinct read,
///   environment and primitive payloads.
/// - provides: a visible namespace distinct from a section’s export namespace.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — sections inherit visible names without automatically
///   exporting them, distinguishing visibility from re-export.
/// - witness: `tests::namespace::a_section_inherits_the_visible_namespace_and_exports_nothing_yet`
#[spec(
        ensures: |ret| {
            usize::from(ret.binding_count()) == 3 && [("fs.read", Payload(10)), ("env.get", Payload(11)), ("prim.id", Payload(12))].iter().all(|&(name, payload)| matches!(ret.get(&path(name)), Maybe::Present(binding) if binding.data == payload))
        },
    )]
fn prelude_shaped() -> Trie<Payload, ()>
{
    namespace(&[
        entry("fs.read", Payload(10)),
        entry("env.get", Payload(11)),
        entry("prim.id", Payload(12)),
    ])
}

/// The bytes from `start` to `end`.
///
/// # Specification
/// - requires: the converted start does not exceed the converted end.
/// - ensures: the supplied byte endpoints are retained exactly.
/// - provides: an independent span fixture.
/// - fails: none for ordered endpoints.
/// - panics: if the converted endpoints are reversed.
/// - executable: none — the generic conversion consumes both inputs; retaining
///   them would add bounds or copies, while checking the result’s ordering
///   would only restate the span type.
///
/// # Adequacy
/// - hypothesis: L3 on ordered endpoint fixtures — duplicate aliases retain the
///   later and earlier source spans independently.
/// - witness: `tests::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
fn bytes<Bound>(
    start: Bound,
    end: Bound,
) -> ByteSpan
where
    Bound: Into<ByteOffset>,
{
    ByteSpan::new(start.into(), end.into()).expect("the span is ordered")
}

/// The built-in grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// The tree the parser builds for `source` under `pbg`, repaired or not.
///
/// # Specification
/// - requires: the parser accepts the source under the supplied grammar.
/// - ensures: the returned tree retains that source and grammar, whether clean
///   or repaired.
/// - provides: a real parser-produced namespace fixture.
/// - fails: no parser failure is converted into an empty tree.
/// - panics: if parsing fails.
///
/// # Adequacy
/// - hypothesis: L3 — complete and missing-alias imports reach lowering with
///   their original spans rather than a synthetic replacement source.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
#[spec(
        ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
    )]
fn parsed<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> SyntaxTree<'source>
{
    parse(pbg, source)
        .expect("the parser reads the source")
        .into_tree()
}

/// `tree` lowered under `pbg` against the empty outermost scope.
///
/// # Specification
/// - requires: the grammar and tree are passed through unchanged.
/// - ensures: grammar mismatch is returned as an engine refusal; successful
///   declarations retain admission order.
/// - provides: a namespace-focused lowering fixture with no outermost names.
/// - fails: preserves the lowering engine’s refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — admitted and duplicate source imports preserve their
///   namespace effects and located refusal rather than silently resolving
///   addresses.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
#[spec(
        ensures: |ret| match ret {
            | Ok(ref module) => {
                tree.grammar() == pbg.fingerprint()
                    && module.declarations().windows(2).all(|pair| match *pair {
                        | [ref left, ref right] => left.constant() < right.constant(),
                        | _ => false,
                    })
            },
            | Err(LoweringRefusal::GrammarMismatch { .. }) => tree.grammar() != pbg.fingerprint(),
            | Err(_) => tree.grammar() == pbg.fingerprint(),
        },
    )]
fn lowered<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    let mut arena = CoreArena::new();
    lower_module(
        pbg,
        tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
}

/// The chain of `depth` segments, each `s`.
///
/// # Specification
/// - requires: the requested path fits in memory.
/// - ensures: exactly the requested number of segments, every one spelled `s`.
/// - provides: a depth-controlled input for the iteration witness.
/// - fails: never.
/// - panics: none within available memory.
///
/// # Adequacy
/// - hypothesis: L3 — the deep-path witness exercises namespace operations and
///   destruction on a small stack at the requested finite depth.
/// - witness: `tests::namespace::every_namespace_walk_is_iterative`
#[spec(
        ensures: |ret| {
            ret.depth() == depth && ret.segments().iter().all(|segment| segment.as_ref() == "s")
        },
    )]
fn chain(depth: SegmentCount) -> NamePath
{
    NamePath::from(
        core::iter::repeat_n(Segment::from("s"), usize::from(depth)).collect::<Vec<Segment>>(),
    )
}

// The modifier language's worked cases.

#[test]
fn only_keeps_the_named_subtree_and_drops_the_rest()
{
    let (outcome, events) = permissive(&Modifier::only(path("nat")), arith());
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("nat.plus.assoc", Payload(1)),
            entry("nat.times.assoc", Payload(2)),
        ]),
        "selective import keeps the whole subtree and nothing else"
    );
    assert!(
        events.is_empty(),
        "a selection that matched something performs no event"
    );
}

#[test]
fn except_drops_the_named_subtree()
{
    let (outcome, events) = permissive(&Modifier::except(path("nat")), arith());
    assert_eq!(
        listing(&outcome),
        expected(&[entry("int.plus.assoc", Payload(3))]),
        "exclusion is subtree-grained, exactly like selection"
    );
    assert!(
        events.is_empty(),
        "an exclusion that matched something performs no event"
    );
}

#[test]
fn in_runs_the_inner_modifier_on_one_subtree()
{
    let modifier = Modifier::in_subtree(path("nat"), Modifier::only(path("plus")));
    let (outcome, events) = permissive(&modifier, arith());
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("int.plus.assoc", Payload(3)),
            entry("nat.plus.assoc", Payload(1)),
        ]),
        "`in nat only plus` keeps nat.plus.assoc, drops nat.times.assoc, and leaves int alone"
    );
    assert!(events.is_empty(), "nothing was missing");
}

#[test]
fn qualified_import_renames_the_root_to_the_alias()
{
    let modifier = Modifier::renaming(NamePath::root(), path("arith"));
    let (outcome, _events) = permissive(&modifier, arith());
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("arith.int.plus.assoc", Payload(3)),
            entry("arith.nat.plus.assoc", Payload(1)),
            entry("arith.nat.times.assoc", Payload(2)),
        ]),
        "qualified import is a renaming of the root, so every path gains the alias"
    );
}

#[test]
fn renaming_to_the_root_unqualifies()
{
    let modifier = Modifier::renaming(path("nat"), NamePath::root());
    let (outcome, _events) = permissive(&modifier, arith());
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("plus.assoc", Payload(1)),
            entry("times.assoc", Payload(2)),
        ]),
        "renaming to the root hoists the subtree and drops everything else"
    );
}

#[test]
fn the_checked_renaming_builder_performs_not_found_on_an_absent_source()
{
    let (outcome, events) = permissive(&Modifier::renaming(path("nta"), path("natural")), arith());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound { path: path("nta") }]),
        "the builder carries the emptiness check, so a mistyped source is reported at the \
             path the user wrote"
    );
    assert_eq!(
        listing(&outcome),
        listing(&arith()),
        "and relocating an empty subtree moves nothing"
    );
}

#[test]
fn the_core_relocation_performs_no_emptiness_check()
{
    let (outcome, events) =
        permissive(&Modifier::relocation(path("nta"), path("natural")), arith());
    assert!(
        events.is_empty(),
        "the core constructor is the unchecked relocation; the check lives in the builder \
             that wraps it"
    );
    assert_eq!(
        listing(&outcome),
        listing(&arith()),
        "and it moves nothing either, silently"
    );
}

#[test]
fn a_rejecting_handler_refuses_a_missing_renaming_source()
{
    let mut handler = RejectingHandler;
    let rejection = Modifier::renaming(path("nta"), path("natural"))
        .apply(arith(), &mut handler)
        .expect_err("this policy treats a typo as fatal");
    assert_eq!(
        rejection.kind(),
        EventKind::NotFound,
        "typo resistance reaches renaming, not only selection"
    );
    assert_eq!(
        *rejection.path(),
        path("nta"),
        "and names the source the user wrote"
    );
}

#[test]
fn renaming_drops_whatever_was_at_the_target()
{
    let subject = namespace(&[
        entry("patch.is_prefix", Payload(1)),
        entry("string.length", Payload(2)),
    ]);
    let modifier = Modifier::renaming(path("patch"), path("string"));
    let (outcome, events) = permissive(&modifier, subject);
    assert_eq!(
        listing(&outcome),
        expected(&[entry("string.is_prefix", Payload(1))]),
        "the target subtree is discarded rather than merged"
    );
    assert!(
        events.is_empty(),
        "dropping the target is silent; the safety net is a later scope-check failure"
    );
}

#[test]
fn a_deep_patch_merges_instead_of_capturing()
{
    let subject = namespace(&[entry("a.x", Payload(1)), entry("b.a.y", Payload(2))]);
    let modifier = Modifier::union(Vec::from([
        Modifier::all(),
        Modifier::renaming(path("b"), NamePath::root()),
    ]));
    let (outcome, events) = permissive(&modifier, subject);
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("a.x", Payload(1)),
            entry("a.y", Payload(2)),
            entry("b.a.y", Payload(2)),
        ]),
        "`a.y` joins the implicit `a` namespace instead of shadowing `a.x`"
    );
    assert!(
        events.is_empty(),
        "no two bindings landed on one path, so nothing was shadowed"
    );
}

#[test]
fn each_union_branch_runs_on_the_original_namespace()
{
    let modifier = Modifier::union(Vec::from([
        Modifier::only(path("nat")),
        Modifier::only(path("int")),
    ]));
    let (outcome, events) = permissive(&modifier, arith());
    assert_eq!(
        listing(&outcome),
        listing(&arith()),
        "both branches see the whole input, so selecting each half and unioning restores it"
    );
    assert!(
        events.is_empty(),
        "neither selection ran on the other's result, so neither matched nothing"
    );
}

#[test]
fn the_empty_sequence_is_the_identity()
{
    let (outcome, events) = permissive(&Modifier::id(), arith());
    assert_eq!(
        listing(&outcome),
        listing(&arith()),
        "`seq ()` changes nothing"
    );
    assert!(events.is_empty(), "and checks nothing");
}

#[test]
fn the_empty_union_is_the_empty_namespace()
{
    let (outcome, events) = permissive(&Modifier::union(Vec::new()), arith());
    assert_eq!(
        listing(&outcome),
        expected(&[]),
        "`union ()` drops everything without checking anything"
    );
    assert!(events.is_empty(), "the empty union performs no event");
}

#[test]
fn except_on_an_absent_subtree_performs_not_found()
{
    let (outcome, events) = permissive(&Modifier::except(path("nta")), arith());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound { path: path("nta") }]),
        "`except p` is `in p none`, and `none` checks emptiness before it drops, so \
             excluding an absent subtree is the typo signal selecting one gives"
    );
    assert_eq!(
        listing(&outcome),
        listing(&arith()),
        "and excluding an empty subtree excludes nothing"
    );
}

#[test]
fn the_identity_checks_nothing_on_an_empty_namespace()
{
    let (outcome, events) = permissive(&Modifier::id(), Trie::empty());
    assert!(
        events.is_empty(),
        "`id` is `seq ()`, which carries no emptiness check: the whole difference from `all`"
    );
    assert_eq!(listing(&outcome), expected(&[]), "and it changes nothing");
}

#[test]
fn none_drops_everything_and_flags_an_empty_input()
{
    let (outcome, events) = permissive(&Modifier::none(), arith());
    assert_eq!(listing(&outcome), expected(&[]), "`none` drops everything");
    assert!(
        events.is_empty(),
        "the input was not empty, so no not-found event was performed"
    );

    let (emptied, flagged) = permissive(&Modifier::none(), Trie::empty());
    assert_eq!(listing(&emptied), expected(&[]), "still nothing");
    assert_eq!(
        flagged,
        Vec::from([NamespaceEvent::NotFound {
            path: NamePath::root(),
        }]),
        "`none` on an already-empty namespace performs not-found at the root"
    );
}

#[test]
fn all_performs_not_found_on_an_empty_namespace()
{
    let (_outcome, events) = permissive(&Modifier::all(), Trie::empty());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound {
            path: NamePath::root(),
        }]),
        "`all` is the emptiness check, so an empty namespace is the signal"
    );
}

#[test]
fn a_selection_that_matched_nothing_performs_not_found()
{
    let (outcome, events) = permissive(&Modifier::only(path("nta")), arith());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound { path: path("nta") }]),
        "the misspelling is reported at the path the user wrote, once"
    );
    assert_eq!(
        listing(&outcome),
        expected(&[]),
        "and the selection still yields nothing, so the mistake cannot pass unnoticed"
    );
}

#[test]
fn a_nested_event_reports_the_accumulated_prefix()
{
    let modifier = Modifier::in_subtree(path("nat"), Modifier::only(path("mnus")));
    let (_outcome, events) = permissive(&modifier, arith());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound {
            path: path("nat.mnus"),
        }]),
        "an event inside `in nat` names the full path, not the subtree-relative one"
    );
}

#[test]
fn a_nested_shadow_reports_the_accumulated_prefix()
{
    let subject = namespace(&[entry("nat.a.x", Payload(1)), entry("nat.x", Payload(2))]);
    let modifier = Modifier::in_subtree(
        path("nat"),
        Modifier::union(Vec::from([
            Modifier::id(),
            Modifier::renaming(path("a"), NamePath::root()),
        ])),
    );
    let (outcome, events) = permissive(&modifier, subject);
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::Shadow {
            path: path("nat.x"),
        }]),
        "a collision inside `in nat` names the whole path, not the subtree-relative one"
    );
    assert_eq!(
        listing(&outcome),
        expected(&[entry("nat.a.x", Payload(1)), entry("nat.x", Payload(1))]),
        "and the union still merges inside the subtree it ran on"
    );
}

#[test]
fn a_nested_hook_reports_the_accumulated_prefix()
{
    let modifier = Modifier::in_subtree(path("nat"), Modifier::hook(HookLabel::KeepEverything));
    let (_outcome, events) = permissive(&modifier, arith());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::Hook {
            path: path("nat"),
            label: HookLabel::KeepEverything,
        }]),
        "a hook inside `in nat` is told the prefix it ran under"
    );
}

#[test]
fn a_hook_can_replace_the_namespace()
{
    let mut handler = RewritingHandler;
    let dropped = Modifier::hook(HookLabel::DropEverything)
        .apply(arith(), &mut handler)
        .expect("this policy accepts the label");
    assert_eq!(
        listing(&dropped),
        expected(&[]),
        "the handler's return value is the modifier's result"
    );

    let kept = Modifier::hook(HookLabel::KeepEverything)
        .apply(arith(), &mut handler)
        .expect("this policy accepts the label");
    assert_eq!(
        listing(&kept),
        listing(&arith()),
        "and a different label means something different, with no engine change"
    );
}

#[test]
fn rewriting_policy_continues_after_a_miss_and_keeps_the_later_collision()
{
    let subject = namespace(&[
        entry("left", Payload(9)),
        entry("left", Payload(1)),
        entry("right", Payload(2)),
    ]);
    let modifier = Modifier::union(vec![
        Modifier::only(path("missing")),
        Modifier::seq(vec![
            Modifier::only(path("right")),
            Modifier::relocation(path("right"), path("target")),
        ]),
        Modifier::seq(vec![
            Modifier::only(path("left")),
            Modifier::relocation(path("left"), path("target")),
        ]),
    ]);
    let result = modifier
        .apply(subject, &mut RewritingHandler)
        .expect("policy continues");
    assert_eq!(listing(&result), expected(&[entry("target", Payload(1))]));
}

#[test]
fn a_refused_nested_hook_preserves_the_namespace_transaction()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("left.a", Payload(1)), entry("right.b", Payload(2))]),
            &mut PermissiveHandler::<HookLabel>::new(),
        )
        .expect("fresh scope");
    let modifier = Modifier::in_subtree(
        path("left"),
        Modifier::seq(vec![
            Modifier::relocation(path("a"), path("moved")),
            Modifier::hook(HookLabel::KeepEverything),
        ]),
    );
    let refusal = scope
        .modify_visible(&modifier, &mut RejectingHandler)
        .expect_err("hook refuses");
    assert!(matches!(refusal, ScopeError::Rejected(ref rejection)
            if rejection.kind() == EventKind::Hook && rejection.path() == &path("left")));
    let original = expected(&[entry("left.a", Payload(1)), entry("right.b", Payload(2))]);
    assert_eq!(listing(scope.visible()), original);
    assert_eq!(listing(scope.export()), original);
}

// The `as name` clause, and the import lowering it drives.

#[test]
fn as_name_qualifies_every_imported_path()
{
    let imported = namespace(&[
        entry("lexer.token", Payload(1)),
        entry("parser", Payload(2)),
    ]);
    let (outcome, _events) = permissive(&Modifier::alias_as(Segment::from("parse")), imported);
    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("parse.lexer.token", Payload(1)),
            entry("parse.parser", Payload(2)),
        ]),
        "the import clause is the one-constructor case of the general language"
    );
}

#[test]
fn source_import_reaches_the_namespace_engine_and_exposes_its_alias()
{
    let pbg = grammar();
    let module = lowered(
        &pbg,
        &parsed(
            &pbg,
            SourceText::from(
                "import \"file:///lib/parse.gandr\" as parse ;\nimport \
                     \"file:///lib/list.gandr\" as list_ext ;",
            ),
        ),
    )
    .expect("import declarations lower");

    assert!(
        module.declarations().is_empty(),
        "an import is not a declaration"
    );
    assert_eq!(
        module
            .imports()
            .iter()
            .map(|import| (import.uri().as_ref(), import.binding()))
            .collect::<Vec<(&str, ImportBinding<'_>)>>(),
        Vec::from([
            (
                "file:///lib/parse.gandr",
                ImportBinding::Aliased(SurfaceName::from("parse"))
            ),
            (
                "file:///lib/list.gandr",
                ImportBinding::Aliased(SurfaceName::from("list_ext"))
            ),
        ]),
        "imports keep source order and their written operands"
    );
    let Maybe::Present(scope) = module.import_scope(SourceIndex::from(0_usize))
    else {
        panic!("the source binds two aliases");
    };
    assert_eq!(
        (
            scope.resolve(&path("parse")).map(|binding| binding.data),
            scope.resolve(&path("list_ext")).map(|binding| binding.data),
        ),
        (
            Maybe::Present(ImportIndex::from(0_usize)),
            Maybe::Present(ImportIndex::from(1_usize)),
        ),
        "each alias resolves to its import's source position"
    );
    assert_eq!(
        scope.export(),
        &Trie::empty(),
        "imports do not re-export their bindings"
    );
}

#[test]
fn an_import_binds_its_alias_and_resolves_no_address()
{
    let source = "import \"file:///no/such/\\\"place\\\".gandr\" as far ;\ndef x : Integer ; def \
                      x = 3 ;";
    let pbg = grammar();
    let module = lowered(&pbg, &parsed(&pbg, SourceText::from(source))).expect("the module lowers");
    let span = bytes(0_usize, 49_usize);

    assert_eq!(
        module.imports(),
        [ImportDeclaration::new(
            ImportUri::from(String::from("file:///no/such/\"place\".gandr")),
            ImportBinding::Aliased(SurfaceName::from("far")),
            span,
            SourceIndex::from(0_usize),
            ImportResolution::Foreign,
        )]
        .as_slice(),
        "a scheme address is kept with its escapes decoded and nothing resolved, so an \
             address naming nothing still lowers"
    );
    let Maybe::Present(scope) = module.import_scope(SourceIndex::from(0_usize))
    else {
        panic!("the source binds an alias");
    };
    assert_eq!(
        listing_of(scope.visible()),
        Vec::from([(String::from("far"), ImportIndex::from(0_usize), span)]),
        "the alias is the one binding, to the import's position, tagged with its bytes"
    );
    assert_eq!(
        module.declarations().len(),
        1_usize,
        "the declarations after an import are collected as before"
    );
}

/// The import namespace's dotted paths with their bindings.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every import binding is rendered in trie order with its exact
///   import index and source span.
/// - provides: a semantic import-namespace observer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source import retains its alias, index and span without
///   resolving or replacing its URI.
/// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
#[spec(
        ensures: |ret| {
            ret.len() == usize::from(subject.binding_count())
                && ret.iter().zip(subject.iter()).all(
                    |(&(ref rendered, index, span), (bound, binding))| {
                        index == binding.data && span == binding.tag && {
                            if bound.segments().is_empty() {
                                rendered == "."
                            }
                            else {
                                rendered
                                    .chars()
                                    .eq(bound.segments().iter().enumerate().flat_map(
                                        |(index, segment)| {
                                            (index != 0)
                                                .then_some('.')
                                                .into_iter()
                                                .chain(segment.as_ref().chars())
                                        },
                                    ))
                            }
                        }
                    },
                )
        },
    )]
fn listing_of(subject: &Trie<ImportIndex, ByteSpan>) -> Vec<(String, ImportIndex, ByteSpan)>
{
    subject
        .iter()
        .map(|(bound, binding)| (format!("{bound}"), binding.data, binding.tag))
        .collect()
}

#[test]
fn duplicate_source_import_alias_is_rejected_as_a_shadow()
{
    let first = bytes(0_usize, 43_usize);
    let second = bytes(44_usize, 86_usize);
    let source = SourceIndex::from(0_usize);
    let mut imports = ModuleImports::new();
    imports
        .bind(ImportDeclaration::new(
            ImportUri::from(String::from("file:///lib/parse.gandr")),
            ImportBinding::Aliased(SurfaceName::from("parse")),
            first,
            source,
            ImportResolution::Foreign,
        ))
        .expect("a fresh alias binds");
    let refused = imports
        .bind(ImportDeclaration::new(
            ImportUri::from(String::from("file:///lib/list.gandr")),
            ImportBinding::Aliased(SurfaceName::from("parse")),
            second,
            source,
            ImportResolution::Foreign,
        ))
        .expect_err("two imports must not silently shadow at one alias");

    assert_eq!(
        refused,
        LoweringRefusal::DuplicateImportAlias {
            span: second,
            alias: SurfaceName::from("parse"),
            first,
        },
        "the import policy's shadow rejection names both imports"
    );
    let Maybe::Present(scope) = imports.scope(source)
    else {
        panic!("the first alias stays bound");
    };
    assert_eq!(
        (
            imports.declarations().len(),
            scope.resolve(&path("parse")).map(|binding| binding.data),
        ),
        (1_usize, Maybe::Present(ImportIndex::from(0_usize))),
        "a refused import is not kept and leaves the first binding in place"
    );
}

#[test]
fn an_unqualified_import_binds_no_alias()
{
    let pbg = grammar();
    let module = lowered(
        &pbg,
        &parsed(&pbg, SourceText::from("import \"./parse.gandr\" ;")),
    )
    .expect("an import with no alias lowers");

    assert_eq!(
        module.imports(),
        [ImportDeclaration::new(
            ImportUri::from(String::from("./parse.gandr")),
            ImportBinding::Unqualified,
            bytes(0_usize, 24_usize),
            SourceIndex::from(0_usize),
            ImportResolution::Path(ImportTarget::Unresolved),
        )]
        .as_slice(),
        "a path read alone names no source of its unit"
    );
    assert!(
        matches!(
            module.import_scope(SourceIndex::from(0_usize)),
            Maybe::Absent(_)
        ),
        "an unqualified import binds no alias"
    );
}

/// An import whose parse is repaired inside a form it holds, here a
/// declaration left unended after its path, is refused by that form, as every
/// reader refuses a nested repair, whether its imports are read alone or
/// lowered.
#[test]
fn an_import_repaired_inside_a_nested_form_is_refused_by_that_form()
{
    let pbg = grammar();
    let tree = parsed(&pbg, SourceText::from("import \"./base.gandr\" def ;"));
    let refused = |refusal: LoweringRefusal<'_>| {
        matches!(
            refusal,
            LoweringRefusal::MalformedForm {
                span,
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(_),
            } if span == bytes(25_usize, 25_usize)
        )
    };
    assert!(
        gandr_surface_lowering::written_imports(&pbg, &tree).is_err_and(refused),
        "the imports read alone are refused by the unended declaration"
    );
    assert!(
        lowered(&pbg, &tree).is_err_and(refused),
        "and so is the lowering"
    );
}

#[test]
fn an_unqualified_import_answers_a_name_its_source_declares()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "data Point : Type { One : Point; }\ndef one : Point ;\ndef one = One ;",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef again : Point ;\ndef again = one ;\ndef \
                     made : Point ;\ndef made = One ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<String> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some(format!("{refusal:?}"))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refusals,
        Vec::<String>::new(),
        "the importer's type head, value and constructor resolve in the base"
    );
    assert_eq!(
        module.declarations().len(),
        4_usize,
        "the family, `one`, `again` and `made` are declared once each"
    );
}

#[test]
fn a_method_of_a_source_not_imported_is_out_of_scope()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "module Str { def len(self : shared Integer) -> -F Integer { pure self } }",
            ),
            &[],
        ),
        (
            SourceText::from(
                "module Bytes { def len(self : shared Integer) -> -F Integer { pure 0 } }",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./str.gandr\" ;\ndef measured() -> -F Integer { hold s = 1; s.len() }",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(
                "import \"./str.gandr\" ;\nimport \"./bytes.gandr\" ;\ndef both() -> -F Integer \
                 { hold s = 1; s.len() }",
            ),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let outcome = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(gandr_surface_lowering::LoweredDeclaration::outcome)
    };

    assert!(
        !matches!(outcome("measured"), Some(DeclarationOutcome::Refused(_))),
        "a source importing `Str` alone calls its `len`, though the unit recognises `Bytes`: \
         {:?}",
        outcome("measured")
    );
    assert!(
        matches!(
            outcome("both"),
            Some(DeclarationOutcome::Refused(LoweringRefusal::AmbiguousMethod { first, second, .. }))
                if first == SurfaceName::from("Str") && second == SurfaceName::from("Bytes")
        ),
        "a source importing both sees both: {:?}",
        outcome("both")
    );
}

#[test]
fn two_imports_binding_one_name_refuse_its_use()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("def one : Integer ;\ndef one = 1 ;"), &[]),
        (SourceText::from("def one : Integer ;\ndef one = 2 ;"), &[]),
        (
            SourceText::from(
                "import \"./left.gandr\" ;\nimport \"./right.gandr\" ;\ndef both : \
                     Integer ;\ndef both = one ;",
            ),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<String> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }) =
                declaration.outcome()
            {
                Some(String::from(name.as_ref()))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([String::from("one")]),
        "the use of a name two imports bind is refused, naming it"
    );
}

#[test]
fn a_model_of_an_imported_theory_derives_its_signature_726()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "theory Nat {\n  sort Nat : Type;\n  oper zero : () --> Nat;\n  oper succ : (n : \
                 Nat) --> Nat;\n}",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\nmodule Counting : Model(Nat) {\n  type Nat = \
                 Integer;\n  def zero() -> -F Integer { return 0 }\n  def succ(n : Integer) -> \
                 -F Integer { return n + 1 }\n}",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let declarations: Vec<(String, String)> = module
        .declarations()
        .iter()
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                format!("{:?}", declaration.outcome()),
            )
        })
        .collect();
    assert!(
        declarations
            .iter()
            .all(|&(_, ref outcome)| !outcome.starts_with("Refused")),
        "`Model(Nat)` reads the imported block as a local one: {declarations:?}"
    );
}

/// The include faults a lowering's descriptions report, in the order the
/// unit's sources write them.
///
/// # Specification
/// trivial.
fn include_faults(module: &LoweredModule<'_>) -> Vec<SignatureFault>
{
    module
        .descriptions()
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            if let DescriptionFault::Signature(
                ref
                fault @ (SignatureFault::UnknownInclude(_) | SignatureFault::AmbiguousInclude(_)),
            ) = diagnostic.fault
            {
                Some(fault.clone())
            }
            else {
                None
            }
        })
        .collect()
}

/// #1224: an `include` names a theory of its own source or of one its source
/// imports unqualified, in the whole unit's lowering and in a document's
/// resumed after its closure alike. A theory two imports present is refused
/// as ambiguous; one only an import's import presents, or an aliased import,
/// is not seen.
#[test]
fn an_include_reads_the_theories_its_source_imports_1224()
{
    let pbg = grammar();
    let magma =
        SourceText::from("theory Mag {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n}");
    let pointed = SourceText::from(
        "import \"./magma.gandr\" ;\ntheory Pointed {\n  include Mag;\n  oper one : () --> \
         M;\n}",
    );
    let mag = Name::from("Mag");
    let (text, unit) = laid(&[
        (magma, &[]),
        (pointed, &[ImportTarget::Source(SourceIndex::from(0_usize))]),
        (
            SourceText::from(
                "import \"./pointed.gandr\" ;\ntheory Through {\n  include Mag;\n  oper two : \
                 () --> M;\n}",
            ),
            &[ImportTarget::Source(SourceIndex::from(1_usize))],
        ),
        (
            SourceText::from(
                "import \"./magma.gandr\" as magma ;\ntheory Aliased {\n  include Mag;\n}",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(
                "theory Mag {\n  sort N : Type;\n  oper add : (x : N, y : N) --> N;\n}",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./magma.gandr\" ;\nimport \"./other.gandr\" ;\ntheory Both {\n  include \
                 Mag;\n}",
            ),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(4_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        include_faults(&module),
        Vec::from([
            SignatureFault::UnknownInclude(mag.clone()),
            SignatureFault::UnknownInclude(mag.clone()),
            SignatureFault::AmbiguousInclude(mag),
        ]),
        "`Pointed` reads its import's `Mag`; `Through` and `Aliased` see none, `Both` two"
    );

    let (text, unit) = laid(&[
        (magma, &[]),
        (pointed, &[ImportTarget::Source(SourceIndex::from(0_usize))]),
    ]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the magma").to_vec())
            .expect("the magma alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut arena = CoreArena::new();
    let resumed = closure
        .resume(&joined, &unit, &mut arena, &mut Decisions::none())
        .expect("the unit lowers resumed");
    assert_eq!(
        include_faults(&resumed),
        Vec::new(),
        "the resumed document reads its closure's `Mag`"
    );
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    assert_eq!(resumed, whole, "the module the whole unit lowers to");
}

/// #776: a unit is lowered a source at a time, so a source lowers to the same
/// declarations, ids included, and the same leading arena rows whether or not
/// an importer follows it. Lowered pass by pass over the whole unit, the
/// importer's types were minted among the base's.
#[test]
fn a_source_lowers_alike_whatever_follows_it_776()
{
    let pbg = grammar();
    let base = SourceText::from(
        "theory Nat {\n  sort Nat : Type;\n  oper zero : () --> Nat;\n  oper succ : (n : Nat) \
         --> Nat;\n}\ndata Point : Type { One : Point; }\ndef one : Point ;\ndef one = One \
         ;\ndef inc(n : Integer) -> -F Integer { return n + 1 }",
    );
    let importer = SourceText::from(
        "import \"./base.gandr\" ;\nmodule Counting : Model(Nat) {\n  type Nat = Integer;\n  \
         def zero() -> -F Integer { return 0 }\n  def succ(n : Integer) -> -F Integer { return \
         n + 1 }\n}\ndef again : Point ;\ndef again = one ;",
    );
    let (alone_text, alone_unit) = laid(&[(base, &[])]);
    let (whole_text, whole_unit) = laid(&[
        (base, &[]),
        (importer, &[ImportTarget::Source(SourceIndex::from(
            0_usize,
        ))]),
    ]);
    let mut alone_arena = CoreArena::new();
    let alone = lower_unit(
        &pbg,
        &parsed(&pbg, SourceText::from(alone_text.as_str())),
        &alone_unit,
        &mut alone_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the base alone lowers");
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &parsed(&pbg, SourceText::from(whole_text.as_str())),
        &whole_unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the base and its importer lower");
    let own = alone.declarations().len();
    assert!(
        whole.declarations().len() > own
            && whole.declarations().iter().all(|declaration| !matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(_)
            )),
        "the importer adds declarations of its own, and nothing is refused"
    );
    assert_eq!(
        whole.declarations().get(.. own),
        Some(alone.declarations()),
        "the base's declarations are the same, ids included, with the importer after it"
    );
    let start = CoreArena::new().watermark();
    assert!(
        alone_arena
            .values_since(start)
            .all(|id| whole_arena.value(id) == alone_arena.value(id))
            && alone_arena
                .computations_since(start)
                .all(|id| whole_arena.computation(id) == alone_arena.computation(id))
            && alone_arena
                .value_types_since(start)
                .all(|id| whole_arena.value_type(id) == alone_arena.value_type(id))
            && alone_arena
                .comp_types_since(start)
                .all(|id| whole_arena.comp_type(id) == alone_arena.comp_type(id)),
        "the base's arena rows lead the unit's arena"
    );
}

/// #1078: a `theory` block names the unit's one `Theory`, whatever the unit
/// lays before it. Alone, a source naming `Theory` and `Presents` mints the
/// code; behind a block it does not import, and behind one it imports, it takes
/// that block's code and every declaration of it stands. A source importing
/// both names the one code, with no ambiguity. The code a later source's block
/// took answered no name of that source.
#[test]
fn a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078()
{
    let pbg = grammar();
    let first =
        SourceText::from("theory Magma {\n  sort M : Type;\n  oper one : () --> (z : M);\n}");
    let counting = "theory Monoid {\n  sort M : Type;\n  oper one : () --> (z : M);\n}\ndef \
                    count(presented : Theory) -> -F Integer {\n  case presented {\n    \
                    Presents(sorts, opers, rules) => return 1,\n    _ => return 0\n  }\n}";
    let importing = format!("import \"./base.gandr\" ;\n{counting}");
    let both = SourceText::from(
        "import \"./base.gandr\" ;\nimport \"./counting.gandr\" ;\ndef pick(presented : Theory) \
         -> -F Theory {\n  return presented\n}",
    );
    let declared = |sources: &[(SourceText<'_>, &[ImportTarget])]| -> Vec<(String, bool)> {
        let (text, unit) = laid(sources);
        lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers")
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    String::from(declaration.name().as_ref()),
                    matches!(declaration.outcome(), DeclarationOutcome::Refused(_)),
                )
            })
            .collect()
    };
    let stood = |names: &[&str]| -> Vec<(String, bool)> {
        names
            .iter()
            .map(|&name| (String::from(name), false))
            .collect()
    };
    assert_eq!(
        declared(&[(SourceText::from(counting), &[])]),
        stood(&["Theory", "Monoid", "count"]),
        "alone, the block mints `Theory` and `count` reads it"
    );
    assert_eq!(
        declared(&[(first, &[]), (SourceText::from(counting), &[])]),
        stood(&["Theory", "Magma", "Monoid", "count"]),
        "behind a block it does not import, the source names that block's `Theory`"
    );
    assert_eq!(
        declared(&[
            (first, &[]),
            (SourceText::from(importing.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ])
        ]),
        stood(&["Theory", "Magma", "Monoid", "count"]),
        "behind a block it imports, the source names that block's `Theory`"
    );
    assert_eq!(
        declared(&[
            (first, &[]),
            (SourceText::from(counting), &[]),
            (both, &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ])
        ]),
        stood(&["Theory", "Magma", "Monoid", "count", "pick"]),
        "a source importing both blocks names one `Theory`"
    );
}

/// #1078: a univalence statement reads the `theory` blocks its own source
/// sees. Behind a source declaring `Monoid` that it does not import, `ua`
/// naming `Monoid` is refused as an unresolved name, as it is alone; through an
/// import of that source it reads the block. The statement read every block of
/// the unit by name.
#[test]
fn a_univalence_statement_reads_only_the_blocks_its_source_sees_1078()
{
    let pbg = grammar();
    let monoid = SourceText::from(
        "theory Monoid {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> (z : M);\n  oper one : \
         () --> (z : M);\n}",
    );
    let stating = "theory Magma {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> (z : M);\n  \
                   oper one : () --> (z : M);\n}\ndef exchange(b : Bool) -> -F Bool {\n  case b \
                   {\n    true => return +{.1 = unit},\n    false => return +{.0 = unit}\n  \
                   }\n}\ndef keep(e : +{Unit}) -> -F +{Unit} {\n  return e\n}\ndef unnamed = \
                   ua[1, 4](Monoid, Magma, #{mul = exchange, one = keep}, #{mul = exchange, one \
                   = keep}) ;";
    let importing = format!("import \"./base.gandr\" ;\n{stating}");
    // Whether `unnamed` is refused, and whether at `Monoid` as an unresolved
    // name.
    let unnamed = |sources: &[(SourceText<'_>, &[ImportTarget])]| -> (bool, bool) {
        let (text, unit) = laid(sources);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        let outcome = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == "unnamed")
            .expect("`unnamed` is declared")
            .outcome();
        (
            matches!(outcome, DeclarationOutcome::Refused(_)),
            matches!(
                outcome,
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                    if name.as_ref() == "Monoid"
            ),
        )
    };
    assert_eq!(
        unnamed(&[(SourceText::from(stating), &[])]),
        (true, true),
        "alone, `Monoid` names no block"
    );
    assert_eq!(
        unnamed(&[(monoid, &[]), (SourceText::from(stating), &[])]),
        (true, true),
        "behind a source it does not import, `Monoid` still names no block"
    );
    assert_eq!(
        unnamed(&[
            (monoid, &[]),
            (SourceText::from(importing.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize),)
            ]),
        ]),
        (false, false),
        "through an import, `Monoid` reads the imported block"
    );
}

/// #1033: a document parsed alone, laid after its closure's tree and resumed
/// on the closure's lowering lowers as the whole unit does over that tree, the
/// module and the arena alike, each time it is resumed, the closure's hole and
/// the document's numbered as the whole unit numbers them; its declarations
/// and arena are the ones the whole text's parse lowers to. A tree that does
/// not extend the closure's is lowered whole, and a document that refuses the
/// unit answers the whole lowering's refusal.
#[test]
fn a_document_resumed_after_its_closure_lowers_as_the_whole_1033()
{
    let pbg = grammar();
    let base = SourceText::from(
        "theory Nat {\n  sort Nat : Type;\n  oper zero : () --> Nat;\n  oper succ : (n : Nat) \
         --> Nat;\n}\ndata Point : Type { One : Point; }\ndef one : Point ;\ndef one = One \
         ;\ndef pending = ? ;\ndef inc(n : Integer) -> -F Integer { return n + 1 }",
    );
    let importer = SourceText::from(
        "import \"./base.gandr\" ;\nmodule Counting : Model(Nat) {\n  type Nat = Integer;\n  \
         def zero() -> -F Integer { return 0 }\n  def succ(n : Integer) -> -F Integer { return \
         n + 1 }\n}\ndef again : Point ;\ndef again = one ;\ndef later = ?named ;",
    );
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (importer, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    assert!(
        whole
            .declarations()
            .iter()
            .all(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))),
        "nothing is refused"
    );
    for _ in 0_usize .. 2_usize {
        let mut arena = CoreArena::new();
        let resumed = closure
            .resume(&joined, &unit, &mut arena, &mut Decisions::none())
            .expect("the unit lowers resumed");
        assert_eq!(resumed, whole, "the module the whole unit lowers to");
        assert_eq!(arena, whole_arena, "the arena the whole unit mints");
    }
    let tree = parsed(&pbg, SourceText::from(text.as_str()));
    let mut text_arena = CoreArena::new();
    let from_text = lower_unit(
        &pbg,
        &tree,
        &unit,
        &mut text_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the whole text lowers");
    assert_eq!(
        from_text.declarations(),
        whole.declarations(),
        "the whole text's declarations"
    );
    assert_eq!(text_arena, whole_arena, "the whole text's arena");
    let mut fallback_arena = CoreArena::new();
    assert_eq!(
        closure.resume(&tree, &unit, &mut fallback_arena, &mut Decisions::none()),
        Ok(from_text),
        "a tree that does not extend the closure's is lowered whole"
    );
    assert_eq!(fallback_arena, text_arena);
    let refusing = SourceText::from(
        "import \"./base.gandr\" as B ;\nimport \"./base.gandr\" as B ;\ndef c = ? ;",
    );
    let twice = [
        ImportTarget::Source(SourceIndex::from(0_usize)),
        ImportTarget::Source(SourceIndex::from(0_usize)),
    ];
    let (refused_text, refused_unit) = laid(&[(base, &[]), (refusing, &twice)]);
    let refused = parse(&pbg, refusing)
        .expect("the document parses")
        .after(closure.tree(), SourceText::from(refused_text.as_str()))
        .expect("the document lays after its closure")
        .into_tree();
    let expected = lower_unit(
        &pbg,
        &refused,
        &refused_unit,
        &mut CoreArena::new(),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    );
    assert!(
        expected.is_err(),
        "two imports of one alias refuse the unit"
    );
    assert_eq!(
        closure.resume(
            &refused,
            &refused_unit,
            &mut CoreArena::new(),
            &mut Decisions::none()
        ),
        expected
    );
}

/// #776: a closure's own module is the leading declarations its importer
/// lowers to, ids included. Onto the closure's own arena the document lowers
/// exactly as the whole unit does; onto that arena with more nodes minted after
/// it — what a checker judging the closure leaves — the closure's declarations
/// and rows stand unchanged, and the document declares what the whole unit
/// declares, minting as many nodes, after the added ones. A tree that does not
/// extend the closure's is left to the whole lowering, the arena untouched.
#[test]
fn a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776()
{
    /// Each declaration's name and the kind of its outcome.
    ///
    /// # Specification
    /// trivial.
    fn shape<'source>(
        module: &LoweredModule<'source>
    ) -> Vec<(String, core::mem::Discriminant<DeclarationOutcome<'source>>)>
    {
        module
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    String::from(declaration.name().as_ref()),
                    core::mem::discriminant(&declaration.outcome()),
                )
            })
            .collect()
    }
    let pbg = grammar();
    let base = SourceText::from(
        "data Point : Type { One : Point; }\ndef one : Point ;\ndef one = One ;\ndef pending = ? \
         ;",
    );
    let importer = SourceText::from(
        "import \"./base.gandr\" ;\ndef again : Point ;\ndef again = one ;\ndef later = ?named ;",
    );
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (importer, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    let (alone, alone_arena) = closure.alone().expect("the closure lowers to its end");
    let leading = alone.declarations().len();
    assert_eq!(
        Some(alone.declarations()),
        whole.declarations().get(.. leading),
        "the closure's own declarations lead the importer's"
    );
    let mut onto = alone_arena.clone();
    let uncarried = closure.carrying(&[], &[]);
    let Ok(Onto::Resumed(resumed)) = closure.resume_onto(
        &joined,
        &unit,
        &mut onto,
        &uncarried,
        &mut Decisions::none(),
    )
    else {
        panic!("the document resumes onto its closure's arena");
    };
    assert_eq!(
        resumed, whole,
        "onto the closure's own arena, the whole module"
    );
    assert_eq!(onto, whole_arena, "and the whole arena");
    let source = alone
        .declarations()
        .iter()
        .find_map(|declaration| {
            if let DeclarationOutcome::Completed { body, .. } = declaration.outcome() {
                Some(body)
            }
            else {
                None
            }
        })
        .expect("`one` is completed");
    let Maybe::Present(written) = alone.origins().value(source)
    else {
        panic!("`one`'s body is located");
    };
    let mut checked = alone_arena.clone();
    let elaborated = checked.value_unit();
    let _type = checked.value_type_unit();
    let added = checked.watermark();
    assert_ne!(added, alone_arena.watermark(), "nodes follow the closure's");
    let Ok(Onto::Resumed(after)) = closure.resume_onto(
        &joined,
        &unit,
        &mut checked,
        &closure.carrying(&[Carried::Value(source, elaborated)], &[]),
        &mut Decisions::none(),
    )
    else {
        panic!("the document resumes onto the checked arena");
    };
    assert_eq!(
        after.origins().value(elaborated),
        Maybe::Present(written),
        "a node minted after the closure's is located where its source is written"
    );
    let bodies = |module: &LoweredModule<'_>| {
        module
            .declarations()
            .get(leading ..)
            .unwrap_or_default()
            .iter()
            .filter_map(|declaration| match declaration.outcome() {
                DeclarationOutcome::Completed { body, .. }
                | DeclarationOutcome::Bodied { body } => Some(module.origins().value(body)),
                DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        bodies(&after),
        bodies(&whole),
        "and the document's bodies where the whole lowering locates them"
    );
    assert_eq!(
        after.declarations().get(.. leading),
        Some(alone.declarations()),
        "the closure's declarations stand"
    );
    assert_eq!(
        shape(&after),
        shape(&whole),
        "the whole unit's declarations"
    );
    let mark = alone_arena.watermark();
    assert_eq!(
        (
            checked.values_since(added).len(),
            checked.computations_since(added).len(),
            checked.value_types_since(added).len(),
            checked.comp_types_since(added).len(),
        ),
        (
            whole_arena.values_since(mark).len(),
            whole_arena.computations_since(mark).len(),
            whole_arena.value_types_since(mark).len(),
            whole_arena.comp_types_since(mark).len(),
        ),
        "the document mints as many nodes, after the added ones"
    );
    let tree = parsed(&pbg, SourceText::from(text.as_str()));
    let mut untouched = alone_arena.clone();
    assert!(
        matches!(
            closure.resume_onto(
                &tree,
                &unit,
                &mut untouched,
                &uncarried,
                &mut Decisions::none()
            ),
            Ok(Onto::Whole)
        ),
        "a tree that does not extend the closure's is left to the whole lowering"
    );
    assert_eq!(untouched, alone_arena, "its arena untouched");
}

#[test]
fn a_pending_declaration_is_not_exported()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("def owed : Integer ;"), &[]),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef again : Integer ;\ndef again = owed ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnexportedName { name, .. })
                if name.as_ref() == "owed"
        )),
        "a signature without a definition is not exported, and its use refuses by name"
    );
}

#[test]
fn an_aliased_import_qualifies_its_source_s_names()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "data Point : Type { One : Point; }\ndef one : Point ;\ndef one = One ;",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" as base ;\ndef again : base.Point ;\ndef again = \
                     base.one ;\ndef lost : Integer ;\ndef lost = base.two ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some((
                    String::from(declaration.name().as_ref()),
                    format!("{refusal:?}"),
                ))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(refusals.len(), 1_usize, "only `lost` refuses: {refusals:?}");
    assert!(
        refusals
            .iter()
            .any(|&(ref name, ref refusal)| name == "lost"
                && refusal.starts_with("UnknownMember")
                && refusal.contains("\"two\"")),
        "a name the imported source does not declare is refused by name: {refusals:?}"
    );
}

#[test]
fn a_pending_member_read_through_an_alias_is_refused_at_the_member()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("def owed : Integer ;"), &[]),
        (
            SourceText::from(
                "import \"./base.gandr\" as base ;\ndef again : Integer ;\ndef again = \
                     base.owed ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let member = text.find("base.owed").expect("the path is written") + "base.".len();

    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnexportedName { span, name, .. })
                if name.as_ref() == "owed" && span == bytes(member, member + "owed".len())
        )),
        "the refusal stands at the selected name, not the whole path"
    );
}

#[test]
fn an_unresolved_import_refuses_its_source()
{
    let pbg = grammar();
    let (text, unit) = laid(&[(
        SourceText::from("import \"./nowhere.gandr\" ;\ndef one : Integer ;\ndef one = 1 ;"),
        &[ImportTarget::Unresolved],
    )]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        matches!(
            module.declarations(),
            [declaration] if matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::ImportUnresolved { span, .. })
                    if span == bytes(0_usize, 26_usize)
            )
        ),
        "every declaration of the source is refused, naming the import"
    );
}

#[test]
fn an_import_closing_a_cycle_refuses_its_source()
{
    let pbg = grammar();
    let (text, unit) = laid(&[(
        SourceText::from("import \"./self.gandr\" ;\ndef one : Integer ;\ndef one = 1 ;"),
        &[ImportTarget::Cycle],
    )]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        matches!(
            module.declarations(),
            [declaration] if matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::ImportCycle { span, .. })
                    if span == bytes(0_usize, 23_usize)
            )
        ),
        "every declaration of the source is refused, naming the import on the cycle"
    );
}

#[test]
fn a_constructor_an_import_binds_again_refuses_its_family()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from("data Bit : Type { O : Bit; I : Bit; }"),
            &[],
        ),
        (
            SourceText::from("import \"./base.gandr\" ;\ndata Other : Type { O : Other; }"),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }) =
                declaration.outcome()
            {
                Some((
                    String::from(declaration.name().as_ref()),
                    String::from(name.as_ref()),
                ))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([(String::from("Other"), String::from("O"))]),
        "the importer's family is refused at its constructor `O`, which the base binds"
    );
}

#[test]
fn a_declaration_an_import_binds_again_is_refused()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("def one : Integer ;\ndef one = 1 ;"), &[]),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef one : Integer ;\ndef one = 2 ;\ndef two : \
                     Integer ;\ndef two = 2 ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<(String, ByteSpan)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { other, .. }) =
                declaration.outcome()
            {
                Some((String::from(declaration.name().as_ref()), other))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([(String::from("one"), bytes(4_usize, 7_usize))]),
        "the importer's `one` is refused, naming the base's; `two` stands"
    );
}

/// #596: one attributed form written byte for byte in two sources of a
/// unit — its documentation apart, which no key reads — is keyed apart by
/// its source, so each declaration reads its own attribute and its own
/// documentation.
#[test]
fn one_form_in_two_sources_files_its_attributes_apart_596()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("def zero : Integer ;\ndef zero = 0 ;"), &[
        ]),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\n/// The left two.\n@[ checks ]\ndef two : \
                     Integer ;\ndef two = 2 ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\n/// The right two.\n@[ checks ]\ndef two : \
                     Integer ;\ndef two = 2 ;",
            ),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let keys: Vec<_> = module
        .declarations()
        .iter()
        .filter(|declaration| declaration.name().as_ref() == "two")
        .filter_map(|declaration| match declaration.signature() {
            Maybe::Present(key) => Some(key),
            Maybe::Absent(_) => None,
        })
        .collect();
    let &[left, right] = keys.as_slice()
    else {
        panic!("each source declares its own `two`: {keys:?}");
    };
    assert_eq!(
        left.form(),
        right.form(),
        "the two forms are one form byte for byte"
    );
    assert_eq!(
        (left.source(), right.source()),
        (SourceIndex::from(1_usize), SourceIndex::from(2_usize)),
        "each key names the source holding its form"
    );
    for key in [left, right] {
        assert_eq!(
            module.attributes().entries(key).len(),
            1_usize,
            "each declaration reads its own `checks` alone"
        );
    }
    let documented = |key| match module.documentation(key) {
        Maybe::Present(documentation) => format!("{documentation:?}"),
        Maybe::Absent(_) => String::new(),
    };
    assert!(
        documented(left).contains("The left two.") && documented(right).contains("The right two."),
        "each declaration keeps its own documentation"
    );
}

/// The unit text of `sources` laid end to end, one newline apart, and the
/// unit that says where each starts and what its path imports name.
///
/// # Specification
/// - requires: each source imports only earlier ones.
/// - ensures: each source starts one byte after the one before it ends.
/// - provides: a several-source fixture.
/// - fails: never.
/// - panics: when a source imports a later one.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses resolve across the sources it lays.
/// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
#[spec(
        ensures: |ret| ret.1.sources().len() == sources.len()
            && sources.iter().all(|&(source, _)| ret.0.contains(<&str>::from(source))),
    )]
fn laid(sources: &[(SourceText<'_>, &[ImportTarget])]) -> (String, Unit)
{
    let mut text = String::new();
    let mut laid = Vec::with_capacity(sources.len());
    for &(source, imports) in sources {
        if !text.is_empty() {
            text.push('\n');
        }
        laid.push(UnitSource::new(
            ByteOffset::from(text.len()),
            imports.to_vec(),
        ));
        text.push_str(<&str>::from(source));
    }
    let unit = Unit::new(laid).expect("each source imports an earlier one");
    (text, unit)
}

/// `tree`, molded over the text `unit` lays out, lowered under `pbg`.
///
/// # Specification
/// - requires: `tree` was parsed from the text [`laid`] made with `unit`.
/// - ensures: as [`lowered`], over the unit.
/// - provides: the several-source lowering fixture.
/// - fails: preserves the lowering's refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses of [`laid`].
/// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
#[spec(
        ensures: |ret| matches!(ret, Err(LoweringRefusal::GrammarMismatch { .. })) == (tree.grammar() != pbg.fingerprint()),
    )]
fn lowered_unit<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    let mut arena = CoreArena::new();
    lower_unit(
        pbg,
        tree,
        unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
}

#[test]
fn duplicate_source_import_alias_becomes_a_refusal()
{
    let pbg = grammar();
    let refused = lowered(
        &pbg,
        &parsed(
            &pbg,
            SourceText::from(
                "import \"file:///lib/parse.gandr\" as parse ;\nimport \
                     \"file:///lib/list.gandr\" as parse ;",
            ),
        ),
    )
    .expect_err("two imports of one alias refuse the module");
    assert_eq!(
        refused,
        LoweringRefusal::DuplicateImportAlias {
            span: bytes(44_usize, 86_usize),
            alias: SurfaceName::from("parse"),
            first: bytes(0_usize, 43_usize),
        },
        "the second import is refused, naming the first"
    );
}

#[test]
fn as_name_on_an_empty_import_performs_not_found()
{
    let (outcome, events) = permissive(&Modifier::alias_as(Segment::from("parse")), Trie::empty());
    assert_eq!(
        events,
        Vec::from([NamespaceEvent::NotFound {
            path: NamePath::root(),
        }]),
        "the desugaring inherits the checked builder's typo resistance: aliasing an empty \
             import is reported at the root"
    );
    assert_eq!(
        listing(&outcome),
        expected(&[]),
        "and qualifying nothing yields nothing"
    );
}

// The visible/export split.

#[test]
fn include_touches_both_namespaces()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides in an empty scope");
    assert_eq!(
        listing(scope.visible()),
        listing(&arith()),
        "an include is usable here"
    );
    assert_eq!(
        listing(scope.export()),
        listing(&arith()),
        "and visible to importers"
    );
}

#[test]
fn import_touches_only_the_visible_namespace()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .import_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides in an empty scope");
    assert_eq!(
        listing(scope.visible()),
        listing(&arith()),
        "an import is usable here"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[]),
        "and is not a re-export"
    );
}

#[test]
fn an_import_arrives_under_its_prefix()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .import_subtree(
            &path("lib"),
            namespace(&[entry("parse.token", Payload(1))]),
            &mut handler,
        )
        .expect("nothing collides in an empty scope");
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("lib.parse.token", Payload(1))]),
        "an import is merged under the prefix it was handed, not at the root"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[]),
        "and prefixing it still does not make it a re-export"
    );
}

#[test]
fn a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was()
{
    let mut scope: Scope<Payload, ()> =
        Scope::with_init_visible(namespace(&[entry("taken", Payload(1))]));
    let before = scope.visible().clone();
    let imported = namespace(&[entry("available", Payload(2)), entry("taken", Payload(3))]);
    let mut handler = RejectingHandler;

    let failure = scope
        .import_subtree(&NamePath::root(), imported, &mut handler)
        .expect_err("the existing `taken` binding must be refused");
    assert_eq!(
        failure,
        ScopeError::Rejected(EventRejection::new(
            EventKind::Shadow,
            path("taken"),
            RejectionReason::from("this policy forbids shadowing"),
        )),
        "the collision reaches the caller as the handler's structured rejection"
    );
    assert_eq!(
        scope.visible(),
        &before,
        "the earlier `available` insertion rolls back with the later collision"
    );
}

#[test]
fn a_refused_modifier_leaves_the_visible_namespace_as_it_was()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut permissive_handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut permissive_handler)
        .expect("nothing collides in an empty scope");
    let mut handler = RejectingHandler;
    let failure = scope
        .modify_visible(&Modifier::only(path("nta")), &mut handler)
        .expect_err("this policy treats a typo as fatal");
    assert_eq!(
        failure,
        ScopeError::Rejected(EventRejection::new(
            EventKind::NotFound,
            path("nta"),
            RejectionReason::from("nothing matched here; check for a typo"),
        )),
        "the policy's refusal reaches the caller whole"
    );
    assert_eq!(
        listing(scope.visible()),
        listing(&arith()),
        "the rewrite lands only once the modifier has succeeded"
    );
    assert_eq!(
        listing(scope.export()),
        listing(&arith()),
        "with the namespace it never touches untouched throughout"
    );
}

#[test]
fn a_refused_modifier_leaves_the_export_namespace_as_it_was()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut permissive_handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut permissive_handler)
        .expect("nothing collides in an empty scope");
    let mut handler = RejectingHandler;
    let failure = scope
        .modify_export(&Modifier::only(path("nta")), &mut handler)
        .expect_err("this policy treats a typo as fatal");
    assert_eq!(
        failure,
        ScopeError::Rejected(EventRejection::new(
            EventKind::NotFound,
            path("nta"),
            RejectionReason::from("nothing matched here; check for a typo"),
        )),
        "the same refusal, on the other namespace"
    );
    assert_eq!(
        listing(scope.export()),
        listing(&arith()),
        "and the export namespace is exactly as it was"
    );
    assert_eq!(
        listing(scope.visible()),
        listing(&arith()),
        "with the visible namespace untouched throughout"
    );
}

#[test]
fn a_refused_re_export_leaves_the_prior_export_as_it_was()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut permissive_handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("already.exported", Payload(4))]),
            &mut permissive_handler,
        )
        .expect("nothing collides in an empty scope");
    let mut handler = RejectingHandler;
    let failure = scope
        .export_visible(&Modifier::only(path("nta")), &mut handler)
        .expect_err("this policy treats a typo as fatal");
    assert_eq!(
        failure,
        ScopeError::Rejected(EventRejection::new(
            EventKind::NotFound,
            path("nta"),
            RejectionReason::from("nothing matched here; check for a typo"),
        )),
        "the selection is refused before anything is passed on"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("already.exported", Payload(4))]),
        "a refused selection re-exports nothing and takes nothing away"
    );
}

#[test]
fn modifying_visible_leaves_export_alone()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides in an empty scope");
    scope
        .modify_visible(&Modifier::only(path("nat")), &mut handler)
        .expect("the subtree exists");
    assert_eq!(
        listing(scope.visible()),
        expected(&[
            entry("nat.plus.assoc", Payload(1)),
            entry("nat.times.assoc", Payload(2)),
        ]),
        "the visible namespace was narrowed"
    );
    assert_eq!(
        listing(scope.export()),
        listing(&arith()),
        "the export namespace was not"
    );
}

#[test]
fn modifying_export_leaves_visible_alone()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides in an empty scope");
    scope
        .import_subtree(
            &NamePath::root(),
            namespace(&[entry("borrowed", Payload(5))]),
            &mut handler,
        )
        .expect("nothing collides with the included namespace");
    scope
        .modify_export(&Modifier::except(path("nat")), &mut handler)
        .expect("the subtree exists");
    assert_eq!(
        listing(scope.visible()),
        expected(&[
            entry("borrowed", Payload(5)),
            entry("int.plus.assoc", Payload(3)),
            entry("nat.plus.assoc", Payload(1)),
            entry("nat.times.assoc", Payload(2)),
        ]),
        "the visible namespace was not narrowed"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("int.plus.assoc", Payload(3))]),
        "the export namespace was, and the modifier read the export namespace: the imported \
             binding never reached it"
    );
}

#[test]
fn export_visible_re_exports_a_selection()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("already.exported", Payload(4))]),
            &mut handler,
        )
        .expect("nothing collides in an empty scope");
    scope
        .import_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides with the included namespace");
    scope
        .export_visible(&Modifier::only(path("nat")), &mut handler)
        .expect("the subtree exists");
    assert_eq!(
        listing(scope.visible()),
        expected(&[
            entry("already.exported", Payload(4)),
            entry("int.plus.assoc", Payload(3)),
            entry("nat.plus.assoc", Payload(1)),
            entry("nat.times.assoc", Payload(2)),
        ]),
        "re-exporting does not narrow what resolves here"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[
            entry("already.exported", Payload(4)),
            entry("nat.plus.assoc", Payload(1)),
            entry("nat.times.assoc", Payload(2)),
        ]),
        "the selection is merged into what the unit already exported rather than replacing it"
    );
}

#[test]
fn include_merges_the_visible_namespace_before_the_export()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut permissive_handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("m.b", Payload(1))]),
            &mut permissive_handler,
        )
        .expect("nothing collides in an empty scope");
    let mut handler = RejectingHandler;
    let outcome = scope.include_subtree(
        &NamePath::root(),
        namespace(&[entry("m.a", Payload(2)), entry("m.b", Payload(3))]),
        &mut handler,
    );
    let ScopeError::Rejected(rejection) = outcome.expect_err("the collision at `m.b` is refused")
    else {
        panic!("the failure is an event rejection, not a structural one");
    };
    assert_eq!(
        (rejection.kind(), rejection.path().clone()),
        (EventKind::Shadow, path("m.b")),
        "and it is the collision, at the colliding path"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("m.b", Payload(1))]),
        "the visible merge runs first, so a rejection there leaves the export untouched"
    );
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("m.a", Payload(2)), entry("m.b", Payload(1))]),
        "and the visible namespace keeps the bindings merged before the refused one: an \
             include is not atomic"
    );
}

#[test]
fn a_refused_closing_modifier_restores_the_parent_and_closes_the_section()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut allowing = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("parent", Payload(7))]),
            &mut allowing,
        )
        .expect("the parent starts empty");
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("child", Payload(9))]),
            &mut allowing,
        )
        .expect("the child name is fresh");
    let mut rejecting = RejectingHandler;
    let error = scope
        .end_section(
            &path("group"),
            &Modifier::only(path("missing")),
            &mut rejecting,
        )
        .expect_err("the closing modifier selects no export");
    let ScopeError::Rejected(rejection) = error
    else {
        panic!("the close failed in the modifier");
    };
    assert_eq!(rejection.kind(), EventKind::NotFound);
    assert_eq!(rejection.path(), &path("missing"));
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("parent", Payload(7))])
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("parent", Payload(7))])
    );
    assert_eq!(
        scope.end_section(&NamePath::root(), &Modifier::id(), &mut rejecting),
        Err(ScopeError::NoOpenSection)
    );
}

#[test]
fn a_refused_closing_merge_keeps_its_prefix_and_closes_the_section()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut allowing = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("pkg.z", Payload(1))]),
            &mut allowing,
        )
        .expect("the parent starts empty");
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("a", Payload(2)), entry("z", Payload(3))]),
            &mut allowing,
        )
        .expect("the child's root names are fresh");
    let mut rejecting = RejectingHandler;
    let error = scope
        .end_section(&path("pkg"), &Modifier::id(), &mut rejecting)
        .expect_err("the last prefixed binding collides");
    let ScopeError::Rejected(rejection) = error
    else {
        panic!("the close failed in the merge");
    };
    assert_eq!(rejection.kind(), EventKind::Shadow);
    assert_eq!(rejection.path(), &path("pkg.z"));
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("pkg.a", Payload(2)), entry("pkg.z", Payload(1))])
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("pkg.z", Payload(1))])
    );
    assert_eq!(
        scope.end_section(&NamePath::root(), &Modifier::id(), &mut rejecting),
        Err(ScopeError::NoOpenSection)
    );
}
#[test]
fn a_section_inherits_the_visible_namespace_and_exports_nothing_yet()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides in an empty scope");
    scope.begin_section();
    assert_eq!(
        listing(scope.visible()),
        listing(&arith()),
        "the section can see what surrounds it"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[]),
        "and starts with nothing of its own to export, however much the parent exported"
    );
}

#[test]
fn a_sections_closing_modifier_chooses_what_it_passes_on()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[
                entry("public", Payload(1)),
                entry("scaffolding", Payload(2)),
            ]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    scope
        .end_section(
            &path("group"),
            &Modifier::only(path("public")),
            &mut handler,
        )
        .expect("a section is open and the selection matched");
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("group.public", Payload(1))]),
        "the closing modifier runs over the section's export before the prefixed include"
    );
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("group.public", Payload(1))]),
        "and the same selection is what the parent can see"
    );
}

#[test]
fn a_section_exports_under_its_prefix()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("lemma", Payload(1))]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    scope
        .end_section(&path("group"), &Modifier::id(), &mut handler)
        .expect("a section is open");
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("group.lemma", Payload(1))]),
        "the section's export arrives under the section's prefix"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[entry("group.lemma", Payload(1))]),
        "and is itself re-exported, because closing a section is an include"
    );
}

#[test]
fn a_sections_imports_evaporate_at_close()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope.begin_section();
    scope
        .import_subtree(&NamePath::root(), arith(), &mut handler)
        .expect("nothing collides inside a fresh section");
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("lemma", Payload(1))]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    assert_eq!(
        listing(scope.visible()).len(),
        4_usize,
        "inside the section the import resolves alongside the definition"
    );
    scope
        .end_section(&path("group"), &Modifier::id(), &mut handler)
        .expect("a section is open");
    assert_eq!(
        listing(scope.visible()),
        expected(&[entry("group.lemma", Payload(1))]),
        "only what the section exported survives; its imports evaporate"
    );
}

#[test]
fn closing_without_an_open_section_fails()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    let outcome = scope.end_section(&path("group"), &Modifier::id(), &mut handler);
    assert_eq!(
        outcome,
        Err(ScopeError::NoOpenSection),
        "closing a section that was never opened is a structured failure, not a panic"
    );
}

#[test]
fn closing_a_section_restores_what_the_parent_already_held()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("outer_lemma", Payload(1))]),
            &mut handler,
        )
        .expect("nothing collides in an empty scope");
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("inner_lemma", Payload(2))]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    scope
        .end_section(&path("group"), &Modifier::id(), &mut handler)
        .expect("a section is open");
    assert_eq!(
        listing(scope.visible()),
        expected(&[
            entry("group.inner_lemma", Payload(2)),
            entry("outer_lemma", Payload(1)),
        ]),
        "everything the enclosing scope held before the section is still there"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[
            entry("group.inner_lemma", Payload(2)),
            entry("outer_lemma", Payload(1)),
        ]),
        "in both namespaces, because closing restores the enclosing scope"
    );
}

#[test]
fn nested_sections_close_innermost_first()
{
    let mut scope: Scope<Payload, ()> = Scope::new();
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("outer_lemma", Payload(1))]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    scope.begin_section();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("inner_lemma", Payload(2))]),
            &mut handler,
        )
        .expect("nothing collides inside a fresh section");
    scope
        .end_section(&path("inner"), &Modifier::id(), &mut handler)
        .expect("the inner section is open");
    assert_eq!(
        listing(scope.export()),
        expected(&[
            entry("inner.inner_lemma", Payload(2)),
            entry("outer_lemma", Payload(1)),
        ]),
        "closing the inner section returns into the enclosing section: the enclosing \
             scopes are a stack"
    );
    scope
        .end_section(&path("outer"), &Modifier::id(), &mut handler)
        .expect("the outer section is open");
    assert_eq!(
        listing(scope.export()),
        expected(&[
            entry("outer.inner.inner_lemma", Payload(2)),
            entry("outer.outer_lemma", Payload(1)),
        ]),
        "and closing the outer one prefixes both again, so section prefixes nest"
    );
}

// The handler seam.

#[test]
fn the_permissive_handler_records_all_three_events()
{
    let subject = namespace(&[entry("a.x", Payload(1)), entry("x", Payload(2))]);
    let modifier = Modifier::seq(Vec::from([
        Modifier::in_subtree(path("gone"), Modifier::all()),
        Modifier::union(Vec::from([
            Modifier::id(),
            Modifier::renaming(path("a"), NamePath::root()),
        ])),
        Modifier::hook(HookLabel::KeepEverything),
    ]));
    let (outcome, events) = permissive(&modifier, subject);
    assert_eq!(
        events,
        Vec::from([
            NamespaceEvent::NotFound { path: path("gone") },
            NamespaceEvent::Shadow { path: path("x") },
            NamespaceEvent::Hook {
                path: NamePath::root(),
                label: HookLabel::KeepEverything,
            },
        ]),
        "all three events reach the handler, in the order the run performs them"
    );
    assert_eq!(
        listing(&outcome),
        expected(&[entry("a.x", Payload(1)), entry("x", Payload(1))]),
        "and the warn-and-allow policy lets the run finish, later shadowing earlier"
    );
}

#[test]
fn a_rejecting_handler_refuses_a_missing_selection()
{
    let mut handler = RejectingHandler;
    let rejection = Modifier::only(path("nta"))
        .apply(arith(), &mut handler)
        .expect_err("this policy treats a typo as fatal");
    assert_eq!(
        rejection.kind(),
        EventKind::NotFound,
        "the rejection names the event it refused"
    );
    assert_eq!(
        *rejection.path(),
        path("nta"),
        "and the path the user wrote"
    );
}

#[test]
fn a_rejecting_handler_refuses_a_shadow()
{
    let subject = namespace(&[entry("a.x", Payload(1)), entry("x", Payload(2))]);
    let modifier = Modifier::union(Vec::from([
        Modifier::id(),
        Modifier::renaming(path("a"), NamePath::root()),
    ]));
    let mut handler = RejectingHandler;
    let rejection = modifier
        .apply(subject, &mut handler)
        .expect_err("this policy forbids shadowing");
    assert_eq!(
        rejection.kind(),
        EventKind::Shadow,
        "the rejection names the event it refused"
    );
    assert_eq!(
        *rejection.path(),
        path("x"),
        "and the colliding path, as a whole path"
    );
}

#[test]
fn a_rejecting_handler_refuses_a_hook()
{
    let mut handler = RejectingHandler;
    let rejection = Modifier::hook(HookLabel::KeepEverything)
        .apply(arith(), &mut handler)
        .expect_err("this policy recognizes no hooks");
    assert_eq!(
        rejection.kind(),
        EventKind::Hook,
        "the rejection names the event it refused"
    );
    assert_eq!(
        *rejection.path(),
        NamePath::root(),
        "at the prefix the hook ran under"
    );
}

#[test]
fn clearing_a_permissive_handler_forgets_what_it_recorded()
{
    let mut handler = PermissiveHandler::<HookLabel>::new();
    let first = Modifier::<HookLabel>::all()
        .apply(Trie::<Payload, ()>::empty(), &mut handler)
        .expect("the permissive policy rejects nothing");
    assert_eq!(
        listing(&first),
        expected(&[]),
        "the emptiness check transforms nothing"
    );
    assert_eq!(
        handler.events(),
        [NamespaceEvent::NotFound {
            path: NamePath::root(),
        }]
        .as_slice(),
        "and it was recorded"
    );

    handler.clear();
    assert!(
        handler.events().is_empty(),
        "clearing forgets every recorded event"
    );

    let second = Modifier::<HookLabel>::all()
        .apply(Trie::<Payload, ()>::empty(), &mut handler)
        .expect("the permissive policy rejects nothing");
    assert_eq!(
        listing(&second),
        expected(&[]),
        "and the handler is still usable afterwards"
    );
    assert_eq!(
        handler.events(),
        [NamespaceEvent::NotFound {
            path: NamePath::root(),
        }]
        .as_slice(),
        "recording only what happened after the clear"
    );
}

// A seeded outermost namespace, through the plain scope.

#[test]
fn init_visible_seeds_only_the_visible_namespace()
{
    let scope: Scope<Payload, ()> = Scope::with_init_visible(prelude_shaped());
    assert_eq!(
        listing(scope.visible()),
        listing(&prelude_shaped()),
        "the seeded prelude is what resolves here"
    );
    assert_eq!(
        listing(scope.export()),
        expected(&[]),
        "elaborating against a prelude does not re-export it"
    );
    assert_eq!(
        scope.resolve(&path("fs.read")).map(|binding| binding.data),
        Maybe::Present(Payload(10)),
        "recognition is ordinary resolution, not a name-table check"
    );
}

#[test]
fn a_user_binding_over_the_prelude_is_a_shadow_event()
{
    let mut scope: Scope<Payload, ()> = Scope::with_init_visible(prelude_shaped());
    let mut handler = PermissiveHandler::<HookLabel>::new();
    scope
        .include_subtree(
            &NamePath::root(),
            namespace(&[entry("env.get", Payload(99))]),
            &mut handler,
        )
        .expect("the warn-and-allow policy permits the shadow");
    assert_eq!(
        handler.events(),
        [NamespaceEvent::Shadow {
            path: path("env.get"),
        }]
        .as_slice(),
        "a script declaring its own `env.get` is a reportable event, not a prohibition"
    );
    assert_eq!(
        scope.resolve(&path("env.get")).map(|binding| binding.data),
        Maybe::Present(Payload(99)),
        "and under this policy the user's declaration wins"
    );
}

#[test]
fn a_rejecting_policy_forbids_shadowing_the_prelude()
{
    let mut scope: Scope<Payload, ()> = Scope::with_init_visible(prelude_shaped());
    let mut handler = RejectingHandler;
    let outcome = scope.include_subtree(
        &NamePath::root(),
        namespace(&[entry("env.get", Payload(99))]),
        &mut handler,
    );
    let ScopeError::Rejected(rejection) =
        outcome.expect_err("this policy forbids shadowing the prelude")
    else {
        panic!("the failure is an event rejection, not a structural one");
    };
    assert_eq!(
        rejection.kind(),
        EventKind::Shadow,
        "the same collision, refused instead of allowed: the policy moved, the engine did not"
    );
}

#[test]
fn a_nested_modifier_survives_a_round_trip()
{
    let inner = Modifier::seq(Vec::from([
        Modifier::only(path("plus")),
        Modifier::renaming(path("plus"), path("sum")),
    ]));
    // The identity first puts the nested modifier at a non-zero offset of
    // the composed arena.
    let composed = Modifier::seq(Vec::from([
        Modifier::id(),
        Modifier::in_subtree(path("nat"), inner.clone()),
    ]));
    let (outcome, events) = permissive(&composed, arith());

    let mut by_hand = arith();
    let detached = by_hand.detach_subtree(&path("nat"));
    let (rewritten, by_hand_events) = permissive(&inner, detached);
    by_hand.graft_subtree(&path("nat"), rewritten);

    assert_eq!(
        listing(&outcome),
        expected(&[
            entry("int.plus.assoc", Payload(3)),
            entry("nat.sum.assoc", Payload(1)),
        ]),
        "the nested modifier ran on `nat` alone"
    );
    assert_eq!(
        (outcome, events),
        (by_hand, by_hand_events),
        "composing and applying agrees with running the inner modifier on the detached \
             subtree by hand"
    );
    assert_eq!(
        Modifier::except(path("nat")),
        Modifier::in_subtree(path("nat"), Modifier::<HookLabel>::none()),
        "equality is structural: one modifier built two ways is one modifier"
    );
}

#[test]
fn every_namespace_walk_is_iterative()
{
    let worker = std::thread::Builder::new()
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let deep = chain(SegmentCount::from(DEPTH));
            let half = chain(SegmentCount::from(HALF_DEPTH));
            let mut trie: Trie<Payload, ()> = Trie::empty();
            let _fresh = trie.insert(&deep, Binding::new(Payload(1), ()));
            let copy = trie.clone();
            assert_eq!(trie, copy, "a deep namespace equals its clone");
            let listed: Vec<NamePath> = trie.iter().map(|(bound, _binding)| bound).collect();
            assert_eq!(
                listed,
                Vec::from([deep.clone()]),
                "the walk reaches the one binding at the bottom of the chain"
            );

            let detached = trie.detach_subtree(&half);
            assert_eq!(
                trie,
                Trie::empty(),
                "cutting the chain halfway leaves nothing above the cut"
            );
            trie.graft_subtree(&half, detached);
            assert_eq!(trie, copy, "grafting the cut back restores the chain");

            let mut collisions = 0_usize;
            trie.union_resolving(
                copy,
                &mut |_bound: &NamePath, collision: Collision<Payload, ()>| {
                    collisions = collisions.saturating_add(1_usize);
                    Ok::<Binding<Payload, ()>, EventRejection>(collision.latter)
                },
            )
            .expect("the resolver declines nothing");
            assert_eq!(
                collisions, 1_usize,
                "the two chains collide once, at the bottom"
            );
            assert_eq!(
                trie.get(&deep).map(|binding| binding.data),
                Maybe::Present(Payload(1)),
                "lookup reaches the bottom of the chain"
            );
            assert_eq!(
                trie.first_at_or_below(&half).map(|binding| binding.data),
                Maybe::Present(Payload(1)),
                "and so does the search below a prefix"
            );

            let mut handler = PermissiveHandler::<HookLabel>::new();
            let mut scope: Scope<Payload, ()> = Scope::new();
            scope
                .include_subtree(&NamePath::root(), trie, &mut handler)
                .expect("nothing collides in an empty scope");
            scope.begin_section();
            scope
                .end_section(&NamePath::root(), &Modifier::id(), &mut handler)
                .expect("a section is open");
            scope
                .modify_visible(
                    &Modifier::in_subtree(deep.clone(), Modifier::all()),
                    &mut handler,
                )
                .expect("the permissive policy rejects nothing");

            let mut nested = Modifier::<HookLabel>::all();
            for _ in 0_usize .. DEPTH {
                nested = Modifier::in_subtree(NamePath::root(), nested);
            }
            let applied = nested
                .apply(scope.visible().clone(), &mut handler)
                .expect("the permissive policy rejects nothing");
            let selected = Modifier::<HookLabel>::in_subtree(deep, Modifier::all())
                .apply(applied, &mut handler)
                .expect("the permissive policy rejects nothing");
            assert!(
                handler.events().is_empty(),
                "the chain is bound all the way down, so nothing was missing"
            );
            let count = selected.binding_count();
            drop(nested);
            drop(selected);
            drop(scope);
            count
        })
        .expect("the small-stack worker starts");

    let count = worker.join().expect("the small-stack worker finishes");
    assert_eq!(
        usize::from(count),
        1_usize,
        "the chain survives every walk, so the iteration claim is not vacuous"
    );
}

#[test]
fn a_rejection_reason_reads_as_the_text_it_was_given()
{
    let given = "this policy forbids shadowing";
    let reasons = [
        RejectionReason::from(given),
        RejectionReason::from(String::from(given)),
    ];
    for reason in &reasons {
        let text: &str = reason.as_ref();
        assert_eq!(text, given, "the reason reads as its text");
        assert_eq!(reason.to_string(), given, "and displays it");
    }
}

/// Each importer reads its base by one route, and the last reads nothing: the
/// imports read through are the reached ones, the last alone is not.
#[test]
fn each_import_a_name_is_read_through_is_reached()
{
    let pbg = grammar();
    let on = |source: usize| [ImportTarget::Source(SourceIndex::from(source))];
    let (first, fourth) = (on(0_usize), on(4_usize));
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "data Point : Type { One : Point; }\nmodule Cancel :> #{\n  notes : String\n} \
                 {\n  def notes = \"notes\";\n}\nmodule Str { def len(self : shared Integer) \
                 -> -F Integer { pure self } }\ndef seven : Integer ;\ndef seven = 7 ;",
            ),
            &[],
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef value : Integer ;\ndef value = seven ;",
            ),
            &first,
        ),
        (
            SourceText::from("import \"./base.gandr\" ;\ndef made = One ;"),
            &first,
        ),
        (
            SourceText::from("import \"./base.gandr\" ;\ndef kept(p : Point) -> -F Point { p }"),
            &first,
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef member : String ;\ndef member = Cancel.notes ;",
            ),
            &first,
        ),
        (
            SourceText::from(
                "import \"./member.gandr\" ;\ndef far : String ;\ndef far = Cancel.notes ;",
            ),
            &fourth,
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" as base ;\ndef aliased : Integer ;\ndef aliased = \
                 base.seven ;",
            ),
            &first,
        ),
        (
            SourceText::from(
                "import \"./base.gandr\" ;\ndef measured() -> -F Integer { hold s = 1; s.len() }",
            ),
            &first,
        ),
        (
            SourceText::from("import \"./base.gandr\" ;\ndef idle : Integer ;\ndef idle = 1 ;"),
            &first,
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let refused: Vec<String> = module
        .declarations()
        .iter()
        .filter(|declaration| matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
        .map(|declaration| String::from(declaration.name().as_ref()))
        .collect();
    assert_eq!(refused, Vec::<String>::new(), "every importer lowers");
    let imports: Vec<ByteSpan> = module
        .imports()
        .iter()
        .map(ImportDeclaration::span)
        .collect();
    let (idle, read) = imports.split_last().expect("the importers import");
    assert_eq!(
        module.reached_imports(),
        read,
        "a value, a constructor, a type head, a module member, one through an import of an \
         import, an aliased member and a method each reach the import they are read through"
    );
    assert!(
        !module.reached_imports().contains(idle),
        "an import nothing is read through is not reached"
    );
}
