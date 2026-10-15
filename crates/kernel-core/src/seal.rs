//! The **seal rule**: inside the admission that minted an abstract type, the
//! atom reads as its representation; outside it, the atom is opaque.
//!
//! # The decision
//!
//! **Choice.** An abstract-type declaration carries its kind, the
//! representation it was sealed over, and the scope of the admission that
//! minted it. While that admission is open the environment lists the atom as
//! *manifest*, and a declaration admitted then is checked with every manifest
//! atom read as its representation — at its own declared type, and at the type
//! of every constant it names — while it is admitted at its declared type, the
//! atom included. When the admission closes the atom leaves the manifest, and
//! from then on no rule reads the representation: conversion relates the atom
//! to itself alone, so a value of the representation is refused where the atom
//! is expected. A sealed module's export is therefore checked twice over by
//! the kernel and never postulated: its members against the representation,
//! and every client against the atom.
//!
//! This is the existential package of *F-ing modules* (Rossberg, Russo and
//! Dreyer) with the package and its unpacking at one site: the members are the
//! package body, checked at the witness type, and the atom is the abstract
//! type a client sees after unpacking. The atom is generative — one per
//! abstract component per sealing site, minted at the site's admission
//! position — which is opaque ascription in the sense of Harper and
//! Lillibridge and of Leroy's manifest types, with the generative reading
//! Dreyer, Crary and Harper give sealing.
//!
//! **The boundary is the kernel's own.** A scope is a count of admissions
//! the atom's record carries, and an open scope is closed by
//! [`Environment::seal`] with the count the environment itself kept. No
//! later declaration names the atoms it is inside — no provenance, no
//! certificate — so none can claim its way in: membership is decided from the
//! atom's own record and the environment's admission count.
//!
//! **Where the rule reads.** The substitution is applied at the two places a
//! type enters a check from outside the term being checked: a definition's
//! declared type, and a constant's synthesized type. Everything a body builds
//! from those is then already at the representation. A code is not entered: an
//! atom inside a code stays opaque even inside its minting admission, so a body
//! comparing such a code with its representation's code is refused. That is
//! incompleteness a producer avoids by writing the representation, never a
//! soundness hazard. A representation is closed — it forms in the empty
//! context — so substituting it under a binder captures nothing.
//!
//! **Alternatives.** Postulating each sealed member as an axiom at the atom
//! would move the module's correctness out of the kernel and into the audit.
//! Admitting the members at the representation and relying on the producer to
//! re-type clients would make opacity a producer convention. A sealing
//! provenance on each member naming the atoms it may see through would let a
//! forged declaration claim a module's inside. A transparent definition whose
//! unfolding the kernel switches off after the module would make every
//! conversion consult a mutable transparency table.
//!
//! **Reversal.** If a sealed module's members must be re-checkable without
//! their representation — an artifact that hides it from its readers — the
//! representation moves out of the atom's record into a separate, optional
//! segment the replay demands only for the members' admissions. If codes must
//! see through an open atom, the substitution moves into the rewrite engine as
//! a third rewrite beside shifting and substitution.
//!
//! [`Environment::seal`]: crate::Environment::seal

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::env::AdmittedDeclaration;
use crate::error::KernelError;

/// A node the substitution walk visits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node
{
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// One step of the walk: descend into a node, or rebuild it from its
/// children's results.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// Schedule the node's children, then its rebuild.
    Enter(Node),
    /// Rebuild the node from its children's results.
    Exit(Node),
}

/// The results the walk has computed so far, one per visited node.
#[derive(Debug, Default)]
struct Unsealed
{
    /// The substituted value types, by original id.
    value_types: BTreeMap<ValueTypeId, ValueTypeId>,
    /// The substituted computation types, by original id.
    comp_types: BTreeMap<CompTypeId, CompTypeId>,
}

impl Unsealed
{
    /// The substituted value type of an already-rebuilt child.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded result for `id`.
    /// - provides: the lookup a rebuild reads its children through.
    /// - fails: [`KernelError::ArenaFault`] when `id` was not rebuilt, which
    ///   the walk's post-order rules out.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::ArenaFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rebuild reads its children through here, so a
    ///   member checked at a nested representation exercises it.
    /// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
    #[spec(ensures: |ret| ret.as_ref().ok() == self.value_types.get(&id))]
    fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Result<ValueTypeId, KernelError>
    {
        self.value_types
            .get(&id)
            .copied()
            .ok_or(KernelError::ArenaFault)
    }

    /// The substituted computation type of an already-rebuilt child.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded result for `id`.
    /// - provides: the lookup a rebuild reads its children through.
    /// - fails: [`KernelError::ArenaFault`] when `id` was not rebuilt, which
    ///   the walk's post-order rules out.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::ArenaFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_type`], on the computation plane.
    /// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
    #[spec(ensures: |ret| ret.as_ref().ok() == self.comp_types.get(&id))]
    fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Result<CompTypeId, KernelError>
    {
        self.comp_types
            .get(&id)
            .copied()
            .ok_or(KernelError::ArenaFault)
    }
}

quenchant_shape::reason_enum! {
    /// Why an atom reference does not unfold.
    mod unfolding {
        /// The atom is opaque at this admission.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The atom is not manifest, or the position names no abstract
            /// type.
            Opaque,
        }
    }
}

/// The representation `atom` unfolds to, when it is manifest.
///
/// # Specification
/// - requires: `manifest` is ascending.
/// - ensures: the representation recorded in the abstract-type declaration at
///   `atom` exactly when `atom` is in `manifest` and names one, and the absence
///   otherwise.
/// - provides: the one place the seal rule reads a representation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a manifest atom unfolds and a sealed one does not.
/// - witness: `seal::tests::only_a_manifest_atom_unfolds`
#[spec(ensures: |ret| match (manifest.binary_search(&atom).is_ok(), entries.get(usize::from(atom)).map(AdmittedDeclaration::content)) {
    (true, Some(&DeclarationContent::AbstractType { representation, .. })) => matches!(ret, quenchant_shape::shape::Maybe::Present(found) if found == representation),
    _ => matches!(ret, quenchant_shape::shape::Maybe::Absent(unfolding::Absent::Opaque)),
})]
fn representation(
    entries: &[AdmittedDeclaration],
    manifest: &[ConstantIndex],
    atom: ConstantIndex,
) -> quenchant_shape::shape::Maybe<ValueTypeId, unfolding::Absent>
{
    use quenchant_shape::shape::Maybe;
    if manifest.binary_search(&atom).is_err() {
        return Maybe::Absent(unfolding::Absent::Opaque);
    }
    match entries
        .get(usize::from(atom))
        .map(AdmittedDeclaration::content)
    {
        Some(&DeclarationContent::AbstractType { representation, .. }) => {
            Maybe::Present(representation)
        },
        Some(_) | None => Maybe::Absent(unfolding::Absent::Opaque),
    }
}

/// `root` with every manifest atom read as its representation, recursively.
///
/// # Specification
/// - requires: `manifest` is ascending and names abstract types in `entries`.
/// - ensures: `root` itself when `manifest` is empty or no manifest atom occurs
///   in `root` outside a code; otherwise a type minted into `arena` that is
///   `root` with each such occurrence replaced by its representation, itself
///   substituted. A node none of whose children changed is returned unchanged.
///   Codes, nominal arguments and path endpoints are values and are not
///   entered.
/// - provides: the seal rule's substitution, applied by the checker to a
///   definition's declared type and to a constant's synthesized type.
/// - fails: [`KernelError::ArenaFault`] on an unreadable node.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ArenaFault`].
///
/// # Adequacy
/// - hypothesis: L3 — an empty manifest returns the root; an atom nested in a
///   thunk, an arrow, a product and a record unseals in each; an atom whose
///   representation names an earlier manifest atom unseals both; a sealed atom
///   beside a manifest one is kept.
/// - witness: `seal::tests::only_a_manifest_atom_unfolds`
/// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
#[spec(ensures: |ret| !manifest.is_empty() || ret.as_ref().ok() == Some(&root))]
pub(crate) fn unseal(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    manifest: &[ConstantIndex],
    root: ValueTypeId,
) -> Result<ValueTypeId, KernelError>
{
    if manifest.is_empty() {
        return Ok(root);
    }
    let mut done = Unsealed::default();
    let mut steps = Vec::from([Step::Enter(Node::ValueType(root))]);
    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(node) => enter(arena, entries, manifest, &done, node, &mut steps)?,
            Step::Exit(Node::ValueType(id)) => {
                let rebuilt = exit_value_type(arena, entries, manifest, &done, id)?;
                let _first = done.value_types.insert(id, rebuilt);
            },
            Step::Exit(Node::CompType(id)) => {
                let rebuilt = exit_comp_type(arena, &done, id)?;
                let _first = done.comp_types.insert(id, rebuilt);
            },
        }
    }
    done.value_type(root)
}

/// Schedule `node`'s rebuild and, above it, its children's visits.
///
/// # Specification
/// - requires: nothing.
/// - ensures: nothing is scheduled for a node already rebuilt; otherwise its
///   exit is pushed, then an entry for each child the substitution enters — for
///   a manifest atom, its representation.
/// - provides: the descent half of the post-order walk.
/// - fails: [`KernelError::ArenaFault`] on an unreadable node.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ArenaFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`unseal`].
/// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
#[spec(captures: entry = steps.len(), ensures: |ret| ret.is_err() || steps.len() >= entry)]
fn enter(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    manifest: &[ConstantIndex],
    done: &Unsealed,
    node: Node,
    steps: &mut Vec<Step>,
) -> Result<(), KernelError>
{
    match node {
        Node::ValueType(id) => {
            if done.value_types.contains_key(&id) {
                return Ok(());
            }
            steps.push(Step::Exit(node));
            match *arena.value_type(id).ok_or(KernelError::ArenaFault)? {
                ValueType::Abstract(atom) => {
                    if let quenchant_shape::shape::Maybe::Present(unfolded) =
                        representation(entries, manifest, atom)
                    {
                        steps.push(Step::Enter(Node::ValueType(unfolded)));
                    }
                },
                ValueType::Record(ref fields) => steps.extend(
                    fields
                        .values()
                        .map(|&field| Step::Enter(Node::ValueType(field))),
                ),
                ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                    steps.extend(parts.iter().map(|&part| Step::Enter(Node::ValueType(part))));
                },
                ValueType::Sigma { first, second } => {
                    steps.push(Step::Enter(Node::ValueType(first)));
                    steps.push(Step::Enter(Node::ValueType(second)));
                },
                ValueType::List(inner)
                | ValueType::Lift { inner, .. }
                | ValueType::Path { domain: inner, .. }
                | ValueType::Flow { domain: inner, .. }
                | ValueType::Session {
                    payloads: inner, ..
                } => steps.push(Step::Enter(Node::ValueType(inner))),
                ValueType::Thunk(computation) => {
                    steps.push(Step::Enter(Node::CompType(computation)));
                },
                ValueType::Data { .. }
                | ValueType::PathUniverse(..)
                | ValueType::FlowUniverse(..)
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Element { .. }
                | ValueType::StaticPi { .. } => {},
            }
        },
        Node::CompType(id) => {
            if done.comp_types.contains_key(&id) {
                return Ok(());
            }
            steps.push(Step::Exit(node));
            match *arena.comp_type(id).ok_or(KernelError::ArenaFault)? {
                CompType::Returner(result) => {
                    steps.push(Step::Enter(Node::ValueType(result)));
                },
                CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                    steps.push(Step::Enter(Node::ValueType(domain)));
                    steps.push(Step::Enter(Node::CompType(codomain)));
                },
                CompType::With(left, right) => {
                    steps.push(Step::Enter(Node::CompType(left)));
                    steps.push(Step::Enter(Node::CompType(right)));
                },
                CompType::Element { .. } => {},
            }
        },
    }
    Ok(())
}

/// Rebuild a value type from its children's results.
///
/// # Specification
/// - requires: every child [`enter`] scheduled for `id` has been rebuilt.
/// - ensures: for a manifest atom, its representation's result; for a node
///   whose children all came back unchanged, `id`; otherwise the same former
///   minted over the rebuilt children.
/// - provides: the ascent half of the walk on the value plane.
/// - fails: [`KernelError::ArenaFault`] on an unreadable node or a child not
///   yet rebuilt.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ArenaFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`unseal`].
/// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|rebuilt| arena.value_type(*rebuilt).is_some()))]
fn exit_value_type(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    manifest: &[ConstantIndex],
    done: &Unsealed,
    id: ValueTypeId,
) -> Result<ValueTypeId, KernelError>
{
    let node = arena.value_type(id).ok_or(KernelError::ArenaFault)?.clone();
    let rebuilt = match node {
        ValueType::Abstract(atom) => match representation(entries, manifest, atom) {
            quenchant_shape::shape::Maybe::Present(unfolded) => done.value_type(unfolded)?,
            quenchant_shape::shape::Maybe::Absent(_) => id,
        },
        ValueType::Record(fields) => {
            let mut rebuilt = BTreeMap::new();
            for (label, &field) in &fields {
                let _first = rebuilt.insert(label.clone(), done.value_type(field)?);
            }
            if rebuilt == fields {
                id
            }
            else {
                arena.value_type_record(rebuilt)
            }
        },
        ValueType::Product(parts) => {
            let rebuilt = rebuilt_parts(done, &parts)?;
            if *rebuilt == *parts {
                id
            }
            else {
                arena.value_type_product(&rebuilt)
            }
        },
        ValueType::Sum(parts) => {
            let rebuilt = rebuilt_parts(done, &parts)?;
            if *rebuilt == *parts {
                id
            }
            else {
                arena.value_type_sum(&rebuilt)
            }
        },
        ValueType::Sigma { first, second } => {
            let rebuilt_first = done.value_type(first)?;
            let rebuilt_second = done.value_type(second)?;
            if rebuilt_first == first && rebuilt_second == second {
                id
            }
            else {
                arena.value_type_sigma(rebuilt_first, rebuilt_second)
            }
        },
        ValueType::List(element) => {
            let rebuilt = done.value_type(element)?;
            if rebuilt == element {
                id
            }
            else {
                arena.value_type_list(rebuilt)
            }
        },
        ValueType::Lift { inner, target } => {
            let rebuilt = done.value_type(inner)?;
            if rebuilt == inner {
                id
            }
            else {
                arena.value_type_lift(rebuilt, target)
            }
        },
        ValueType::Path {
            domain,
            left,
            right,
        } => {
            let rebuilt = done.value_type(domain)?;
            if rebuilt == domain {
                id
            }
            else {
                arena.value_type_path(rebuilt, left, right)
            }
        },
        ValueType::Flow {
            domain,
            source,
            target,
        } => {
            let rebuilt = done.value_type(domain)?;
            if rebuilt == domain {
                id
            }
            else {
                arena.value_type_flow(rebuilt, source, target)
            }
        },
        ValueType::Session { graph, payloads } => {
            let rebuilt = done.value_type(payloads)?;
            if rebuilt == payloads {
                id
            }
            else {
                arena.value_type_session(graph, rebuilt)
            }
        },
        ValueType::Thunk(computation) => {
            let rebuilt = done.comp_type(computation)?;
            if rebuilt == computation {
                id
            }
            else {
                arena.value_type_thunk(rebuilt)
            }
        },
        ValueType::Data { .. }
        | ValueType::PathUniverse(..)
        | ValueType::FlowUniverse(..)
        | ValueType::Base(_)
        | ValueType::Universe { .. }
        | ValueType::Element { .. }
        | ValueType::StaticPi { .. } => id,
    };
    Ok(rebuilt)
}

/// The rebuilt parts of a product or sum, in order.
///
/// # Specification
/// - requires: every part has been rebuilt.
/// - ensures: one result per part, in order.
/// - provides: the shared child map of the two n-ary formers.
/// - fails: [`KernelError::ArenaFault`] on a part not yet rebuilt.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ArenaFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`unseal`].
/// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|rebuilt| rebuilt.len() == parts.len()))]
fn rebuilt_parts(
    done: &Unsealed,
    parts: &[ValueTypeId],
) -> Result<Vec<ValueTypeId>, KernelError>
{
    parts.iter().map(|&part| done.value_type(part)).collect()
}

/// Rebuild a computation type from its children's results.
///
/// # Specification
/// - requires: every child [`enter`] scheduled for `id` has been rebuilt.
/// - ensures: `id` when every child came back unchanged; otherwise the same
///   former minted over the rebuilt children.
/// - provides: the ascent half of the walk on the computation plane.
/// - fails: [`KernelError::ArenaFault`] on an unreadable node or a child not
///   yet rebuilt.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ArenaFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`unseal`].
/// - witness: `seal::tests::a_nested_atom_unseals_through_every_former`
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|rebuilt| arena.comp_type(*rebuilt).is_some()))]
fn exit_comp_type(
    arena: &mut TermArena,
    done: &Unsealed,
    id: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    let node = arena.comp_type(id).ok_or(KernelError::ArenaFault)?.clone();
    let rebuilt = match node {
        CompType::Returner(result) => {
            let rebuilt = done.value_type(result)?;
            if rebuilt == result {
                id
            }
            else {
                arena.comp_type_returner(rebuilt)
            }
        },
        CompType::Arrow { domain, codomain } => {
            let (domain_rebuilt, codomain_rebuilt) =
                (done.value_type(domain)?, done.comp_type(codomain)?);
            if domain_rebuilt == domain && codomain_rebuilt == codomain {
                id
            }
            else {
                arena.comp_type_arrow(domain_rebuilt, codomain_rebuilt)
            }
        },
        CompType::Pi { domain, codomain } => {
            let (domain_rebuilt, codomain_rebuilt) =
                (done.value_type(domain)?, done.comp_type(codomain)?);
            if domain_rebuilt == domain && codomain_rebuilt == codomain {
                id
            }
            else {
                arena.comp_type_pi(domain_rebuilt, codomain_rebuilt)
            }
        },
        CompType::With(left, right) => {
            let (left_rebuilt, right_rebuilt) = (done.comp_type(left)?, done.comp_type(right)?);
            if left_rebuilt == left && right_rebuilt == right {
                id
            }
            else {
                arena.comp_type_with(left_rebuilt, right_rebuilt)
            }
        },
        CompType::Element { .. } => id,
    };
    Ok(rebuilt)
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::SealScope;
    use gandr_kernel_term::ValueType;

    use super::unseal;
    use crate::conv::Convertibility;
    use crate::conv::convertible_value_types;
    use crate::env::Environment;

    #[test]
    fn only_a_manifest_atom_unfolds()
    {
        let mut environment = Environment::new();
        for _ in 0_u8 .. 2 {
            let atom = {
                let mut staging = environment.stage();
                let kind = staging
                    .arena()
                    .value_type_universe(GroundSort::Value, Level::zero());
                let integer = staging.arena().value_type_base(BaseType::Integer);
                staging.abstract_type(
                    LevelSignature::monomorphic(),
                    kind,
                    integer,
                    SealScope::Open,
                )
            };
            let _admitted = environment.add_decl(atom).expect("an atom admits");
        }
        let first = ConstantIndex::from(0_usize);
        let second = ConstantIndex::from(1_usize);
        let mut arena = environment.arena().clone();
        let pair = {
            let one = arena.value_type_abstract(first);
            let other = arena.value_type_abstract(second);
            arena.value_type_product(&[one, other])
        };
        assert_eq!(
            unseal(&mut arena, environment.entries(), &[], pair),
            Ok(pair),
            "outside every minting admission the type is returned as it is"
        );
        let unsealed = unseal(&mut arena, environment.entries(), &[second], pair)
            .expect("the walk reads every node");
        let integer = arena.value_type_base(BaseType::Integer);
        let sealed = arena.value_type_abstract(first);
        let expected = arena.value_type_product(&[sealed, integer]);
        assert_eq!(
            convertible_value_types(&arena, unsealed, expected),
            Convertibility::Convertible,
            "the manifest atom unfolds and the sealed one beside it is kept"
        );
    }

    #[test]
    fn a_nested_atom_unseals_through_every_former()
    {
        // `t` is sealed over the integer, and `u` over `t × t`: unsealing `u`
        // inside both admissions reaches the integer through `t`.
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, Level::zero());
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Open,
            )
        };
        let _t = environment.add_decl(atom).expect("t admits");
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, Level::zero());
            let t = staging
                .arena()
                .value_type_abstract(ConstantIndex::from(0_usize));
            let pair = staging.arena().value_type_product(&[t, t]);
            staging.abstract_type(LevelSignature::monomorphic(), kind, pair, SealScope::Open)
        };
        let _u = environment.add_decl(atom).expect("u admits over t");
        let manifest = [ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)];
        let mut arena = environment.arena().clone();
        let u = arena.value_type_abstract(ConstantIndex::from(1_usize));
        let list = arena.value_type_list(u);
        let returner = arena.comp_type_returner(list);
        let arrow = arena.comp_type_arrow(u, returner);
        let with = arena.comp_type_with(arrow, returner);
        let thunk = arena.value_type_thunk(with);
        let record = arena.value_type_record(BTreeMap::from([(
            FieldLabel::from(alloc::string::String::from("f")),
            thunk,
        )]));
        let unsealed = unseal(&mut arena, environment.entries(), &manifest, record)
            .expect("the walk reads every node");
        let integer = arena.value_type_base(BaseType::Integer);
        let pair = arena.value_type_product(&[integer, integer]);
        let list = arena.value_type_list(pair);
        let returner = arena.comp_type_returner(list);
        let arrow = arena.comp_type_arrow(pair, returner);
        let with = arena.comp_type_with(arrow, returner);
        let thunk = arena.value_type_thunk(with);
        let expected = arena.value_type_record(BTreeMap::from([(
            FieldLabel::from(alloc::string::String::from("f")),
            thunk,
        )]));
        assert_eq!(
            convertible_value_types(&arena, unsealed, expected),
            Convertibility::Convertible,
            "every former is rebuilt over its unsealed children"
        );
        assert!(
            matches!(arena.value_type(unsealed), Some(&ValueType::Record(_))),
            "and the root keeps its former"
        );
    }
}
