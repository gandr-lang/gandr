//! Native nominal signature formation, sealed abstract-type formation and
//! capture-free telescope instantiation.
//!
//! # Nominal data
//!
//! A data declaration admits a nominal identity with a parameter telescope, an
//! ordered constructor table and a positive universe bound. Its signature is
//! not a value type for the declaration's constant: `Verdict::Data` is distinct
//! from a checked value, and a term reference to that position is refused. A
//! `Data` application checks each explicit argument against its instantiated
//! parameter classifier. Constructors retain that complete application and
//! their tag; fields check against the declaration's instantiated field types.
//! A case supplies exactly one branch per tag and a computation motive under
//! one scrutinee binder. Branches are ambient functions over their constructor
//! fields, not syntax under implicit field binders.
//!
//! An indexed family adds an index telescope after its parameters and states,
//! for each constructor, the indices it stands at, scoped under the parameters
//! and the constructor's fields. An application carries the parameters then
//! the indices; fields read the parameters alone; a constructor's annotation
//! converts with the application [`stated_at`] reads off its fields. A case
//! on an indexed family supplies a branch per constructor, each over that
//! constructor's fields at the motive applied to it, as a case on a family
//! with no indices does.
//!
//! **Choice.** Nominal identity stays separate from structural records; neither
//! is an abstract atom or a product encoding. Type parameters are quoted codes
//! and value indices are ordinary terms in one typed telescope. All arguments
//! are invariant: declaration formation proves no variance property that would
//! justify covariance. A declaration cannot see a later declaration.
//!
//! **Conversion boundary.** Index equality is structural in both checkers,
//! including under thunks, and ignores only candidate path evidence as ordinary
//! kernel conversion does. It does not reduce beta, delta or eta redexes.
//! General definitional index conversion waits for a certified kernel
//! conversion reader; frontend conversion alone cannot authorize it.
//! `term_indices_are_structural_in_both_checkers` witnesses separately
//! allocated equal function indices and constant references, and refuses beta-
//! and delta-related indices rather than accepting a declaration the kernel
//! rejects. **Reversal.** Widen this boundary only with replay-checked index
//! conversion and independent readmission witnesses.
//!
//! The programmatic forms cross ordinary checked kernel admission, canonical
//! artifacts, incremental support and edit snapshots, and
//! `gandr-core-sequent`'s machine runs nominal constructors, cases and
//! fixpoints. There is no parser notation, description decoder or graded thunk
//! former for them. Native declarations export as data declarations, not
//! axioms.
//!
//! # The field telescope
//!
//! A constructor's fields form a telescope after the parameters: field `i` is
//! scoped under the parameters, then fields `0 .. i`, the one before it
//! innermost. A field may name a universe and a later field the code it binds
//! (`Sup : (a : Type, f : +U (a -> -F Vinf))`), or a later field the decode of
//! an earlier code (`Mk : (c : U, v : el(c))`). [`field_type`] instantiates
//! the parameters beneath the earlier field binders; [`field_at`] then
//! substitutes the values a constructor gives those fields, which is the type
//! each field checks at; [`branch_type`] abstracts the fields in order, so a
//! branch's later domain names the earlier binders; [`field_outside`] reads a
//! field outside its constructor where it names none of them, as a pattern
//! column does. Every field is scoped this way whether or not it names an
//! earlier one, so a non-dependent field after the first reads its
//! parameters one binder further out per field before it.
//!
//! **Choice.** One telescope, uniform across fields. **Alternatives.** A
//! dependent pair packed into one field keeps every field under the
//! parameters alone, but puts the family inside a Σ the occurrence walk reads
//! as nested, and diverges from the surface the constructor is written in;
//! numbering the parameters innermost keeps a non-dependent field's indices
//! but forms each field in a context that is not a telescope, and every
//! instantiation then permutes indices; a per-constructor flag choosing the
//! scope is two conventions where one serves. **Reversal.** None needed for
//! dependency itself; a rule binding a variable at an open field after the
//! first is refused ([`slot_table`]) until a rule's slot reads its classifier
//! in the constructor's telescope, at the pattern's earlier fields.
//!
//! # Apartness
//!
//! A data type with no constructor is eliminated by its case of no branch,
//! which synthesizes its motive at the scrutinee like any data case; no β rule
//! exists, having no constructor to fire at. A path is eliminated the same way
//! when its endpoints are apart ([`apart`]): its carrier, read as its words at
//! a looped point, is a data type whose rules converge, and the endpoints'
//! normal forms first differ at two distinct constructors. Each endpoint is
//! read where the carrier stands — a constructor of it a node, a reference to
//! a definition its body, anything else a leaf — by the decision
//! `gandr_kernel_term::Presentation::apart` makes for both checkers, so the
//! kernel admits exactly the cases the checker does. A case whose endpoints
//! are not apart is refused [`CheckRefusal::NotApart`] with the reason.
//!
//! **Choice.** Apartness decided at the presented type, from its normal forms.
//! **Alternative.** Decoding: a map out of the type into one with its own
//! no-confusion — the circle's winding number into the integers — carries the
//! path to one between the images. Each type then owes its decoding, and the
//! integers at the bottom still need this rule at their constructors.
//! **Reversal.** An endpoint open at a constructor head, or a type whose
//! identity is not decided by normal form, takes decoding through a map the
//! program defines.
//!
//! # Sealed abstract types
//!
//! An abstract type forms when its kind is a value universe and its
//! representation forms at or below that universe's level; then its site
//! mints its atom and the context retains it. Like a data declaration it is
//! nominal — `Verdict::Data` answers it, and no value type enters the
//! signature table at its position — but its atom has no constructors and no
//! eliminator: inside its seal the weak head reads it as its representation,
//! and outside it relates to nothing but itself. The kernel admits the same
//! declaration under the same two premises.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Apartness;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::RuleSlot;
use gandr_kernel_term::TermReading;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::TypeNode;
use crate::declaration::AbstractType;
use crate::formation::form_value_type;
use crate::formation::level_of;

/// Read a data kind's value-universe level.
///
/// # Specification
/// - requires: nothing; malformed kinds are admissible input.
/// - ensures: only a value universe supplies a level.
/// - fails: a named kind refusal for any other former or sort.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::DataKindNotUniverse`] names the rejected kind.
///
/// # Adequacy
/// - hypothesis: L3 — both universe sorts and a non-universe separate the rule.
/// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|level| matches!(context.arena().value_type(kind), Some(ValueType::Universe { sort: Sort::Ground(GroundSort::Value), level: held }) if held == level)) == ret.is_ok())]
pub fn kind_level(
    context: &CheckingContext<'_>,
    kind: ValueTypeId,
) -> Result<Level, CheckRefusal>
{
    match context.arena().value_type(kind) {
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ref level,
        }) => Ok(level.clone()),
        _ => Err(CheckRefusal::DataKindNotUniverse(kind)),
    }
}

/// Check a parameter telescope, an index telescope and every constructor
/// field and stated index before admission.
///
/// Fields see the complete parameter telescope, the fields before them in
/// their constructor and the declaration's own family, at its admission
/// position. The family may occur in a field only where the stage order places
/// it below the constructor and at its parameter variables, which the
/// occurrence walk decides before anything forms; what the walk decided is
/// kept once the signature forms. A refused signature leaves no binder, block,
/// nominal entry or accessibility of its own; a family of an open mutual block
/// stays in scope with the block, which its other families' fields name.
///
/// # Specification
/// - requires: the nominal entry has not been installed in the context, and
///   `position` is the admission position the declaration takes.
/// - ensures: every occurrence of the family is accessible under the stage
///   order and uniform; every parameter, index and field forms in its declared
///   scope, an index under the parameters and the indices before it, a field
///   under the parameters and its constructor's fields before it; each stated
///   index checks at its index classifier past its constructor's fields
///   ([`index_at`]); fields fit the declared value universe; the original
///   binder depth is restored and the block closed, unless the family is one of
///   an open mutual block; on success the walk's accessibility is held at
///   `position`.
/// - fails: occurrence, kind, formation, field-universe and stated-index
///   refusals are retained; [`CheckRefusal::MachineInvariant`] for an indexed
///   family stating another number of indices, or presenting rules.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] identifies the failed formation judgment.
///
/// # Adequacy
/// - hypothesis: L3 — dependent parameters, an invalid field, an excessive
///   field universe, admitted self references and refused occurrences
///   distinguish the admission premises; a vector stating an element as its
///   length is refused.
/// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
/// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::readmission_agrees_with_the_checker_on_every_occurrence_class`
/// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole_in_both_checkers`
/// - witness: `tests::native_formers::an_indexed_family_stands_at_its_indices_in_both_checkers`
/// - witness: `former::tests::a_field_above_its_declaration_s_universe_is_refused`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth
    && (matches!(context.data_in_scope(position), Maybe::Absent(_))
        || context.data_signatures().contains_key(&position)
        || context.block_of(position) != crate::occurrence::Block::lone(position)))]
pub fn form_signature(
    context: &mut CheckingContext<'_>,
    position: ConstantIndex,
    signature: &Arc<DataSignature>,
) -> Result<(), CheckRefusal>
{
    let accessibility = crate::occurrence::occurrences(
        context.arena(),
        (
            &context.block_of(position),
            context.block_definitions(),
            context.accessibility(),
        ),
        signature,
    )?;
    let depth = context.depth(Zone::Intuitionistic);
    context.open_block(position, Arc::clone(signature));
    let outcome = (|| {
        let _kind = form_value_type(context, signature.kind())?;
        let level = kind_level(context, signature.kind())?;
        let upper = level
            .succ()
            .map_err(|_cause| CheckRefusal::DataKindNotUniverse(signature.kind()))?;
        for &parameter in signature.parameters() {
            let _formed = form_value_type(context, parameter)?;
            context.binders().open(Zone::Intuitionistic, parameter);
        }
        let stated = signature.results().len() == signature.constructors().len()
            && signature
                .results()
                .iter()
                .all(|results| results.len() == signature.indices().len());
        let presented = !signature.presentation().rules().is_empty()
            || signature.presentation().cells().is_some();
        if !signature.indices().is_empty() && (!stated || presented)
            || signature.indices().is_empty() && !signature.results().is_empty()
        {
            return Err(CheckRefusal::MachineInvariant);
        }
        let below = context.depth(Zone::Intuitionistic);
        for &index in signature.indices() {
            let _formed = form_value_type(context, index)?;
            context.binders().open(Zone::Intuitionistic, index);
        }
        while context.depth(Zone::Intuitionistic) != below {
            let _closed = context
                .binders()
                .close(Zone::Intuitionistic)
                .map_err(|_cause| CheckRefusal::MachineInvariant)?;
        }
        for (tag, fields) in signature.constructors().iter().enumerate() {
            let below = context.depth(Zone::Intuitionistic);
            for &field in fields {
                let _formed = form_value_type(context, field)?;
                if !bool::from(level_of(context, TypeNode::Value(field))?.lt(&upper)) {
                    return Err(CheckRefusal::DataFieldLevel {
                        field,
                        kind: signature.kind(),
                    });
                }
                context.binders().open(Zone::Intuitionistic, field);
            }
            let stated = signature.results().get(tag).map_or(&[][..], Vec::as_slice);
            for (position, (&value, &index)) in stated.iter().zip(signature.indices()).enumerate() {
                let binders = |count: usize| {
                    u32::try_from(count)
                        .map(Binders::from)
                        .map_err(|_cause| CheckRefusal::MachineInvariant)
                };
                let expected = index_at(
                    context,
                    index,
                    (stated, binders(position)?),
                    binders(fields.len())?,
                )?;
                let formed = form_value_type(context, expected)?;
                let _checked = crate::judgement::check_value(context, value, formed)?;
            }
            while context.depth(Zone::Intuitionistic) != below {
                let _closed = context
                    .binders()
                    .close(Zone::Intuitionistic)
                    .map_err(|_cause| CheckRefusal::MachineInvariant)?;
            }
        }
        present(context, position, signature)
    })();
    context.close_block(position);
    while context.depth(Zone::Intuitionistic) != depth {
        let _closed = context
            .binders()
            .close(Zone::Intuitionistic)
            .map_err(|_cause| CheckRefusal::MachineInvariant)?;
    }
    if outcome.is_ok() {
        context.record_accessibility(position, accessibility);
    }
    outcome
}

/// Check a data declaration's rules against its constructor table.
///
/// # Specification
/// - requires: `signature` is the declaration's at `position`, its fields
///   formed.
/// - ensures: `Ok(())` exactly when the rules validate against the table, a
///   field reading as the declaration's own type where it is the family at
///   `position` and as its classifier elsewhere — the table the kernel's
///   admission reads, so the two refuse alike.
/// - fails: [`CheckRefusal::RuleNotPresentable`] naming the first rule that
///   does not present the type and why.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a rule placing a constructor of the family at a field of
///   another type is refused by name in both checkers, and the circle's
///   cancellations admit.
/// - witness: `tests::native_formers::a_misplaced_rule_is_refused_in_both_checkers`
/// - witness: `tests::native_formers::a_presented_word_meets_its_reduced_word_in_both_checkers`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::RuleNotPresentable { .. })))]
fn present(
    context: &CheckingContext<'_>,
    position: ConstantIndex,
    signature: &DataSignature,
) -> Result<(), CheckRefusal>
{
    let presentation = signature.presentation();
    if presentation.rules().is_empty() {
        return Ok(());
    }
    presentation
        .validate(&slot_table(context.arena(), position, signature))
        .map_err(|refusal| CheckRefusal::RuleNotPresentable {
            kind: signature.kind(),
            refusal,
        })
}

/// A data declaration's constructor table as a rule side reads it: a field
/// reading as the declaration's own type where it is the family at
/// `position`; as dependent where it follows its constructor's first field and
/// its type is open, formed under the fields before it as well as the
/// parameters; and as its classifier elsewhere.
///
/// # Specification
/// - requires: `signature` is the declaration's at `position`.
/// - ensures: one row per constructor, one slot per field, as above; a field
///   whose reach cannot be read is dependent.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`present`], and a fold's law reads each pattern
///   variable at its slot; a rule binding the second field of a pair over a
///   parameter is refused rather than read at the first field's scope.
/// - witness: `tests::native_formers::a_misplaced_rule_is_refused_in_both_checkers`
/// - witness: `tests::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
/// - witness: `tests::native_formers::a_rule_binding_a_dependent_field_is_refused_in_both_checkers`
#[spec(ensures: |ret| ret.len() == signature.constructors().len())]
pub fn slot_table(
    arena: &gandr_core_term::CoreArena,
    position: ConstantIndex,
    signature: &DataSignature,
) -> Vec<Vec<RuleSlot<ValueTypeId>>>
{
    signature
        .constructors()
        .iter()
        .map(|fields| {
            fields
                .iter()
                .enumerate()
                .map(|(index, &field)| match arena.value_type(field) {
                    Some(&ValueType::Data { declaration, .. }) if declaration == position => {
                        RuleSlot::Own
                    },
                    _ if index != 0
                        && crate::code::loose_reach(
                            arena,
                            crate::refusal::CoreNode::Type(crate::refusal::TypeNode::Value(field)),
                        )
                        .map_or(true, |reach| {
                            reach != gandr_core_term::BinderDepth::default()
                        }) =>
                    {
                        RuleSlot::Dependent
                    },
                    _ => RuleSlot::Other(field),
                })
                .collect()
        })
        .collect()
}

quenchant_shape::reason_enum! {
    /// Why a path's endpoints are no question for the apartness rule.
    pub mod carrier {
        /// The reason the carrier is not decided over.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The carrier, read as its words where it is a path at a looped
            /// point, is no data type.
            NotData,
        }
    }
}

/// Decide whether `left` and `right`, the endpoints of a path at `carrier`,
/// are apart: the rule a case of no branches over the path rests on.
///
/// # Specification
/// - requires: `left` and `right` are terms of `carrier`, formed.
/// - ensures: [`gandr_kernel_term::Presentation::apart`] over the declaration's
///   own table ([`slot_table`]) and rules, both endpoints read by [`node`] —
///   each constructor of the declaration a constructor, each reference to a
///   definition its body, every other value a leaf by its id — when `carrier`,
///   read as its words where it is a path at a looped point, is a data type;
///   its signature and each definition read are then logged as consulted.
///   [`carrier::Absent::NotData`] otherwise. The kernel decides over the same
///   table, rules and terms (`presented::apart` in `gandr-kernel-core`), so the
///   two admit alike.
/// - provides: the apartness rule of the absurd case over a path.
/// - fails: as [`CheckingContext::identified`]; [`CheckRefusal::NotADataType`]
///   for a declaration not in scope.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — absurd cases over `S(Z)` against `Z`, over a free type's
///   distinct constructors and over the circle's loop, a definition, against
///   its empty word check, and over `S(P(Z))` against `Z` and over an open
///   endpoint are refused by name, in both checkers.
/// - witness: `tests::native_formers::an_absurd_case_rests_on_apart_endpoints_in_both_checkers`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::NotADataType(_) | CheckRefusal::Undecided { .. } | CheckRefusal::DanglingNode { .. } | CheckRefusal::OutOfFragment { .. })))]
pub fn apart(
    context: &mut CheckingContext<'_>,
    carrier: ValueTypeId,
    endpoints: (ValueId, ValueId),
) -> Result<Maybe<Apartness, carrier::Absent>, CheckRefusal>
{
    let carrier = context.identified(carrier)?;
    let Some(&ValueType::Data { declaration, .. }) = context.arena().value_type(carrier)
    else {
        return Ok(Maybe::Absent(carrier::Absent::NotData));
    };
    let signature = context
        .consult_data(declaration)
        .ok_or(CheckRefusal::NotADataType(declaration))?;
    let mut unfolded = Vec::new();
    let decided = {
        let (arena, definitions) = (context.arena(), context.definitions());
        let table = slot_table(arena, declaration, &signature);
        signature
            .presentation()
            .apart(&table, endpoints, |at, fields| {
                node(
                    (arena, definitions),
                    declaration,
                    (at, fields),
                    &mut unfolded,
                )
            })
    };
    for constant in unfolded {
        let _answer = context.consult(constant);
    }
    Ok(Maybe::Present(decided))
}

/// The node at `at` as a term of the data type `declaration` heads.
///
/// # Specification
/// - requires: nothing — an unreadable id is a leaf.
/// - ensures: [`TermReading::Constructor`] with its fields appended for a
///   constructor of `declaration`; [`TermReading::Defined`] with the body for a
///   reference to a definition, the reference's constant appended to
///   `unfolded`; [`TermReading::Other`] for every other value. The kernel reads
///   its own arena alike.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`apart`].
/// - witness: `tests::native_formers::an_absurd_case_rests_on_apart_endpoints_in_both_checkers`
#[spec(captures: before = fields.len(), ensures: |ret| matches!(ret, TermReading::Constructor(_)) || fields.len() == before)]
fn node(
    (arena, definitions): (&gandr_core_term::CoreArena, &crate::code::CodeDefinitions),
    declaration: ConstantIndex,
    (at, fields): (ValueId, &mut Vec<ValueId>),
    unfolded: &mut Vec<ConstantIndex>,
) -> TermReading<ValueId>
{
    match arena.value(at) {
        Some(&Value::Constructor {
            datatype,
            tag,
            fields: ref written,
        }) if matches!(
            arena.value_type(datatype),
            Some(&ValueType::Data { declaration: found, .. }) if found == declaration
        ) =>
        {
            fields.extend_from_slice(written);
            TermReading::Constructor(tag)
        },
        Some(&Value::Constant(constant)) => match definitions.body(constant) {
            Maybe::Present(body) => {
                unfolded.push(constant);
                TermReading::Defined(body)
            },
            Maybe::Absent(_) => TermReading::Other,
        },
        _ => TermReading::Other,
    }
}

/// Form an abstract type's kind and representation: the level of the universe
/// its atom will inhabit.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the kind is a value universe whose level is returned,
///   the representation forms at or below that level, and the site has not
///   minted an atom; the seal table is unchanged either way.
/// - fails: the formation refusal of the kind or the representation;
///   [`CheckRefusal::AbstractKindNotUniverse`] for a kind that is no value
///   universe, or one at the greatest level;
///   [`CheckRefusal::RepresentationAboveKind`] for a representation above it;
///   [`CheckRefusal::SealSiteRepeated`] for a site minted before.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] identifies the failed premise.
///
/// # Adequacy
/// - hypothesis: L3 — a kind at a value universe, a kind that is no universe, a
///   representation above its kind and a repeated site separate the premises.
/// - witness: `module::tests::an_abstract_type_forms_at_a_value_universe_and_mints_its_site`
/// - witness: `module::tests::a_repeated_sealing_site_is_refused_and_mints_nothing`
#[spec(
    captures: minted = context.seal_table().sites().len(),
    ensures: |ret| context.seal_table().sites().len() == minted
        && (ret.is_err() || matches!(context.seal_table().lookup(declared.site()), Maybe::Absent(_))),
)]
pub fn form_abstract(
    context: &mut CheckingContext<'_>,
    declared: AbstractType,
) -> Result<Level, CheckRefusal>
{
    let kind = declared.kind();
    let _formed = form_value_type(context, kind)?;
    let level = match context.arena().value_type(kind) {
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ref level,
        }) => level.clone(),
        _ => return Err(CheckRefusal::AbstractKindNotUniverse(kind)),
    };
    let upper = level
        .succ()
        .map_err(|_cause| CheckRefusal::AbstractKindNotUniverse(kind))?;
    let representation = declared.representation();
    let _formed = form_value_type(context, representation)?;
    if !bool::from(level_of(context, TypeNode::Value(representation))?.lt(&upper)) {
        return Err(CheckRefusal::RepresentationAboveKind {
            representation,
            kind,
        });
    }
    if let Maybe::Present(_) = context.seal_table().lookup(declared.site()) {
        return Err(CheckRefusal::SealSiteRepeated(declared.site()));
    }
    Ok(level)
}

/// Check the interface `declared` states at the types its representation `R`
/// and its kind's level `level` give: the relation at `U(R → R → F kind)`, its
/// reflexivity at `U(Π (x : R). F El(⟨relation x x⟩))`, and the law, when
/// stated, at `U(Π (a b : R). Π (r : El(⟨relation a b⟩)). F Path(Σ (y : R).
/// El(⟨relation a y⟩), (b, r), (a, ⟨reflexivity a⟩)))`: every element of the
/// singleton at `a` is its centre. These are the types the kernel checks the
/// interface at when it admits the atom.
///
/// # Specification
/// - requires: `declared` formed by [`form_abstract`] at `level`.
/// - ensures: on success each stated value checks at its type; nothing is
///   checked for an atom stating no interface.
/// - fails: the formation or checking refusal of the first value that does not
///   check, the relation first, then the reflexivity, then the law.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] names the failed check.
///
/// # Adequacy
/// - hypothesis: L3 — a total relation over `Unit` with its reflexivity and
///   contraction checks, and each member named at another member's place is
///   refused; the same atom's identity reads the relation.
/// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
/// - witness: `bridge::tests::an_interface_member_named_at_another_member_s_type_refuses_the_atom`
#[spec(ensures: |ret| matches!(declared.interface(), Maybe::Present(_)) || ret.is_ok())]
pub fn form_interface(
    context: &mut CheckingContext<'_>,
    declared: AbstractType,
    level: &Level,
) -> Result<(), CheckRefusal>
{
    let Maybe::Present(interface) = declared.interface()
    else {
        return Ok(());
    };
    let representation = declared.representation();
    let kind = declared.kind();
    let arena = context.arena_mut();
    let codes = arena.comp_type_returner(kind);
    let inner = arena.comp_type_arrow(representation, codes);
    let outer = arena.comp_type_arrow(representation, inner);
    let relations = arena.value_type_thunk(outer);
    let formed = form_value_type(context, relations)?;
    let _checked = crate::judgement::check_value(context, interface.relation(), formed)?;
    let arena = context.arena_mut();
    let element = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let diagonal = related_by(
        arena,
        interface.relation(),
        (element, element),
        level.clone(),
    );
    let witnessed = arena.comp_type_returner(diagonal);
    let reflexive = arena.comp_type_pi(representation, witnessed);
    let reflexive = arena.value_type_thunk(reflexive);
    let formed = form_value_type(context, reflexive)?;
    let _checked = crate::judgement::check_value(context, interface.reflexivity(), formed)?;
    let Maybe::Present(law) = interface.law()
    else {
        return Ok(());
    };
    let lawful = law_type(
        context.arena_mut(),
        level,
        representation,
        (interface.relation(), interface.reflexivity()),
    );
    let formed = form_value_type(context, lawful)?;
    let _checked = crate::judgement::check_value(context, law, formed)?;
    Ok(())
}

/// `El(⟨relation left right⟩)` at `level`: the decode of the code `relation`
/// relates `left` and `right` by.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — the reflexivity is checked at the relation's diagonal and
///   the evidence at the relation between its endpoints, so another type
///   refuses the atom or the evidence.
/// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
/// - witness: `bridge::tests::an_interface_member_named_at_another_member_s_type_refuses_the_atom`
pub fn related_by(
    arena: &mut gandr_core_term::CoreArena,
    relation: ValueId,
    (left, right): (ValueId, ValueId),
    level: Level,
) -> ValueTypeId
{
    let forced = arena.computation_force(relation);
    let applied = arena.computation_application(forced, left);
    let applied = arena.computation_application(applied, right);
    let code = arena.value_returned(applied);
    arena.value_type_element(code, level)
}

/// The type an atom's identity-system law checks at over its representation
/// `R`: `U(Π (a b : R). Π (r : El(⟨relation a b⟩)). F Path(Σ (y : R).
/// El(⟨relation a y⟩), (b, r), (a, ⟨reflexivity a⟩)))`.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a law is checked at this type, so a reflexivity named as
///   the law refuses the atom and the stated law admits it.
/// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
/// - witness: `bridge::tests::an_interface_member_named_at_another_member_s_type_refuses_the_atom`
pub fn law_type(
    arena: &mut gandr_core_term::CoreArena,
    level: &Level,
    representation: ValueTypeId,
    (relation, reflexivity): (ValueId, ValueId),
) -> ValueTypeId
{
    let var = |arena: &mut gandr_core_term::CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // Under `a`, `b` and `r`, and under the pair's binder `y` beneath them.
    let (a, y) = (var(arena, 3), var(arena, 0));
    let singleton = related_by(arena, relation, (a, y), level.clone());
    let pairs = arena.value_type_sigma(representation, singleton);
    let (a, b, r) = (var(arena, 2), var(arena, 1), var(arena, 0));
    let source = arena.value_tuple(&[b, r]);
    let forced = arena.computation_force(reflexivity);
    let diagonal = arena.computation_application(forced, a);
    let centre = arena.value_returned(diagonal);
    let centre = arena.value_tuple(&[a, centre]);
    let contracted = arena.value_type_path(pairs, source, centre);
    let returns = arena.comp_type_returner(contracted);
    // Under `a` and `b`: the relation between them.
    let (a, b) = (var(arena, 1), var(arena, 0));
    let related = related_by(arena, relation, (a, b), level.clone());
    let over_r = arena.comp_type_pi(related, returns);
    let over_b = arena.comp_type_pi(representation, over_r);
    let over_a = arena.comp_type_pi(representation, over_b);
    arena.value_type_thunk(over_a)
}

/// Resolve the signature and check a nominal application's argument count:
/// one per parameter, then one per index.
///
/// # Specification
/// - requires: `datatype` is a native Data node.
/// - ensures: success supplies exactly its admitted signature at matching
///   arity.
/// - fails: absent nominal identities and wrong arity have distinct refusals.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::NotADataType`] or [`CheckRefusal::DataArgumentArity`].
///
/// # Adequacy
/// - hypothesis: L3 — equal carriers at distinct positions stay nominal.
/// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|signature| matches!(context.arena().value_type(datatype), Some(ValueType::Data { declaration, arguments }) if matches!(context.data_in_scope(*declaration), Maybe::Present(ref held) if held == signature) && signature.arity().0 == arguments.len())) == ret.is_ok())]
pub fn signature(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
) -> Result<Arc<DataSignature>, CheckRefusal>
{
    let (declaration, count) = match context.arena().value_type(datatype) {
        Some(&ValueType::Data {
            ref declaration,
            ref arguments,
        }) => (*declaration, arguments.len()),
        _ => return Err(CheckRefusal::MachineInvariant),
    };
    let signature = context
        .consult_data(declaration)
        .ok_or(CheckRefusal::NotADataType(declaration))?;
    if signature.arity().0 != count {
        return Err(CheckRefusal::DataArgumentArity(datatype));
    }
    Ok(signature)
}

/// Substitute a prefix of the application's arguments simultaneously.
///
/// # Specification
/// - requires: `subject` is scoped under `prefix` parameters of `datatype`.
/// - ensures: outer arguments retain their ambient indices; zero parameters
///   return the same node without rewriting.
/// - fails: malformed internal application references or an index ceiling.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::MachineInvariant`] for an invalid internal application.
///
/// # Adequacy
/// - hypothesis: L3 — two open arguments distinguish reversal and capture.
/// - witness: `tests::native_formers::dependent_data_parameters_and_case_motives`
#[spec(ensures: |ret| usize::from(prefix) != 0 || ret == Ok(subject))]
pub fn instantiate(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    mut subject: ValueTypeId,
    prefix: gandr_core_term::BinderDepth,
) -> Result<ValueTypeId, CheckRefusal>
{
    for index in (0 .. usize::from(prefix)).rev() {
        let argument = match context.arena().value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(CheckRefusal::MachineInvariant)?,
            _ => return Err(CheckRefusal::MachineInvariant),
        };
        let depth =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let argument = gandr_core_term::shift_value(context.arena_mut(), argument, depth)
            .settle(context.arena_mut());
        subject = gandr_core_term::instantiate_value_type(context.arena_mut(), subject, argument);
    }
    Ok(subject)
}

/// A constructor field's type at a nominal application, its parameters
/// instantiated at the application's arguments and its `earlier` fields left
/// bound.
///
/// # Specification
/// - requires: `field` is a field type of `datatype`'s declaration at telescope
///   position `earlier`: scoped under the parameters, then the constructor's
///   `earlier` fields before it.
/// - ensures: the same type scoped under the ambient context, then those
///   `earlier` fields, each parameter replaced by its argument carried under
///   them; zero parameters return the same node.
/// - fails: malformed internal application references or an index ceiling.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::MachineInvariant`] for an invalid internal application.
///
/// # Adequacy
/// - hypothesis: L3 — a list's tail at its second position reads the element
///   parameter past the head's binder, and a dependent field keeps the binder
///   of the field it names.
/// - witness: `former::tests::a_later_field_reads_its_parameters_past_the_earlier_fields`
#[spec(ensures: |ret| !matches!(context.arena().value_type(datatype), Some(ValueType::Data { arguments, .. }) if arguments.is_empty()) || ret == Ok(field))]
pub fn field_type(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    field: ValueTypeId,
    earlier: Binders,
) -> Result<ValueTypeId, CheckRefusal>
{
    // The fields are scoped under the parameters alone: an indexed family's
    // indices stand after them in the application and bind nothing.
    let (declaration, count) = match context.arena().value_type(datatype) {
        Some(&ValueType::Data {
            ref declaration,
            ref arguments,
        }) => (*declaration, arguments.len()),
        _ => return Err(CheckRefusal::MachineInvariant),
    };
    let count = match context.data_in_scope(declaration) {
        Maybe::Present(signature) => count.min(signature.parameters().len()),
        Maybe::Absent(_) => count,
    };
    let mut subject = field;
    for index in (0 .. count).rev() {
        let argument = match context.arena().value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(CheckRefusal::MachineInvariant)?,
            _ => return Err(CheckRefusal::MachineInvariant),
        };
        let depth =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let argument = gandr_core_term::shift_value(context.arena_mut(), argument, depth)
            .settle(context.arena_mut());
        subject = gandr_core_term::instantiate_value_type_under(
            context.arena_mut(),
            subject,
            argument,
            earlier,
        );
    }
    Ok(subject)
}

/// A constructor field's type at a constructor value: its parameters
/// instantiated at the application's arguments and its earlier fields at the
/// values the constructor gives them.
///
/// # Specification
/// - requires: `constructor` is a constructor value of `datatype`, and `field`
///   the type of its field at `position`.
/// - ensures: the field's type scoped in the ambient context, every parameter
///   and earlier field replaced by its value.
/// - provides: the type a constructor's field checks against.
/// - fails: as [`field_type`]; [`CheckRefusal::MachineInvariant`] for a
///   constructor holding fewer than `position` fields.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a field whose domain is the code an earlier field holds
///   checks at the decode of that code, and a field naming no earlier field at
///   its parameters alone.
/// - witness: `former::tests::a_dependent_field_checks_at_the_value_of_the_field_it_names`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&id| context.arena().value_type(id).is_some()) == ret.is_ok())]
pub fn field_at(
    context: &mut CheckingContext<'_>,
    (datatype, constructor): (ValueTypeId, ValueId),
    field: ValueTypeId,
    position: FieldPosition,
) -> Result<ValueTypeId, CheckRefusal>
{
    let position = usize::from(position);
    let earlier =
        Binders::from(u32::try_from(position).map_err(|_cause| CheckRefusal::MachineInvariant)?);
    let mut subject = field_type(context, datatype, field, earlier)?;
    for index in (0 .. position).rev() {
        let value = match context.arena().value(constructor) {
            Some(&Value::Constructor { ref fields, .. }) => fields
                .get(index)
                .copied()
                .ok_or(CheckRefusal::MachineInvariant)?,
            _ => return Err(CheckRefusal::MachineInvariant),
        };
        let depth =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let value = gandr_core_term::shift_value(context.arena_mut(), value, depth)
            .settle(context.arena_mut());
        subject = gandr_core_term::instantiate_value_type(context.arena_mut(), subject, value);
    }
    Ok(subject)
}

quenchant_shape::reason_enum! {
    /// Why a constructor field's type has no reading outside its constructor.
    pub mod outside {
        /// The reason the field is read only in its constructor's telescope.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its type names a field before it.
            Dependent,
        }
    }
}

/// A constructor field's type at a nominal application, read outside the
/// fields before it.
///
/// # Specification
/// - requires: as [`field_type`], `position` the field's place in its
///   constructor.
/// - ensures: the field's type in the ambient context, its parameters at the
///   application's arguments, when it names no field before it;
///   [`outside::Absent::Dependent`] when it names one.
/// - provides: the classifier a pattern column, or a rule's variable, takes at
///   a field independent of its constructor's other fields.
/// - fails: as [`field_type`].
/// - panics: none.
///
/// # Errors
/// As [`field_type`].
///
/// # Adequacy
/// - hypothesis: L3 — a list's tail reads at the list, and a field naming the
///   code before it is dependent.
/// - witness: `former::tests::a_later_field_reads_its_parameters_past_the_earlier_fields`
#[spec(ensures: |ret| usize::from(position) != 0 || matches!(ret, Ok(Maybe::Present(_)) | Err(_)))]
pub fn field_outside(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    field: ValueTypeId,
    position: FieldPosition,
) -> Result<Maybe<ValueTypeId, outside::Absent>, CheckRefusal>
{
    let earlier = Binders::from(
        u32::try_from(usize::from(position)).map_err(|_cause| CheckRefusal::MachineInvariant)?,
    );
    let subject = field_type(context, datatype, field, earlier)?;
    Ok(
        match gandr_core_term::strengthen_value_type(context.arena_mut(), subject, earlier) {
            Maybe::Present(lowered) => Maybe::Present(lowered.settle(context.arena_mut())),
            Maybe::Absent(_) => Maybe::Absent(outside::Absent::Dependent),
        },
    )
}

/// The classifier a constructor's stated index at `position` checks against,
/// read under the parameters and the constructor's `fields`: the index
/// classifier carried past the fields, the indices before it replaced by the
/// results the constructor states for them.
///
/// # Specification
/// - requires: `index` is scoped under the parameters and the `position`
///   indices before it; `stated` under the parameters and `fields` binders.
/// - ensures: the classifier scoped under the parameters and those binders; at
///   position zero, `index` carried past the fields alone.
/// - fails: [`CheckRefusal::MachineInvariant`] for a position past the stated
///   results or an unrepresentable binder count.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `Cons`'s `S(n)` checks at `Nat` past its three fields,
///   and its element is refused there.
/// - witness: `tests::native_formers::an_indexed_family_stands_at_its_indices_in_both_checkers`
#[spec(ensures: |ret| ret.is_err() || usize::try_from(u32::from(position)).is_ok_and(|position| position <= stated.len()))]
pub fn index_at(
    context: &mut CheckingContext<'_>,
    index: ValueTypeId,
    (stated, position): (&[ValueId], Binders),
    fields: Binders,
) -> Result<ValueTypeId, CheckRefusal>
{
    let arena = context.arena_mut();
    let mut subject =
        gandr_core_term::shift_value_type_under(arena, index, position, fields).settle(arena);
    for before in (0 .. u32::from(position)).rev() {
        let value = usize::try_from(before)
            .ok()
            .and_then(|before| stated.get(before))
            .copied()
            .ok_or(CheckRefusal::MachineInvariant)?;
        let value = gandr_core_term::shift_value(arena, value, Binders::from(before)).settle(arena);
        subject = gandr_core_term::instantiate_value_type(arena, subject, value);
    }
    Ok(subject)
}

/// The application a constructor value stands at: its family at the
/// annotation's parameter arguments, then at the indices its constructor
/// states, each read at the constructor's field values.
///
/// # Specification
/// - requires: `constructor` is a constructor value of `datatype` tagged `tag`,
///   holding one field per declared field.
/// - ensures: `datatype` itself for a family with no index; otherwise the
///   family applied to `datatype`'s parameter arguments and the indices the
///   constructor states.
/// - provides: the application a constructor's annotation must convert with.
/// - fails: as [`field_at`]; [`CheckRefusal::MachineInvariant`] for a tag past
///   the declaration's table.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `Cons(Z, x, Nil)` stands at `Vec(a, S(Z))`, and `Nil` at
///   `Vec(a, Z)` whatever its annotation says.
/// - witness: `tests::native_formers::an_indexed_family_stands_at_its_indices_in_both_checkers`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&id| context.arena().value_type(id).is_some()) == ret.is_ok())]
pub fn stated_at(
    context: &mut CheckingContext<'_>,
    (datatype, constructor): (ValueTypeId, ValueId),
    tag: ConstructorTag,
) -> Result<ValueTypeId, CheckRefusal>
{
    let signature = signature(context, datatype)?;
    if signature.indices().is_empty() {
        return Ok(datatype);
    }
    let Some(&ValueType::Data { declaration, .. }) = context.arena().value_type(datatype)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let (Some(fields), Some(results)) = (
        signature.constructors().get(usize::from(tag)),
        signature.results().get(usize::from(tag)),
    )
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    // Past the constructor's fields, the parameters read as the variables
    // its stated indices name them by.
    let parameters = signature.parameters().len();
    let past = fields
        .len()
        .checked_add(parameters)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let mut arguments = Vec::with_capacity(signature.arity().0);
    for position in 0 .. parameters {
        let distance = past
            .checked_sub(position)
            .and_then(|distance| distance.checked_sub(1))
            .and_then(|distance| u32::try_from(distance).ok())
            .ok_or(CheckRefusal::MachineInvariant)?;
        arguments.push(
            context
                .arena_mut()
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(distance)),
        );
    }
    arguments.extend(results.iter().copied());
    let stated = context.arena_mut().value_type_data(declaration, arguments);
    field_at(
        context,
        (datatype, constructor),
        stated,
        FieldPosition::from(fields.len()),
    )
}

/// Form the ordinary branch function's classifier.
///
/// Only the motive has an implicit scrutinee binder. Branches abstract their
/// fields explicitly with ordinary lambdas, in declaration order. At an indexed
/// family each branch then binds one equation per index, in index order: a
/// path from the index its constructor states, read at the branch's fields,
/// to the index the scrutinee stands at. A binder — a field or an equation —
/// binds the rest of the telescope only when the rest names it: the
/// classifier is the Π over that binder, and the plain arrow over every other,
/// as the lowering reads a written `(x : A) -> C` whose `C` does not name `x`.
/// One type has one node, so the classifier a hover prints reads back to it.
///
/// # Specification
/// - requires: the datatype and motive have formed and `tag` belongs to it.
/// - ensures: the result is a telescope over the constructor's fields, then one
///   equation per index of the family, ending in the motive applied to the
///   corresponding constructor; the equation at index `j` is `Path(I_j,
///   stated_j, scrutinee_j)`, `I_j` the index's classifier at the scrutinee's
///   earlier indices; each binder's former is a Π when the telescope after it
///   names it and a plain arrow, the rest strengthened past the binder,
///   otherwise.
/// - fails: a malformed application or an unrepresentable binder count.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] retains the failed nominal lookup or internal scope error.
///
/// # Adequacy
/// - hypothesis: L3 — dependent results and unequal fields separate motive
///   substitution, binder shifting and field order; a result naming its field
///   and one naming none separate the Π from the plain arrow; `Cons` at `Vec(a,
///   n)` owes `Path(Nat, S(m), n)` past its fields, and `Nil` `Path(Nat, Z,
///   n)`.
/// - witness: `tests::native_formers::dependent_data_parameters_and_case_motives`
/// - witness: `former::tests::a_branch_binds_a_field_only_where_its_result_names_it`
/// - witness: `former::tests::an_indexed_branch_binds_its_equations_after_its_fields`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&id| context.arena().comp_type(id).is_some()) == ret.is_ok())]
pub fn branch_type(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    tag: ConstructorTag,
    motive: CompTypeId,
) -> Result<CompTypeId, CheckRefusal>
{
    let signature = signature(context, datatype)?;
    let fields = signature
        .constructors()
        .get(usize::from(tag))
        .ok_or(CheckRefusal::MachineInvariant)?;
    let count = u32::try_from(fields.len()).map_err(|_cause| CheckRefusal::MachineInvariant)?;
    let shifted_type =
        gandr_core_term::shift_value_type(context.arena_mut(), datatype, Binders::from(count))
            .settle(context.arena_mut());
    let values = (0 .. count)
        .rev()
        .map(|index| {
            context
                .arena_mut()
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        })
        .collect();
    let constructor = context
        .arena_mut()
        .value_constructor(shifted_type, tag, values);
    let shifted = gandr_core_term::shift_comp_type_under(
        context.arena_mut(),
        motive,
        Binders::ONE,
        Binders::from(count),
    )
    .settle(context.arena_mut());
    let mut result =
        gandr_core_term::instantiate_comp_type(context.arena_mut(), shifted, constructor);
    let equations = equations(
        context,
        (datatype, &signature),
        (shifted_type, constructor),
        tag,
    )?;
    if !equations.is_empty() {
        let owed =
            u32::try_from(equations.len()).map_err(|_cause| CheckRefusal::MachineInvariant)?;
        result = gandr_core_term::shift_comp_type(context.arena_mut(), result, Binders::from(owed))
            .settle(context.arena_mut());
    }
    for &equation in equations.iter().rev() {
        result = bound(context, equation, result);
    }
    for (index, &field) in fields.iter().enumerate().rev() {
        let earlier =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let domain = field_type(context, datatype, field, earlier)?;
        result = bound(context, domain, result);
    }
    Ok(result)
}

/// The equations a branch at an indexed family binds past its constructor's
/// fields, the `j`th scoped under the fields and the `j` equations before it.
///
/// # Specification
/// - requires: `beneath` is `datatype` carried past the constructor's fields,
///   and `constructor` the constructor tagged `tag` at `beneath` holding those
///   fields' binders.
/// - ensures: none for a family with no index; otherwise one path type per
///   index, from the constructor's stated index to the scrutinee's.
/// - fails: as [`stated_at`] and [`instantiate`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a vector's two branches each bind one equation, from the
///   length their constructor states to the scrutinee's.
/// - witness: `former::tests::an_indexed_branch_binds_its_equations_after_its_fields`
/// - witness: `tests::native_formers::an_indexed_family_stands_at_its_indices_in_both_checkers`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.len() == signature.indices().len()))]
fn equations(
    context: &mut CheckingContext<'_>,
    (datatype, signature): (ValueTypeId, &DataSignature),
    (beneath, constructor): (ValueTypeId, ValueId),
    tag: ConstructorTag,
) -> Result<Vec<ValueTypeId>, CheckRefusal>
{
    if signature.indices().is_empty() {
        return Ok(Vec::new());
    }
    let fields = signature
        .constructors()
        .get(usize::from(tag))
        .map_or(0, Vec::len);
    let stated = stated_at(context, (beneath, constructor), tag)?;
    let parameters = signature.parameters().len();
    let mut equations = Vec::with_capacity(signature.indices().len());
    for (position, &index) in signature.indices().iter().enumerate() {
        let argument = parameters
            .checked_add(position)
            .ok_or(CheckRefusal::MachineInvariant)?;
        let below = fields
            .checked_add(position)
            .and_then(|below| u32::try_from(below).ok())
            .map(Binders::from)
            .ok_or(CheckRefusal::MachineInvariant)?;
        let earlier = Binders::from(
            u32::try_from(position).map_err(|_cause| CheckRefusal::MachineInvariant)?,
        );
        let carrier = instantiate(
            context,
            datatype,
            index,
            gandr_core_term::BinderDepth::from(argument),
        )?;
        let carrier = gandr_core_term::shift_value_type(context.arena_mut(), carrier, below)
            .settle(context.arena_mut());
        let (Some(&left), Some(&right)) = (
            data_arguments(context, stated).get(argument),
            data_arguments(context, datatype).get(argument),
        )
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let left = gandr_core_term::shift_value(context.arena_mut(), left, earlier)
            .settle(context.arena_mut());
        let right = gandr_core_term::shift_value(context.arena_mut(), right, below)
            .settle(context.arena_mut());
        equations.push(context.arena_mut().value_type_path(carrier, left, right));
    }
    Ok(equations)
}

/// The arguments of a nominal application, and none of anything else.
///
/// # Specification
/// trivial.
fn data_arguments<'arena>(
    context: &'arena CheckingContext<'_>,
    application: ValueTypeId,
) -> &'arena [ValueId]
{
    match context.arena().value_type(application) {
        Some(&ValueType::Data { ref arguments, .. }) => arguments,
        _ => &[],
    }
}

/// `domain` bound over `result`: the plain arrow when `result` does not name
/// the binder, strengthened past it, and the Π otherwise.
///
/// # Specification
/// trivial.
fn bound(
    context: &mut CheckingContext<'_>,
    domain: ValueTypeId,
    result: CompTypeId,
) -> CompTypeId
{
    match gandr_core_term::strengthen_comp_type(context.arena_mut(), result) {
        Maybe::Present(closed) => {
            let closed = closed.settle(context.arena_mut());
            context.arena_mut().comp_type_arrow(domain, closed)
        },
        Maybe::Absent(_) => context.arena_mut().comp_type_pi(domain, result),
    }
}

#[cfg(test)]
mod tests;
