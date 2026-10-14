//! **Presented types**: a data declaration's rules, admitted against its own
//! constructor table, and the normal form its terms convert by.
//!
//! # What a presented type is to the kernel
//!
//! A data declaration may carry oriented rules over its own constructors
//! ([`gandr_kernel_term::Presentation`]). Its terms are then the constructor
//! terms modulo the rules, and two of them are definitionally equal exactly
//! when their normal forms are. The kernel takes nothing about the rules on
//! trust: admission re-checks each one ([`admit`]) and conversion rewrites by
//! them itself ([`normal_form`]); neither a dialogue nor a producer's claim
//! names a rewrite.
//!
//! # Admission
//!
//! A rule presents its type when it is linear and constructor-headed over the
//! declaration's own table, every constructor standing where the declaration's
//! own type does, every right-side variable at the slot its left occurrence
//! holds and at most once, and its right side holds fewer constructors than
//! its left. Such a rule removes a constructor from every term it rewrites,
//! so a term of `n` constructors normalizes in at most `n` rewrites: the
//! kernel needs no termination claim and no budget argument beyond the term's
//! own size. Confluence is not checked here. The normal form is taken by one
//! fixed strategy (`Presentation::normalize` names it), so conversion is an
//! equivalence and sound for the equational theory whether or not the rules
//! are confluent; confluence makes it complete, and the producer's coincidence
//! check is where a presentation's convergence is established.
//!
//! **Alternatives.** A recursive path order would admit size-preserving rules
//! such as associativity, at the price of a precedence in the trusted base. A
//! critical-pair check in the kernel would make conversion complete for every
//! admitted presentation, at the price of joining every overlap at admission.
//! **Reversal.** The first presented type whose rules preserve size takes a
//! path order; the first conversion the fixed strategy separates though the
//! theory equates takes the critical-pair check.
//!
//! # The normal form
//!
//! The replay takes [`normal_form`] in weak head form, once it has read the
//! leaves that are returned endpoints: `Replay::read_returned_leaves` in
//! [`mod@crate::replay`] records which leaves are read, how, and why.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Exhausted;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::Normalized;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleSlot;
use gandr_kernel_term::RuleTerm;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::env::AdmittedDeclaration;
use crate::error::KernelError;

/// One presented type as conversion reads it: its rules and the arity of each
/// of its constructors, in tag order.
///
/// # Specification
/// - provides: what [`Presentation::normalize`] needs beside the term.
/// - panics: none.
/// - executable: none — data declaration; [`Presentations::of`] builds it from
///   an admitted declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PresentedType
{
    /// The rules, in written order.
    presentation: Presentation,
    /// Each constructor's field count, in tag order.
    arities: Arc<[FieldCount]>,
}

/// The presented types of an environment, by admission position.
///
/// # Specification
/// - provides: the rule table every conversion of the environment's terms
///   reads; empty, and free to build and clone, while no admitted declaration
///   presents its type.
/// - panics: none.
/// - executable: none — data declaration; lookup is its observer.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Presentations(Option<Arc<BTreeMap<ConstantIndex, PresentedType>>>);

/// The presentations of an environment presenting no type.
pub(crate) static FREE: Presentations = Presentations(None);

impl Presentations
{
    /// The presented types among `entries`, each at its admission position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the data declarations among `entries` whose
    ///   presentation holds a rule, each with its rules and arities.
    /// - provides: the table [`crate::replay::Unfoldings::presenting`] hands
    ///   every replay over the environment.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`normal_form`].
    /// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
    #[spec(ensures: |ret| ret.0.as_ref().is_none_or(|table| !table.is_empty() && table.len() <= entries.len()))]
    #[inline]
    #[must_use]
    pub fn of(entries: &[AdmittedDeclaration]) -> Self
    {
        let mut presented = BTreeMap::new();
        for (position, entry) in entries.iter().enumerate() {
            let declaration = entry.declaration();
            if declaration.presentation().rules().is_empty() {
                continue;
            }
            if let DeclarationContent::Data {
                ref constructors, ..
            } = *declaration.content()
            {
                let _previous = presented.insert(ConstantIndex::from(position), PresentedType {
                    presentation: declaration.presentation().clone(),
                    arities: constructors
                        .iter()
                        .map(|fields| FieldCount::from(fields.len()))
                        .collect(),
                });
            }
        }
        if presented.is_empty() {
            return Self::default();
        }
        Self(Some(Arc::new(presented)))
    }

    /// The presented type at `constant`, if it presents one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn presented(
        &self,
        constant: ConstantIndex,
    ) -> Option<&PresentedType>
    {
        let table = self.0.as_ref()?;
        table.get(&constant)
    }
}

/// Check a data declaration's rules against its constructor table.
///
/// # Specification
/// - requires: `constructors` is the declaration's table, its field types in
///   `arena`, the declaration standing at `position`.
/// - ensures: `Ok(())` exactly when `presentation` validates against the table,
///   a field reading [`RuleSlot::Own`] where its type is the declaration's own
///   family and [`RuleSlot::Other`] with its type id elsewhere.
/// - provides: the admission obligation of a presented type.
/// - fails: [`KernelError::RuleNotPresentable`] naming the first rule that does
///   not present the type and why.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's rules admit, and a rule placing a
///   constructor under another type's field is refused by name.
/// - witness: `presented::tests::admission_reads_the_own_type_from_the_table`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::RuleNotPresentable(_))))]
pub(crate) fn admit(
    arena: &TermArena,
    position: ConstantIndex,
    constructors: &[Vec<ValueTypeId>],
    presentation: &Presentation,
) -> Result<(), KernelError>
{
    if presentation.rules().is_empty() {
        return Ok(());
    }
    let table: Vec<Vec<RuleSlot<ValueTypeId>>> = constructors
        .iter()
        .map(|fields| {
            fields
                .iter()
                .map(|&field| match arena.value_type(field) {
                    | Some(&ValueType::Data { declaration, .. }) if declaration == position => {
                        RuleSlot::Own
                    },
                    | _ => RuleSlot::Other(field),
                })
                .collect()
        })
        .collect();
    presentation
        .validate(&table)
        .map_err(KernelError::RuleNotPresentable)
}

/// Where a flattened constructor came from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Origin
{
    /// The value at this id, as written.
    Written(ValueId),
    /// A rewrite built it.
    Rewritten,
}

/// The normal form of `value` under the rules of the presented type heading
/// it.
///
/// # Specification
/// - requires: `value` lives in `arena`.
/// - ensures: `value` itself when it is not headed by a constructor of a
///   presented type or no rule matches anywhere in its constructor term;
///   otherwise the value minted for the term's normal form, every subterm the
///   rewriting left as written kept at its own id, every constructor it rebuilt
///   minted at the classifier of the one it stands for, or of the redex it
///   replaced. Each node compared or copied costs one unit of `fuel`.
/// - provides: the forced step the replay takes before it reads a value goal.
/// - fails: [`Exhausted`] when `fuel` runs out; nothing has been minted then.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loops over the flattening stack and over the
///   rewritten term, not recursion; the rewriting itself is
///   [`Presentation::normalize`]'s.
/// - measure: the arena nodes still to flatten, each a strict subterm; the term
///   nodes still to rebuild.
///
/// # Adequacy
/// - hypothesis: L3 — `loop(unloop(loop(x)))` normalizes to `loop(x)` over the
///   very variable written inside it, a normal form comes back as its own id,
///   and a value of a free type is never read.
/// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && ret.is_ok_and(|normal| normal == value || arena.value(normal).is_some()) || ret == Err(Exhausted))]
pub(crate) fn normal_form(
    arena: &mut TermArena,
    presentations: &Presentations,
    value: ValueId,
    fuel: &mut RewriteFuel,
) -> Result<ValueId, Exhausted>
{
    let Some(&Value::Constructor { datatype, .. }) = arena.value(value)
    else {
        return Ok(value);
    };
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Ok(value);
    };
    let Some(presented) = presentations.presented(declaration)
    else {
        return Ok(value);
    };
    let own = |arena: &TermArena, id: ValueId| match arena.value(id) {
        | Some(&Value::Constructor { datatype, .. }) => matches!(
            arena.value_type(datatype),
            Some(&ValueType::Data { declaration: found, .. }) if found == declaration
        ),
        | _ => false,
    };
    let mut term: Vec<RuleTerm<(ValueTypeId, Origin), ValueId>> = Vec::new();
    let mut pending = Vec::from([value]);
    while let Some(id) = pending.pop() {
        match arena.value(id) {
            | Some(&Value::Constructor {
                datatype,
                tag,
                ref fields,
            }) if own(arena, id) => {
                term.push(RuleTerm::Constructor {
                    tag,
                    arity: FieldCount::from(fields.len()),
                    payload: (datatype, Origin::Written(id)),
                });
                pending.extend(fields.iter().rev().copied());
            },
            | _ => term.push(RuleTerm::Leaf(id)),
        }
    }
    let normalized = presented.presentation.normalize(
        &presented.arities,
        &mut term,
        |&(datatype, _)| (datatype, Origin::Rewritten),
        fuel,
    )?;
    if normalized == Normalized::Unchanged {
        return Ok(value);
    }
    let mut built: Vec<ValueId> = Vec::new();
    while let Some(node) = term.pop() {
        match node {
            | RuleTerm::Leaf(id) => built.push(id),
            | RuleTerm::Constructor {
                tag,
                arity,
                payload: (datatype, origin),
            } => {
                let mut fields = built.split_off(built.len().saturating_sub(usize::from(arity)));
                fields.reverse();
                let kept = match origin {
                    | Origin::Written(id) => match arena.value(id) {
                        | Some(&Value::Constructor {
                            fields: ref written,
                            ..
                        }) if *written == fields => Some(id),
                        | _ => None,
                    },
                    | Origin::Rewritten => None,
                };
                built.push(kept.unwrap_or_else(|| arena.value_constructor(datatype, tag, fields)));
            },
        }
    }
    Ok(built.pop().unwrap_or(value))
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::PresentedRule;
    use gandr_kernel_term::RewriteFuel;
    use gandr_kernel_term::RuleFault;
    use gandr_kernel_term::RuleIndex;
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::RuleRefusal;
    use gandr_kernel_term::RuleVariable;
    use gandr_kernel_term::TermArena;

    use crate::env::Environment;
    use crate::error::KernelError;

    /// A constructor of the test's circle, `mark` taking a field of another
    /// type.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug)]
    enum Letter
    {
        /// `base`.
        Base,
        /// `loop(x)`.
        Loop,
        /// `unloop(x)`.
        Unloop,
        /// `mark(u)`, its field a unit.
        Mark,
    }

    impl Letter
    {
        /// The constructor's tag.
        ///
        /// # Specification
        /// trivial.
        fn tag(self) -> ConstructorTag
        {
            ConstructorTag::from(match self {
                | Self::Base => 0_usize,
                | Self::Loop => 1,
                | Self::Unloop => 2,
                | Self::Mark => 3,
            })
        }

        /// The constructor as a rule node.
        ///
        /// # Specification
        /// trivial.
        fn node(self) -> RuleNode
        {
            RuleNode::Constructor(self.tag())
        }
    }

    /// The first variable as a rule node.
    ///
    /// # Specification
    /// trivial.
    fn x() -> RuleNode
    {
        RuleNode::Variable(RuleVariable::from(0_u32))
    }

    /// The circle's two rules.
    ///
    /// # Specification
    /// trivial.
    fn circle() -> Presentation
    {
        let (looped, unlooped) = (Letter::Loop.node(), Letter::Unloop.node());
        Presentation::new(alloc::vec![
            PresentedRule::new([looped, unlooped, x()].into(), [x()].into()),
            PresentedRule::new([unlooped, looped, x()].into(), [x()].into()),
        ])
    }

    #[test]
    fn admission_reads_the_own_type_from_the_table()
    {
        let mut arena = TermArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let unit = arena.value_type_unit();
        let table = alloc::vec![
            alloc::vec![],
            alloc::vec![own],
            alloc::vec![own],
            alloc::vec![unit]
        ];
        assert_eq!(
            super::admit(&arena, ConstantIndex::from(0_usize), &table, &circle()),
            Ok(())
        );
        let other = Presentation::new(alloc::vec![PresentedRule::new(
            [Letter::Mark.node(), Letter::Base.node()].into(),
            [Letter::Base.node()].into()
        )]);
        assert_eq!(
            super::admit(&arena, ConstantIndex::from(0_usize), &table, &other),
            Err(KernelError::RuleNotPresentable(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: RuleFault::NotOwnPosition,
            }))
        );
        assert_eq!(
            super::admit(&arena, ConstantIndex::from(1_usize), &table, &circle()),
            Err(KernelError::RuleNotPresentable(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: RuleFault::NotOwnPosition,
            })),
            "at another position the same table is not the declaration's own"
        );
    }

    #[test]
    fn a_circle_word_normalizes_keeping_what_it_did_not_touch()
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(circle());
        let _admitted = environment
            .add_decl(staged)
            .expect("the circle admits with its rules");
        let presentations = super::Presentations::of(environment.entries());
        let mut cloned = environment.arena().clone();
        let arena = &mut cloned;
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let written = arena.value_constructor(own, Letter::Loop.tag(), alloc::vec![variable]);
        let unlooped = arena.value_constructor(own, Letter::Unloop.tag(), alloc::vec![written]);
        let word = arena.value_constructor(own, Letter::Loop.tag(), alloc::vec![unlooped]);
        let mut fuel = RewriteFuel::from(1_000_u64);
        let normal = super::normal_form(arena, &presentations, word, &mut fuel)
            .expect("the word normalizes within its fuel");
        assert!(
            matches!(
                arena.value(normal),
                Some(gandr_kernel_term::Value::Constructor { datatype, tag, fields })
                    if *datatype == own && *tag == Letter::Loop.tag() && fields.as_slice() == [variable]
            ),
            "`loop(unloop(loop(x)))` is `loop(x)`: the outer `loop` rebuilt over the variable \
             it now holds, the variable kept at its own id"
        );
        assert_eq!(
            super::normal_form(arena, &presentations, normal, &mut fuel),
            Ok(normal),
            "a normal form is its own normal form"
        );
        assert_eq!(
            super::normal_form(arena, &presentations, written, &mut fuel),
            Ok(written),
            "a reduced word is its own normal form"
        );
        let free = super::Presentations::default();
        assert_eq!(
            super::normal_form(arena, &free, word, &mut fuel),
            Ok(word),
            "without the declaration's rules the word is not read"
        );
    }

    /// An environment holding the circle at position zero, its terms read by
    /// `presentation`.
    ///
    /// # Specification
    /// trivial.
    fn circle_environment(presentation: Presentation) -> Environment
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        let _circle = environment.add_decl(staged).expect("the circle admits");
        environment
    }

    /// The word over `base` spelled by `letters`, outermost first.
    ///
    /// # Specification
    /// trivial.
    fn word(
        arena: &mut TermArena,
        letters: &[Letter],
    ) -> gandr_kernel_term::ValueId
    {
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let mut built = arena.value_constructor(own, Letter::Base.tag(), Vec::new());
        for &letter in letters.iter().rev() {
            built = arena.value_constructor(own, letter.tag(), alloc::vec![built]);
        }
        built
    }

    /// Offer `here(loop(base))` at `Path(Circle, loop(unloop(loop(base))),
    /// loop(base))`, then a constant naming it at `Path(Circle, loop(base),
    /// loop(base))`.
    ///
    /// # Specification
    /// trivial.
    fn offer(environment: &mut Environment) -> [Result<(), KernelError>; 2]
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let written = word(arena, &[Letter::Loop, Letter::Unloop, Letter::Loop]);
        let reduced = word(arena, &[Letter::Loop]);
        let declared = arena.value_type_path(own, written, reduced);
        let point = word(arena, &[Letter::Loop]);
        let here = arena.value_here(point);
        let staged = staging.def(LevelSignature::monomorphic(), declared, here);
        let reflexivity = environment.add_decl(staged).map(|_checked| ());
        let position = ConstantIndex::from(environment.entries().len().saturating_sub(1));
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let reduced = word(arena, &[Letter::Loop]);
        let again = word(arena, &[Letter::Loop]);
        let declared = arena.value_type_path(own, reduced, again);
        let named = arena.value_constant(position);
        let staged = staging.def(LevelSignature::monomorphic(), declared, named);
        [reflexivity, environment.add_decl(staged).map(|_checked| ())]
    }

    #[test]
    fn the_forced_loop_converts_circle_words_by_their_normal_forms()
    {
        let mut presented = circle_environment(circle());
        let [reflexivity, _] = offer(&mut presented);
        assert_eq!(
            reflexivity,
            Ok(()),
            "`here(loop(base))` relates the word to its normal form with no dialogue"
        );
        let mut free = circle_environment(Presentation::default());
        let [reflexivity, _] = offer(&mut free);
        assert!(
            matches!(
                reflexivity,
                Err(KernelError::Identity(
                    crate::element_identity::IdentityError::EndpointsDiffer { .. }
                ))
            ),
            "the same words over a free circle are two terms: {reflexivity:?}"
        );
    }

    #[test]
    fn a_mode_switch_reads_circle_words_by_their_normal_forms()
    {
        let mut presented = circle_environment(circle());
        assert_eq!(
            offer(&mut presented),
            [Ok(()), Ok(())],
            "the constant's path type and its declared one meet once both are normal"
        );
    }
}
