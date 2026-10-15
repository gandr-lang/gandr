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
//! own size. Confluence is not checked at admission. The normal form is taken
//! by one fixed strategy (`Presentation::normalize` names it), so conversion
//! is an equivalence and sound for the equational theory whether or not the
//! rules are confluent; confluence makes it complete, and the producer's
//! coincidence check is where a presentation's convergence is established for
//! conversion. The apartness rule below does not lean on it: it joins every
//! critical pair itself before it reads two normal forms as two elements.
//!
//! **Alternatives.** A recursive path order would admit size-preserving rules
//! such as associativity, at the price of a precedence in the trusted base. A
//! critical-pair check at admission would make conversion complete for every
//! admitted presentation, at the price of joining every overlap of every
//! presented type, used or not. **Reversal.** The first presented type whose
//! rules preserve size takes a path order; the first conversion the fixed
//! strategy separates though the theory equates moves the critical-pair check
//! of [`apart`] to admission.
//!
//! # Apartness
//!
//! A case of no branches over a scrutinee of the path type `Path(A, a, b)`,
//! `A` a data type, is admitted at any motive exactly when `a` and `b` are
//! apart ([`apart`]): the rules of `A` converge — every critical pair joins,
//! so with the termination admission establishes each term has one normal
//! form, and two terms are equal exactly when their normal forms are — and the
//! two normal forms, holding no subterm of `A` that is not a constructor,
//! first differ at two constructors with distinct tags. A free type is the
//! case with no rule, and the rule is constructor disjointness; the words of a
//! looped point are a presented type like any other, so `loop` and the empty
//! word are apart at the circle's loop space. The decision is the kernel's own
//! over the admitted declaration: the certificate is the case itself, with no
//! new node and no recorded verdict, and a refusal names the reason
//! ([`KernelError::NotApart`]): the normal forms agree, differ only under a
//! leaf of another type, hold a subterm of `A` that is not a constructor, or
//! the rules diverge.
//!
//! **Alternative.** Apartness by decoding: a map from `A` into a type with its
//! own no-confusion (the circle's winding number into the integers) carries a
//! path between the endpoints to one between their images, and those are
//! apart. Each presented type then owes its decoding, and the decoding's
//! target, the integers, still needs this rule at its own constructors.
//! **Reversal.** The first apartness the rule cannot see — an endpoint that is
//! open at a constructor head, or a type whose identity is not decided by
//! normal form — takes decoding through a map the corpus defines.
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
use gandr_kernel_term::Apartness;
use gandr_kernel_term::CellFault;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Exhausted;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::Normalized;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleSlot;
use gandr_kernel_term::RuleTerm;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::TermReading;
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
    /// For a type of words, the field count of each constructor of the sort
    /// its cells loop in, in tag order: where a case over the sort keeps its
    /// loop arms, and how the cells' point builds.
    sort_arities: Option<Arc<[FieldCount]>>,
}

impl PresentedType
{
    /// The cells the presentation's words loop by, when it is a type of
    /// words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn cells(&self) -> Option<&FreeCells>
    {
        self.presentation.cells()
    }
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
                let sort_arities = declaration.presentation().cells().and_then(|cells| {
                    match *entries
                        .get(usize::from(cells.sort()))?
                        .declaration()
                        .content()
                    {
                        DeclarationContent::Data {
                            constructors: ref table,
                            ..
                        } => Some(
                            table
                                .iter()
                                .map(|fields| FieldCount::from(fields.len()))
                                .collect(),
                        ),
                        DeclarationContent::Def { .. }
                        | DeclarationContent::Axiom { .. }
                        | DeclarationContent::AbstractType { .. } => None,
                    }
                });
                let _previous = presented.insert(ConstantIndex::from(position), PresentedType {
                    presentation: declaration.presentation().clone(),
                    arities: constructors
                        .iter()
                        .map(|fields| FieldCount::from(fields.len()))
                        .collect(),
                    sort_arities,
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

    /// The types of words whose cells loop in the sort admitted at `sort`, by
    /// admission position ascending, each with its cells: the order a case
    /// over the sort keeps its loop arms in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn looping(
        &self,
        sort: ConstantIndex,
    ) -> impl Iterator<Item = (ConstantIndex, &FreeCells)>
    {
        self.0.iter().flat_map(move |table| {
            table.iter().filter_map(move |(&words, presented)| {
                presented
                    .presentation
                    .cells()
                    .filter(|cells| cells.sort() == sort)
                    .map(|cells| (words, cells))
            })
        })
    }

    /// The field counts of the constructors of the sort the type of words at
    /// `words` loops in, in tag order, when `words` is a type of words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn sort_arities(
        &self,
        words: ConstantIndex,
    ) -> Option<&[FieldCount]>
    {
        self.presented(words)?.sort_arities.as_deref()
    }

    /// The type of words the path type `Path(domain, left, right)` reads as:
    /// the one whose cells loop at a point both endpoints spell, over the
    /// parameterless data type `domain` names.
    ///
    /// # Specification
    /// - requires: nothing — unreadable ids read as no words.
    /// - ensures: `Some(words)` exactly when `domain` is a parameterless data
    ///   type, `words` a presented type whose cells are over it, and `left` and
    ///   `right` each a constructor term of that type spelling the cells'
    ///   point; admission keeps one type of words per point.
    /// - provides: the identification every reader of a path type shares: the
    ///   checking machine's fibre and case, and conversion at a mode switch.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop is a word checked at its path type,
    ///   a case over a path reads the words' table, and a path at another point
    ///   reads as no words.
    /// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
    #[spec(ensures: |ret| ret.is_none_or(|words| self.presented(words).is_some_and(|presented| presented.presentation.cells().is_some())))]
    #[must_use]
    pub(crate) fn words(
        &self,
        arena: &TermArena,
        domain: ValueTypeId,
        (left, right): (ValueId, ValueId),
    ) -> Option<ConstantIndex>
    {
        let table = self.0.as_ref()?;
        let Some(&ValueType::Data {
            declaration: sort,
            ref arguments,
        }) = arena.value_type(domain)
        else {
            return None;
        };
        if !arguments.is_empty() {
            return None;
        }
        table.iter().find_map(|(&words, presented)| {
            let cells = presented.presentation.cells()?;
            (cells.sort() == sort
                && spells(arena, sort, left, cells.point()) == Spelling::Spelled
                && spells(arena, sort, right, cells.point()) == Spelling::Spelled)
                .then_some(words)
        })
    }

    /// `ty`, or the data type of the words it reads as when it is a path type
    /// at a looped point ([`Self::words`]).
    ///
    /// # Specification
    /// - requires: `ty` lives in `arena`.
    /// - ensures: a fresh `Data(words, [])` exactly when `ty` is `Path(domain,
    ///   left, right)` and [`Self::words`] reads its parts as `words`; `ty`
    ///   itself otherwise.
    /// - provides: the checking machine's reading of a scrutinee's type and of
    ///   the identity a word checks at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::words`].
    /// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
    #[spec(ensures: |ret| ret == ty || matches!(arena.value_type(ret), Some(ValueType::Data { arguments, .. }) if arguments.is_empty()))]
    #[must_use]
    pub(crate) fn identified(
        &self,
        arena: &mut TermArena,
        ty: ValueTypeId,
    ) -> ValueTypeId
    {
        if let Some(&ValueType::Path {
            domain,
            left,
            right,
        }) = arena.value_type(ty)
            && let Some(words) = self.words(arena, domain, (left, right))
        {
            return arena.value_type_data(words, Vec::new());
        }
        ty
    }
}

/// Whether a value is the closed term a rule side spells.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spelling
{
    /// The value is the term the side spells.
    Spelled,
    /// It is another term, or no term the arena can read.
    Apart,
}

/// Whether `value` is the constructor term of `sort` that the closed rule side
/// `side` spells.
///
/// # Specification
/// - requires: nothing — unreadable ids spell nothing.
/// - ensures: [`Spelling::Spelled`] exactly when reading `value` in pre-order
///   meets one constructor of `sort` per node of `side`, each with the node's
///   tag, and no node is left over on either side; a variable node spells
///   nothing.
/// - provides: the endpoint comparison of [`Presentations::words`], bounded by
///   the side's length whatever the value's depth.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` loop over `side`'s nodes, not recursion.
/// - measure: the nodes of `side` not yet read.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentations::words`].
/// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
#[spec(ensures: |ret| ret == Spelling::Apart || !side.is_empty())]
fn spells(
    arena: &TermArena,
    sort: ConstantIndex,
    value: ValueId,
    side: &[RuleNode],
) -> Spelling
{
    let mut pending = Vec::with_capacity(side.len());
    pending.push(value);
    for &node in side {
        let (Some(at), RuleNode::Constructor(tag)) = (pending.pop(), node)
        else {
            return Spelling::Apart;
        };
        let Some(&Value::Constructor {
            datatype,
            tag: written,
            ref fields,
        }) = arena.value(at)
        else {
            return Spelling::Apart;
        };
        if written != tag
            || !matches!(
                arena.value_type(datatype),
                Some(&ValueType::Data { declaration, .. }) if declaration == sort
            )
        {
            return Spelling::Apart;
        }
        pending.extend(fields.iter().rev());
    }
    if pending.is_empty() {
        Spelling::Spelled
    }
    else {
        Spelling::Apart
    }
}

/// Check a data declaration's rules against its constructor table, and a type
/// of words's cells against the sort they loop in.
///
/// # Specification
/// - requires: `constructors` is the declaration's table, its field types in
///   `arena`, the declaration standing at `position` after `entries` and
///   binding the telescope `parameters`.
/// - ensures: `Ok(())` exactly when `presentation` validates against the table,
///   a field reading [`RuleSlot::Own`] where its type is the declaration's own
///   family and [`RuleSlot::Other`] with its type id elsewhere, and, when it
///   carries cells, [`words`] admits them.
/// - provides: the admission obligation of a presented type.
/// - fails: [`KernelError::WordsRefused`] naming the cells' fault, checked
///   first, or [`KernelError::RuleNotPresentable`] naming the first rule that
///   does not present the type and why.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's rules admit, a rule placing a constructor
///   under another type's field is refused by name, and the words of the
///   circle's loop admit where words with their rules dropped are refused.
/// - witness: `presented::tests::admission_reads_the_own_type_from_the_table`
/// - witness: `presented::tests::words_admit_only_as_their_cells_mint_them`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::RuleNotPresentable(_) | KernelError::WordsRefused(_))))]
pub(crate) fn admit(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    (position, parameters): (ConstantIndex, &[ValueTypeId]),
    constructors: &[Vec<ValueTypeId>],
    presentation: &Presentation,
) -> Result<(), KernelError>
{
    if let Some(cells) = presentation.cells() {
        words(
            arena,
            entries,
            (position, parameters),
            (constructors, presentation.rules()),
            cells,
        )
        .map_err(KernelError::WordsRefused)?;
    }
    if presentation.rules().is_empty() {
        return Ok(());
    }
    presentation
        .validate(&slot_table(arena, position, constructors))
        .map_err(KernelError::RuleNotPresentable)
}

/// Check a type of words against the cells it carries: re-mint the words and
/// compare.
///
/// # Specification
/// - requires: as [`admit`].
/// - ensures: `Ok(())` exactly when the cells' sort is a parameterless data
///   declaration among `entries`, [`FreeCells::validate`] admits the cells
///   against its table, the declaration binds no parameter and its table and
///   rules are the mint — the empty word with no field, then per cell a letter
///   and an inverse each over one field of the declaration's own type, and
///   [`FreeCells::cancellations`] — and no earlier type of words loops at the
///   same point of the same sort.
/// - provides: the kernel's whole trust in a type of words: the producer's
///   table and rules are a claim it re-derives, never reads.
/// - fails: [`CellFault::Sort`], a fault of [`FreeCells::validate`],
///   [`CellFault::NotMinted`] or [`CellFault::Twice`], in that order.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's loop admits, and its words refuse by name
///   with their rules dropped, at a sort admitted later, and a second time.
/// - witness: `presented::tests::words_admit_only_as_their_cells_mint_them`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CellFault::Sort | CellFault::Empty | CellFault::Endpoint(_) | CellFault::Open | CellFault::NotALoop | CellFault::Apart | CellFault::NotMinted | CellFault::Twice)))]
fn words(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    (position, parameters): (ConstantIndex, &[ValueTypeId]),
    (constructors, rules): (&[Vec<ValueTypeId>], &[PresentedRule]),
    cells: &FreeCells,
) -> Result<(), CellFault>
{
    let sort = cells.sort();
    let Some(content) = entries
        .get(usize::from(sort))
        .map(AdmittedDeclaration::content)
    else {
        return Err(CellFault::Sort);
    };
    let DeclarationContent::Data {
        parameters: ref sort_parameters,
        constructors: ref sort_table,
        ..
    } = *content
    else {
        return Err(CellFault::Sort);
    };
    if !sort_parameters.is_empty() {
        return Err(CellFault::Sort);
    }
    cells.validate(&slot_table(arena, sort, sort_table))?;
    let own = |field: &ValueTypeId| {
        matches!(
            arena.value_type(*field),
            Some(&ValueType::Data { declaration, ref arguments })
                if declaration == position && arguments.is_empty()
        )
    };
    let minted = parameters.is_empty()
        && constructors.len() == usize::from(cells.constructors())
        && constructors
            .iter()
            .enumerate()
            .all(|(tag, fields)| match *fields.as_slice() {
                [] => tag == 0,
                [ref field] => tag != 0 && own(field),
                _ => false,
            })
        && rules == cells.cancellations().as_slice();
    if !minted {
        return Err(CellFault::NotMinted);
    }
    if entries.iter().any(|entry| {
        entry
            .declaration()
            .presentation()
            .cells()
            .is_some_and(|earlier| earlier.sort() == sort && earlier.point() == cells.point())
    }) {
        return Err(CellFault::Twice);
    }
    Ok(())
}

/// A data declaration's constructor table as a rule side reads it.
///
/// # Specification
/// - requires: `constructors` is the declaration's table, its field types in
///   `arena`, the declaration standing at `position`.
/// - ensures: one row per constructor, one slot per field in order:
///   [`RuleSlot::Own`] where the field's type is the declaration's own family,
///   [`RuleSlot::Other`] with the field's type id elsewhere.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`].
/// - witness: `presented::tests::admission_reads_the_own_type_from_the_table`
#[spec(ensures: |ret| ret.len() == constructors.len())]
pub(crate) fn slot_table(
    arena: &TermArena,
    position: ConstantIndex,
    constructors: &[Vec<ValueTypeId>],
) -> Vec<Vec<RuleSlot<ValueTypeId>>>
{
    constructors
        .iter()
        .map(|fields| {
            fields
                .iter()
                .map(|&field| match arena.value_type(field) {
                    Some(&ValueType::Data { declaration, .. }) if declaration == position => {
                        RuleSlot::Own
                    },
                    _ => RuleSlot::Other(field),
                })
                .collect()
        })
        .collect()
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
        Some(&Value::Constructor { datatype, .. }) => matches!(
            arena.value_type(datatype),
            Some(&ValueType::Data { declaration: found, .. }) if found == declaration
        ),
        _ => false,
    };
    let mut term: Vec<RuleTerm<(ValueTypeId, Origin), ValueId>> = Vec::new();
    let mut pending = Vec::from([value]);
    while let Some(id) = pending.pop() {
        match arena.value(id) {
            Some(&Value::Constructor {
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
            _ => term.push(RuleTerm::Leaf(id)),
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
            RuleTerm::Leaf(id) => built.push(id),
            RuleTerm::Constructor {
                tag,
                arity,
                payload: (datatype, origin),
            } => {
                let mut fields = built.split_off(built.len().saturating_sub(usize::from(arity)));
                fields.reverse();
                let kept = match origin {
                    Origin::Written(id) => match arena.value(id) {
                        Some(&Value::Constructor {
                            fields: ref written,
                            ..
                        }) if *written == fields => Some(id),
                        _ => None,
                    },
                    Origin::Rewritten => None,
                };
                built.push(kept.unwrap_or_else(|| arena.value_constructor(datatype, tag, fields)));
            },
        }
    }
    Ok(built.pop().unwrap_or(value))
}

/// Decide whether `left` and `right`, two terms of the data type
/// `declaration` heads, are apart: the apartness rule a case of no branches
/// over their path type rests on.
///
/// # Specification
/// - requires: `left` and `right` live in `arena`, each a term of the data type
///   `declaration` heads.
/// - ensures: [`Presentation::apart`] over the declaration's own table and
///   rules — free when it presents none — of the two terms read by [`node`]:
///   each constructor of the declaration a constructor, each reference to an
///   admitted definition its body, every other value a leaf by its id.
/// - provides: the kernel's whole trust in an absurd case over a path: the
///   decision is re-derived from the admitted declarations and the endpoints,
///   and no certificate names a rewrite or a verdict.
/// - fails: [`KernelError::NotADataType`] when `declaration` names no admitted
///   data declaration.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `S(Z)` and `Z` over the integers are apart, `S(P(Z))` and
///   `Z` agree, a reference to a word is read as the word, and a free type's
///   distinct constructors are apart.
/// - witness: `presented::tests::endpoints_are_apart_by_their_normal_forms`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::NotADataType { .. })))]
pub(crate) fn apart(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    declaration: ConstantIndex,
    endpoints: (ValueId, ValueId),
) -> Result<Apartness, KernelError>
{
    let entry = entries
        .get(usize::from(declaration))
        .ok_or(KernelError::NotADataType { index: declaration })?;
    let DeclarationContent::Data {
        ref constructors, ..
    } = *entry.content()
    else {
        return Err(KernelError::NotADataType { index: declaration });
    };
    let table = slot_table(arena, declaration, constructors);
    Ok(entry
        .declaration()
        .presentation()
        .apart(&table, endpoints, |at, fields| {
            node(arena, entries, declaration, at, fields)
        }))
}

/// The node at `at` as a term of the data type `declaration` heads.
///
/// # Specification
/// - requires: nothing — an unreadable id is a leaf.
/// - ensures: [`TermReading::Constructor`] with its fields appended for a
///   constructor of `declaration`; [`TermReading::Defined`] with the body for a
///   reference to an admitted definition; [`TermReading::Other`] for every
///   other value. The checker reads its own arena alike.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`apart`].
/// - witness: `presented::tests::endpoints_are_apart_by_their_normal_forms`
#[spec(captures: before = fields.len(), ensures: |ret| matches!(ret, TermReading::Constructor(_)) || fields.len() == before)]
fn node(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    declaration: ConstantIndex,
    at: ValueId,
    fields: &mut Vec<ValueId>,
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
        Some(&Value::Constant(constant)) => {
            match entries
                .get(usize::from(constant))
                .map(AdmittedDeclaration::content)
            {
                Some(&DeclarationContent::Def { body, .. }) => TermReading::Defined(body),
                _ => TermReading::Other,
            }
        },
        _ => TermReading::Other,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::Apartness;
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
                Self::Base => 0_usize,
                Self::Loop => 1,
                Self::Unloop => 2,
                Self::Mark => 3,
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
            super::admit(
                &arena,
                &[],
                (ConstantIndex::from(0_usize), &[]),
                &table,
                &circle()
            ),
            Ok(())
        );
        let other = Presentation::new(alloc::vec![PresentedRule::new(
            [Letter::Mark.node(), Letter::Base.node()].into(),
            [Letter::Base.node()].into()
        )]);
        assert_eq!(
            super::admit(
                &arena,
                &[],
                (ConstantIndex::from(0_usize), &[]),
                &table,
                &other
            ),
            Err(KernelError::RuleNotPresentable(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: RuleFault::NotOwnPosition,
            }))
        );
        assert_eq!(
            super::admit(
                &arena,
                &[],
                (ConstantIndex::from(1_usize), &[]),
                &table,
                &circle()
            ),
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

    #[test]
    fn endpoints_are_apart_by_their_normal_forms()
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
        let _circle = environment
            .add_decl(staged)
            .expect("the circle admits with its rules");
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let free = staging
            .arena()
            .value_type_data(ConstantIndex::from(1_usize), Vec::new());
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![free], alloc::vec![free]],
            kind,
        );
        let _free = environment
            .add_decl(staged)
            .expect("the same table admits free");
        let mut staging = environment.stage();
        let circled = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let point = staging
            .arena()
            .value_constructor(circled, Letter::Base.tag(), Vec::new());
        let body = staging
            .arena()
            .value_constructor(circled, Letter::Loop.tag(), alloc::vec![point]);
        let staged = staging.def(LevelSignature::monomorphic(), circled, body);
        let _named = environment
            .add_decl(staged)
            .expect("a definition of `loop(base)` admits");
        let mut cloned = environment.arena().clone();
        let arena = &mut cloned;
        let base = arena.value_constructor(own, Letter::Base.tag(), Vec::new());
        let looped = arena.value_constructor(own, Letter::Loop.tag(), alloc::vec![base]);
        let unlooped = arena.value_constructor(own, Letter::Unloop.tag(), alloc::vec![looped]);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let open = arena.value_constructor(own, Letter::Loop.tag(), alloc::vec![variable]);
        let entries = environment.entries();
        let circle = ConstantIndex::from(0_usize);
        assert_eq!(
            super::apart(arena, entries, circle, (looped, base)),
            Ok(Apartness::Apart)
        );
        assert_eq!(
            super::apart(arena, entries, circle, (unlooped, base)),
            Ok(Apartness::Agree),
            "`unloop(loop(base))` is `base` by the declaration's rules"
        );
        assert_eq!(
            super::apart(arena, entries, circle, (open, base)),
            Ok(Apartness::Open)
        );
        let named = arena.value_constant(ConstantIndex::from(2_usize));
        assert_eq!(
            super::apart(arena, entries, circle, (named, base)),
            Ok(Apartness::Apart),
            "a reference to `loop(base)` is read as its definition"
        );
        let free_base = arena.value_constructor(free, Letter::Base.tag(), Vec::new());
        let free_looped = arena.value_constructor(free, Letter::Loop.tag(), alloc::vec![free_base]);
        let free_unlooped =
            arena.value_constructor(free, Letter::Unloop.tag(), alloc::vec![free_looped]);
        assert_eq!(
            super::apart(
                arena,
                entries,
                ConstantIndex::from(1_usize),
                (free_unlooped, free_base)
            ),
            Ok(Apartness::Apart),
            "without rules nothing cancels"
        );
        assert_eq!(
            super::apart(arena, entries, ConstantIndex::from(9_usize), (base, base)),
            Err(KernelError::NotADataType {
                index: ConstantIndex::from(9_usize)
            })
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

    /// `base` as a closed rule side.
    ///
    /// # Specification
    /// trivial.
    fn base() -> alloc::boxed::Box<[RuleNode]>
    {
        [Letter::Base.node()].into()
    }

    /// One loop at `base` of the sort at `sort`.
    ///
    /// # Specification
    /// trivial.
    fn looped(sort: ConstantIndex) -> gandr_kernel_term::FreeCells
    {
        gandr_kernel_term::FreeCells::new(sort, alloc::vec![gandr_kernel_term::FreeCell::new(
            base(),
            base()
        )])
    }

    /// An environment holding the one-point sort `base` at position zero.
    ///
    /// # Specification
    /// trivial.
    fn point() -> Environment
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![]],
            kind,
        );
        let _sort = environment
            .add_decl(staged)
            .expect("a one-point sort admits");
        environment
    }

    /// Stage the words of one loop's table, presented by `presentation`.
    ///
    /// # Specification
    /// trivial.
    fn words(
        environment: &mut Environment,
        presentation: Presentation,
    ) -> Result<ConstantIndex, KernelError>
    {
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging.arena().value_type_data(position, Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        environment
            .add_decl(staged)
            .map(crate::env::CheckedId::position)
    }

    #[test]
    fn words_admit_only_as_their_cells_mint_them()
    {
        use gandr_kernel_term::CellFault;

        let mut environment = point();
        assert_eq!(
            words(
                &mut environment,
                Presentation::new(Vec::new()).carrying(looped(ConstantIndex::from(0_usize)))
            ),
            Err(KernelError::WordsRefused(CellFault::NotMinted)),
            "words whose cancellations were dropped are not the words their cell mints"
        );
        assert_eq!(
            words(
                &mut environment,
                Presentation::new(circle().rules()[.. 1].to_vec())
                    .carrying(looped(ConstantIndex::from(0_usize)))
            ),
            Err(KernelError::WordsRefused(CellFault::NotMinted)),
            "nor are words with one cancellation of two"
        );
        assert_eq!(
            words(
                &mut environment,
                Presentation::words(looped(ConstantIndex::from(1_usize)))
            ),
            Err(KernelError::WordsRefused(CellFault::Sort)),
            "the sort must be admitted before the words"
        );
        let unknown = gandr_kernel_term::FreeCells::new(ConstantIndex::from(0_usize), alloc::vec![
            gandr_kernel_term::FreeCell::new(
                [Letter::Loop.node(), Letter::Base.node()].into(),
                [Letter::Loop.node(), Letter::Base.node()].into(),
            )
        ]);
        assert_eq!(
            words(&mut environment, Presentation::words(unknown)),
            Err(KernelError::WordsRefused(CellFault::Endpoint(
                RuleFault::UnknownConstructor
            ))),
            "a point the sort's table does not spell"
        );
        assert_eq!(
            words(
                &mut environment,
                Presentation::words(looped(ConstantIndex::from(0_usize)))
            ),
            Ok(ConstantIndex::from(1_usize)),
            "the words the loop at `base` mints admit"
        );
        assert_eq!(
            words(
                &mut environment,
                Presentation::words(looped(ConstantIndex::from(0_usize)))
            ),
            Err(KernelError::WordsRefused(CellFault::Twice)),
            "one type of words per point"
        );
    }

    #[test]
    fn a_path_at_a_looped_point_reads_as_its_words()
    {
        let mut environment = point();
        let words_at = words(
            &mut environment,
            Presentation::words(looped(ConstantIndex::from(0_usize))),
        )
        .expect("the loop's words admit");
        let sort = ConstantIndex::from(0_usize);
        let presentations = super::Presentations::of(environment.entries());
        let mut arena = environment.arena().clone();
        let carrier = arena.value_type_data(sort, Vec::new());
        let point = arena.value_constructor(carrier, Letter::Base.tag(), Vec::new());
        let again = arena.value_constructor(carrier, Letter::Base.tag(), Vec::new());
        let open = arena.value_variable(DeBruijnIndex::from(0_u32));
        let word_type = arena.value_type_data(words_at, Vec::new());
        assert_eq!(
            presentations.words(&arena, carrier, (point, again)),
            Some(words_at)
        );
        assert_eq!(
            presentations.words(&arena, carrier, (point, open)),
            None,
            "an endpoint that is no constructor term spells no point"
        );
        assert_eq!(
            presentations.words(&arena, word_type, (point, again)),
            None,
            "no cell loops in the words themselves"
        );
        let path = arena.value_type_path(carrier, point, again);
        let identified = presentations.identified(&mut arena, path);
        assert!(matches!(
            arena.value_type(identified),
            Some(&gandr_kernel_term::ValueType::Data { declaration, .. }) if declaration == words_at
        ));

        // `loop : Path(S, base, base)`, the word of one letter.
        let path_at = |arena: &mut TermArena| {
            let carrier = arena.value_type_data(sort, Vec::new());
            let point = arena.value_constructor(carrier, Letter::Base.tag(), Vec::new());
            arena.value_type_path(carrier, point, point)
        };
        let mut staging = environment.stage();
        let arena = staging.arena();
        let declared = path_at(arena);
        let words = arena.value_type_data(words_at, Vec::new());
        let empty = arena.value_constructor(words, ConstructorTag::from(0_usize), Vec::new());
        let letter =
            arena.value_constructor(words, ConstructorTag::from(1_usize), alloc::vec![empty]);
        let staged = staging.def(LevelSignature::monomorphic(), declared, letter);
        let loop_at = environment
            .add_decl(staged)
            .expect("a word checks at the path of its point")
            .position();

        // The constant read back at the words' own type.
        let mut staging = environment.stage();
        let arena = staging.arena();
        let declared = arena.value_type_data(words_at, Vec::new());
        let named = arena.value_constant(loop_at);
        let staged = staging.def(LevelSignature::monomorphic(), declared, named);
        assert!(
            environment.add_decl(staged).is_ok(),
            "a path at the looped point converts with its words at a mode switch"
        );

        // `fix f. λp. case p { here ⇒ return here; g ∷ q ⇒ r ← f(q); return
        // g ∷ r; … }` at `Path(S, base, base) → F Path(S, base, base)`: a case
        // over a path splits its words, and each cancellation is respected.
        let mut staging = environment.stage();
        let arena = staging.arena();
        let path = path_at(arena);
        let words = arena.value_type_data(words_at, Vec::new());
        let motive = arena.comp_type_returner(path);
        let empty = arena.value_constructor(words, ConstructorTag::from(0_usize), Vec::new());
        let nil = arena.computation_return(empty);
        let mut arm = |tag: usize| {
            let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let folded = arena.computation_application(forced, field);
            let result = arena.value_variable(DeBruijnIndex::from(0_u32));
            let rebuilt =
                arena.value_constructor(words, ConstructorTag::from(tag), alloc::vec![result]);
            let returned = arena.computation_return(rebuilt);
            let sequenced = arena.computation_bind(folded, returned);
            arena.computation_lambda(sequenced)
        };
        let letter = arm(1);
        let inverse = arm(2);
        let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(argument, motive, alloc::vec![nil, letter, inverse]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let body = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(path, motive);
        let declared = arena.value_type_thunk(arrow);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        assert_eq!(
            environment.add_decl(staged).map(|_admitted| ()),
            Ok(()),
            "the identity fold over the words respects both cancellations"
        );
    }
}
