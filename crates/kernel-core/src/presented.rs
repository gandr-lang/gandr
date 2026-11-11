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
//! A case of no branches over a scrutinee of the path type `Path[.A = A](a,
//! b)`, `A` a data type, is admitted at any motive exactly when `a` and `b` are
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
use gandr_kernel_term::Reflexivities;
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
use crate::env::Entries;
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

/// The presented types of an environment, by admission position, and the
/// types of words over each sort.
///
/// # Specification
/// - provides: the rule table every conversion of the environment's terms
///   reads, and the registry that joins a sort's types of words to a check's
///   support; empty, and free to build and clone, while no admitted declaration
///   presents its type. The environment adds a row at each presented admission,
///   so no reading walks the entries.
/// - panics: none.
/// - executable: none — data declaration; lookup is its observer.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Presentations(Option<Arc<Table>>);

/// The rows of [`Presentations`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Table
{
    /// Each presented type, by admission position.
    types: BTreeMap<ConstantIndex, PresentedType>,
    /// The types of words whose cells loop in each sort, by admission
    /// position ascending.
    words: BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
}

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
    ///   every replay over the environment; the environment keeps it, so this
    ///   reads no entry.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`normal_form`].
    /// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
    #[spec(ensures: |ret| ret.0.as_ref().is_none_or(|table| !table.types.is_empty() && table.types.len() <= usize::from(entries.len())))]
    #[inline]
    #[must_use]
    pub fn of(entries: &Entries) -> Self
    {
        entries.presentations().clone()
    }

    /// These presentations and the declaration admitted at `position`, when
    /// it presents its type; `sort` is the constructor table of the sort its
    /// cells loop in, for a type of words.
    ///
    /// # Specification
    /// - requires: `position` is past every position these presentations hold.
    /// - ensures: the declaration's row, with its rules and arities, when it is
    ///   a data declaration whose presentation holds a rule, and its row in the
    ///   registry of its sort when it is a type of words; nothing changes
    ///   otherwise.
    /// - provides: the one change the environment makes at an admission.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   admission, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`normal_form`].
    /// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
    pub(crate) fn admit(
        &mut self,
        position: ConstantIndex,
        declaration: &gandr_kernel_term::Declaration,
        sort: Option<&[Vec<ValueTypeId>]>,
    )
    {
        if declaration.presentation().rules().is_empty() {
            return;
        }
        let DeclarationContent::Data {
            ref constructors, ..
        } = *declaration.content()
        else {
            return;
        };
        let arities = |table: &[Vec<ValueTypeId>]| -> Arc<[FieldCount]> {
            table
                .iter()
                .map(|fields| FieldCount::from(fields.len()))
                .collect()
        };
        let table = Arc::make_mut(self.0.get_or_insert_with(Arc::default));
        if let Some(cells) = declaration.presentation().cells() {
            table.words.entry(cells.sort()).or_default().push(position);
        }
        let _previous = table.types.insert(position, PresentedType {
            presentation: declaration.presentation().clone(),
            arities: arities(constructors),
            sort_arities: declaration.presentation().cells().and(sort).map(arities),
        });
    }

    /// These presentations without the rows from `first` on: those of the
    /// members a refused block admitted.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn forget_from(
        &mut self,
        first: ConstantIndex,
    )
    {
        let Some(shared) = self.0.as_mut()
        else {
            return;
        };
        if shared.types.range(first ..).next().is_none() {
            return;
        }
        let table = Arc::make_mut(shared);
        let _forgotten = table.types.split_off(&first);
        table.words.retain(|_, words| {
            words.retain(|&held| held < first);
            !words.is_empty()
        });
        if table.types.is_empty() {
            self.0 = None;
        }
    }

    /// The types of words whose cells loop in the sort at `sort`, by
    /// admission position ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn over(
        &self,
        sort: ConstantIndex,
    ) -> &[ConstantIndex]
    {
        self.0
            .as_deref()
            .and_then(|table| table.words.get(&sort))
            .map_or(&[], Vec::as_slice)
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
        self.0.as_deref()?.types.get(&constant)
    }

    /// The types of words whose cells loop in the sort admitted at `sort`, by
    /// admission position ascending, each with its cells: the order a case
    /// over the sort keeps its loop arms in. Cells above dimension one loop
    /// at the point's reflexivity, and a case keeps an arm for them too.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn looping(
        &self,
        sort: ConstantIndex,
    ) -> impl Iterator<Item = (ConstantIndex, &FreeCells)>
    {
        self.over(sort).iter().filter_map(move |&words| {
            self.presented(words)
                .and_then(PresentedType::cells)
                .map(|cells| (words, cells))
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

    /// The type of words the path type `Path[.A = domain](left, right)` reads
    /// as: the one whose cells loop at a point both endpoints spell, over
    /// the parameterless data type `domain` names. Cells above dimension one
    /// loop at the point wrapped in its reflexivity: `domain` is then itself a
    /// path type at the wrapped point, down to the data type.
    ///
    /// # Specification
    /// - requires: nothing — unreadable ids read as no words.
    /// - ensures: `Some(words)` exactly when `domain` reads through `n` path
    ///   types down to a parameterless data type, the endpoints at each path
    ///   type are the point wrapped once less than at the one above it and `n`
    ///   times at `left` and `right`, `words` a presented type whose cells are
    ///   over it wrapped `n` times, and every unwrapped endpoint a constructor
    ///   term of that type spelling the cells' point; admission keeps one type
    ///   of words per point and wrapping.
    /// - provides: the identification every reader of a path type shares: the
    ///   checking machine's fibre and case, and conversion at a mode switch.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop is a word checked at its path type,
    ///   a case over a path reads the words' table, and a path at another point
    ///   reads as no words; the sphere's path at the reflexivity of its point
    ///   reads as the words of its 2-cell.
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
        let (sort, wrapped) = tower(arena, domain, (left, right))?;
        self.looping(sort).find_map(|(words, cells)| {
            (cells.reflexivities() == wrapped
                && spelled_along(arena, sort, domain, (left, right), cells.point())
                    == Spelling::Spelled)
                .then_some(words)
        })
    }

    /// `ty`, or the data type of the words it reads as when it is a path type
    /// at a looped point ([`Self::words`]).
    ///
    /// # Specification
    /// - requires: `ty` lives in `arena`.
    /// - ensures: a fresh `Data(words, [])` exactly when `ty` is `Path[.A =
    ///   domain]( left, right)` and [`Self::words`] reads its parts as `words`;
    ///   `ty` itself otherwise.
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

    /// The types of words, by admission position ascending, each with its
    /// cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn worded(&self) -> impl Iterator<Item = (ConstantIndex, &FreeCells)>
    {
        self.0.iter().flat_map(|table| {
            table.types.iter().filter_map(|(&words, presented)| {
                presented.presentation.cells().map(|cells| (words, cells))
            })
        })
    }

    /// The type of words whose empty word a reflexivity at `base`, wrapped
    /// `wraps` times, is.
    ///
    /// # Specification
    /// - requires: nothing — unreadable ids read as no words.
    /// - ensures: `Some(words)` exactly when `base` is a constructor term of a
    ///   sort `s` and `words` the first presented type, by admission position,
    ///   whose cells loop in `s` wrapped `wraps` times at a point `base`
    ///   spells; admission keeps one type of words per point and wrapping.
    /// - provides: the value half of [`Self::words`]: the reading of
    ///   `Replay::present` at a reflexivity, as `syntax::empty_word` in
    ///   core-term compares it and the evaluator's `presented::normal_form`
    ///   reads it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's base at no wrapping and the sphere's
    ///   base at one wrapping read as their words; a point the cells do not
    ///   spell, and a wrapping no cells carry, read as no words.
    /// - witness: `replay::tests::a_reflexivity_at_a_looped_point_presents_as_its_empty_word_6477`
    #[spec(ensures: |ret| ret.is_none_or(|words| self.presented(words).is_some_and(|presented| presented.presentation.cells().is_some_and(|cells| cells.reflexivities() == wraps))))]
    #[must_use]
    pub(crate) fn emptied(
        &self,
        arena: &TermArena,
        base: ValueId,
        wraps: Reflexivities,
    ) -> Option<ConstantIndex>
    {
        let &Value::Constructor { datatype, .. } = arena.value(base)?
        else {
            return None;
        };
        let &ValueType::Data {
            declaration: sort, ..
        } = arena.value_type(datatype)?
        else {
            return None;
        };
        self.looping(sort)
            .find(|&(_, cells)| {
                cells.reflexivities() == wraps
                    && spells(arena, sort, base, cells.point()) == Spelling::Spelled
            })
            .map(|(words, _)| words)
    }
}

/// The sort a path type's domain reads down to, and how many path types it
/// passes on the way.
///
/// # Specification
/// - requires: nothing — unreadable ids read as no tower.
/// - ensures: `Some((sort, n))` exactly when `domain` reads through `n` path
///   types down to `Data(sort, [])`, and the endpoints at each level are
///   wrapped in reflexivity once less than the level above, `n` times at the
///   outer endpoints `left` and `right`.
/// - provides: the shape half of [`Presentations::words`]; [`spelled_along`]
///   reads the bases.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` reads one path type of the domain per turn.
/// - measure: the path types left in the domain, each a strict part of the one
///   above it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentations::words`].
/// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
#[spec(ensures: |ret| ret.is_none_or(|(_, levels)| unwrapped(arena, left).1 == levels && unwrapped(arena, right).1 == levels))]
fn tower(
    arena: &TermArena,
    domain: ValueTypeId,
    (left, right): (ValueId, ValueId),
) -> Option<(ConstantIndex, Reflexivities)>
{
    let (mut domain, mut ends) = (domain, (left, right));
    let mut wraps = None;
    let mut levels = 0_usize;
    loop {
        let (_, left_wraps) = unwrapped(arena, ends.0);
        let (_, right_wraps) = unwrapped(arena, ends.1);
        if left_wraps != right_wraps {
            return None;
        }
        // Each level's endpoints are wrapped once less than the level above.
        let count = usize::from(left_wraps);
        if let Some(above) = wraps
            && count.checked_add(1) != Some(above)
        {
            return None;
        }
        wraps = Some(count);
        let ty = arena.value_type(domain)?;
        if let ValueType::Data {
            declaration,
            ref arguments,
        } = *ty
            && arguments.is_empty()
            && left_wraps == Reflexivities::NONE
        {
            return Some((declaration, Reflexivities::from(levels)));
        }
        let ValueType::Path {
            domain: inner,
            left,
            right,
        } = *ty
        else {
            return None;
        };
        domain = inner;
        ends = (left, right);
        levels = levels.checked_add(1)?;
    }
}

/// Whether every endpoint along the domain [`tower`] reads, unwrapped, spells
/// `point` over `sort`.
///
/// # Specification
/// - requires: [`tower`] reads `domain` and the endpoints down to `sort`.
/// - ensures: [`Spelling::Spelled`] exactly when each endpoint's base spells
///   `point`.
/// - provides: the point half of [`Presentations::words`].
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: as [`tower`].
/// - measure: as [`tower`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentations::words`].
/// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
#[spec(ensures: |ret| ret == Spelling::Apart || spells(arena, sort, unwrapped(arena, left).0, point) == Spelling::Spelled)]
fn spelled_along(
    arena: &TermArena,
    sort: ConstantIndex,
    domain: ValueTypeId,
    (left, right): (ValueId, ValueId),
    point: &[RuleNode],
) -> Spelling
{
    let (mut domain, mut ends) = (domain, (left, right));
    loop {
        let spelled =
            |end: ValueId| spells(arena, sort, unwrapped(arena, end).0, point) == Spelling::Spelled;
        if !spelled(ends.0) || !spelled(ends.1) {
            return Spelling::Apart;
        }
        match arena.value_type(domain) {
            Some(&ValueType::Path {
                domain: inner,
                left,
                right,
            }) => {
                domain = inner;
                ends = (left, right);
            },
            Some(_) | None => return Spelling::Spelled,
        }
    }
}

/// `value` with every reflexivity around it taken off, and how many there
/// were.
///
/// # Specification
/// - requires: nothing — an unreadable id is its own base.
/// - ensures: `(base, n)` with `value` the base wrapped `n` times in `here(_)`,
///   and the base no reflexivity.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` takes one reflexivity off per turn.
/// - measure: the reflexivities left, each a strict part of the one around it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentations::words`].
/// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
#[spec(ensures: |ret| !matches!(arena.value(ret.0), Some(&Value::Here { .. })))]
pub(crate) fn unwrapped(
    arena: &TermArena,
    value: ValueId,
) -> (ValueId, Reflexivities)
{
    let (mut base, mut wraps) = (value, 0_usize);
    while let Some(&Value::Here { point, .. }) = arena.value(base) {
        base = point;
        wraps = wraps.saturating_add(1);
    }
    (base, Reflexivities::from(wraps))
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
            ..
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
    entries: &Entries,
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
///   same point of the same sort, wrapped as many times in its reflexivity.
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
    entries: &Entries,
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
    // The registry holds every earlier type of words over the sort, so no
    // walk over the entries is needed.
    if entries.presentations().looping(sort).any(|(_, earlier)| {
        earlier.point() == cells.point() && earlier.reflexivities() == cells.reflexivities()
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
///   [`RuleSlot::Dependent`] where the field follows its constructor's first
///   and its type reaches a binder — formed under the fields before it as well
///   as the parameters — and [`RuleSlot::Other`] with the field's type id
///   elsewhere.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`], and a pair over a parameter reads its
///   second field as dependent.
/// - witness: `presented::tests::admission_reads_the_own_type_from_the_table`
/// - witness: `presented::tests::a_pair_over_a_parameter_reads_its_second_field_as_dependent`
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
                .enumerate()
                .map(|(index, &field)| match arena.value_type(field) {
                    Some(&ValueType::Data { declaration, .. }) if declaration == position => {
                        RuleSlot::Own
                    },
                    _ if index != 0
                        && arena.value_type_support(field).depth()
                            != gandr_kernel_term::LooseDepth::default() =>
                    {
                        RuleSlot::Dependent
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
                ..
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
                let start = built.len().saturating_sub(usize::from(arity));
                let fields: Vec<ValueId> = built.drain(start ..).rev().collect();
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
                built.push(kept.unwrap_or_else(|| {
                    arena.value_constructor(declaration, datatype, tag, fields)
                }));
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
    entries: &Entries,
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
    entries: &Entries,
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
            ..
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
    use gandr_kernel_term::RuleSlot;
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
                &crate::env::NO_ENTRIES,
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
                &crate::env::NO_ENTRIES,
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
                &crate::env::NO_ENTRIES,
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
    fn a_pair_over_a_parameter_reads_its_second_field_as_dependent()
    {
        // `Pair(a) { mk : (x : El a, y : El a) }`: the first field reads `a`
        // at index 0, the second past the first's binder at index 1, so only
        // the first has a classifier of its own.
        let mut arena = TermArena::new();
        let first = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = arena.value_variable(DeBruijnIndex::from(1_u32));
        let head = arena.value_type_element(first, Level::zero());
        let tail = arena.value_type_element(second, Level::zero());
        let unit = arena.value_type_unit();
        assert_eq!(
            super::slot_table(&arena, ConstantIndex::from(0_usize), &[
                alloc::vec![head, tail],
                alloc::vec![head, unit]
            ],),
            alloc::vec![
                alloc::vec![RuleSlot::Other(head), RuleSlot::Dependent],
                alloc::vec![RuleSlot::Other(head), RuleSlot::Other(unit)],
            ],
            "an open field after the first is dependent, a closed one keeps its classifier"
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
        let written = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Loop.tag(),
            alloc::vec![variable],
        );
        let unlooped = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Unloop.tag(),
            alloc::vec![written],
        );
        let word = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Loop.tag(),
            alloc::vec![unlooped],
        );
        let mut fuel = RewriteFuel::from(1_000_u64);
        let normal = super::normal_form(arena, &presentations, word, &mut fuel)
            .expect("the word normalizes within its fuel");
        assert!(
            matches!(
                arena.value(normal),
                Some(gandr_kernel_term::Value::Constructor { datatype, tag, fields, .. })
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
        let looped = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Loop.tag(),
            alloc::vec![written],
        );
        let cancelled = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Unloop.tag(),
            alloc::vec![looped],
        );
        assert_eq!(
            super::normal_form(arena, &presentations, cancelled, &mut fuel),
            Ok(written),
            "`unloop(loop(w))` is `w` itself: a written constructor the rewriting \
             left whole keeps its id"
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
        let point = staging.arena().value_constructor(
            ConstantIndex::from(0_usize),
            circled,
            Letter::Base.tag(),
            Vec::new(),
        );
        let body = staging.arena().value_constructor(
            ConstantIndex::from(0_usize),
            circled,
            Letter::Loop.tag(),
            alloc::vec![point],
        );
        let staged = staging.def(LevelSignature::monomorphic(), circled, body);
        let _named = environment
            .add_decl(staged)
            .expect("a definition of `loop(base)` admits");
        let mut cloned = environment.arena().clone();
        let arena = &mut cloned;
        let base = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Base.tag(),
            Vec::new(),
        );
        let looped = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Loop.tag(),
            alloc::vec![base],
        );
        let unlooped = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Unloop.tag(),
            alloc::vec![looped],
        );
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let open = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Loop.tag(),
            alloc::vec![variable],
        );
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
        let free_base = arena.value_constructor(
            ConstantIndex::from(1_usize),
            free,
            Letter::Base.tag(),
            Vec::new(),
        );
        let free_looped = arena.value_constructor(
            ConstantIndex::from(1_usize),
            free,
            Letter::Loop.tag(),
            alloc::vec![free_base],
        );
        let free_unlooped = arena.value_constructor(
            ConstantIndex::from(1_usize),
            free,
            Letter::Unloop.tag(),
            alloc::vec![free_looped],
        );
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
        let mut built = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Base.tag(),
            Vec::new(),
        );
        for &letter in letters.iter().rev() {
            built = arena.value_constructor(
                ConstantIndex::from(0_usize),
                own,
                letter.tag(),
                alloc::vec![built],
            );
        }
        built
    }

    /// Offer `here(loop(base))` at `Path[.A = Circle](loop(unloop(loop(base))),
    /// loop(base))`, then a constant naming it at `Path[.A =
    /// Circle](loop(base), loop(base))`.
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
        let position =
            ConstantIndex::from(usize::from(environment.entries().len()).saturating_sub(1));
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
    fn words_refuse_another_table_and_admit_one_type_per_point()
    {
        use gandr_kernel_term::CellFault;

        /// Stage the words of the loop at `point` over the table `fields`
        /// names, `None` a field of the declaration's own type.
        ///
        /// # Specification
        /// trivial.
        fn stage(
            environment: &mut Environment,
            table: &[&[Option<()>]],
            point: ConstructorTag,
        ) -> Result<ConstantIndex, KernelError>
        {
            let position = ConstantIndex::from(environment.entries().len());
            let mut staging = environment.stage();
            let arena = staging.arena();
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let own = arena.value_type_data(position, Vec::new());
            let unit = arena.value_type_unit();
            let table = table
                .iter()
                .map(|fields| {
                    fields
                        .iter()
                        .map(|field| field.map_or(own, |()| unit))
                        .collect()
                })
                .collect();
            let at: alloc::boxed::Box<[RuleNode]> = [RuleNode::Constructor(point)].into();
            let cells =
                gandr_kernel_term::FreeCells::new(ConstantIndex::from(0_usize), alloc::vec![
                    gandr_kernel_term::FreeCell::new(at.clone(), at)
                ]);
            let staged = staging
                .data(LevelSignature::monomorphic(), Vec::new(), table, kind)
                .presented(Presentation::words(cells));
            environment
                .add_decl(staged)
                .map(crate::env::CheckedId::position)
        }

        // A sort of two points.
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![]],
            kind,
        );
        let _sort = environment
            .add_decl(staged)
            .expect("a two-point sort admits");
        let [first, second] = [0_usize, 1_usize].map(ConstructorTag::from);
        for (table, what) in [
            (
                [&[None][..], &[None], &[None]],
                "an empty word over a field",
            ),
            (
                [&[][..], &[Some(())], &[None]],
                "a letter over another type",
            ),
        ] {
            assert_eq!(
                stage(&mut environment, &table, first),
                Err(KernelError::WordsRefused(CellFault::NotMinted)),
                "{what} is not the mint"
            );
        }
        let minted: [&[Option<()>]; 3] = [&[], &[None], &[None]];
        assert!(stage(&mut environment, &minted, first).is_ok());
        assert!(
            stage(&mut environment, &minted, second).is_ok(),
            "the same sort's other point takes its own words"
        );
        assert_eq!(
            stage(&mut environment, &minted, second),
            Err(KernelError::WordsRefused(CellFault::Twice))
        );
    }

    #[test]
    fn a_side_spells_only_its_own_sort_s_tags()
    {
        let mut arena = TermArena::new();
        let sort = ConstantIndex::from(0_usize);
        let own = arena.value_type_data(sort, Vec::new());
        let other = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
        let side = [Letter::Loop.node(), Letter::Base.node()];
        let word = |arena: &mut TermArena, (family, datatype), tag: Letter| {
            let base = arena.value_constructor(sort, own, Letter::Base.tag(), Vec::new());
            arena.value_constructor(family, datatype, tag.tag(), alloc::vec![base])
        };
        let spelled = word(&mut arena, (sort, own), Letter::Loop);
        assert_eq!(
            super::spells(&arena, sort, spelled, &side),
            super::Spelling::Spelled
        );
        for (value, what) in [
            (
                word(
                    &mut arena,
                    (ConstantIndex::from(1_usize), other),
                    Letter::Loop,
                ),
                "the tag over another sort",
            ),
            (
                word(&mut arena, (sort, own), Letter::Unloop),
                "another tag over the sort",
            ),
        ] {
            assert_eq!(
                super::spells(&arena, sort, value, &side),
                super::Spelling::Apart,
                "{what} spells nothing"
            );
        }
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
        let point = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
        let again = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
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

        // `loop : Path[.A = S](base, base)`, the word of one letter.
        let path_at = |arena: &mut TermArena| {
            let carrier = arena.value_type_data(sort, Vec::new());
            let point = arena.value_constructor(sort, carrier, Letter::Base.tag(), Vec::new());
            arena.value_type_path(carrier, point, point)
        };
        let mut staging = environment.stage();
        let arena = staging.arena();
        let declared = path_at(arena);
        let words = arena.value_type_data(words_at, Vec::new());
        let empty =
            arena.value_constructor(words_at, words, ConstructorTag::from(0_usize), Vec::new());
        let letter =
            arena.value_constructor(words_at, words, ConstructorTag::from(1_usize), alloc::vec![
                empty
            ]);
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
        // g ∷ r; … }` at `Path[.A = S](base, base) → F Path[.A = S](base, base)`: a
        // case over a path splits its words, and each cancellation is
        // respected.
        let mut staging = environment.stage();
        let arena = staging.arena();
        let path = path_at(arena);
        let words = arena.value_type_data(words_at, Vec::new());
        let motive = arena.comp_type_returner(path);
        let empty =
            arena.value_constructor(words_at, words, ConstructorTag::from(0_usize), Vec::new());
        let nil = arena.computation_return(empty);
        let mut arm = |tag: usize| {
            let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let folded = arena.computation_application(forced, field);
            let result = arena.value_variable(DeBruijnIndex::from(0_u32));
            let rebuilt =
                arena.value_constructor(words_at, words, ConstructorTag::from(tag), alloc::vec![
                    result
                ]);
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

    #[test]
    fn a_path_that_computes_its_point_is_set_aside_against_its_words_5099()
    {
        // `Path(S, x, x)` against the words at `base`: neither endpoint spells
        // the point, so the walk sets the pair aside for its reader, in either
        // order. A path over a type the words do not loop in stays apart.
        let mut environment = point();
        let words_at = words(
            &mut environment,
            Presentation::words(looped(ConstantIndex::from(0_usize))),
        )
        .expect("the loop's words admit");
        let presentations = super::Presentations::of(environment.entries());
        let mut arena = environment.arena().clone();
        let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let open = arena.value_variable(DeBruijnIndex::from(0_u32));
        let path = arena.value_type_path(carrier, open, open);
        let word_type = arena.value_type_data(words_at, Vec::new());
        for (one, other) in [(word_type, path), (path, word_type)] {
            let mut pending = Vec::new();
            assert_eq!(
                crate::conv::pending_endpoints(
                    &arena,
                    &presentations,
                    crate::conv::ConversionGoal::ValueType(one, other),
                    &mut pending
                ),
                crate::conv::Convertibility::Convertible
            );
            assert_eq!(pending, [crate::conv::SetAside::AtPoint {
                words: words_at,
                from: open,
                to: open
            }]);
        }
        let unlooped = arena.value_type_path(word_type, open, open);
        let mut pending = Vec::new();
        assert_eq!(
            crate::conv::pending_endpoints(
                &arena,
                &presentations,
                crate::conv::ConversionGoal::ValueType(word_type, unlooped),
                &mut pending
            ),
            crate::conv::Convertibility::Distinct,
            "no cell loops in the words themselves"
        );

        // `c = λy. return here(y)` at `(y : S) → F Path(S, y, y)`, then
        // `λx. return ⟨force c x⟩` at `S → F words`: the path at an open `x`
        // reads as the words only if `x` reads as `base`, and it does not.
        let mut staging = environment.stage();
        let arena = staging.arena();
        let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let y = arena.value_variable(DeBruijnIndex::from(0_u32));
        let at_y = arena.value_type_path(carrier, y, y);
        let returns_path = arena.comp_type_returner(at_y);
        let pi = arena.comp_type_pi(carrier, returns_path);
        let declared = arena.value_type_thunk(pi);
        let here = arena.value_here(y);
        let returned = arena.computation_return(here);
        let lambda = arena.computation_lambda(returned);
        let body = arena.value_thunk(lambda);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        let reflexive = environment
            .add_decl(staged)
            .expect("reflexivity at every point admits")
            .position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let carrier = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let word_type = arena.value_type_data(words_at, Vec::new());
        let named = arena.value_constant(reflexive);
        let forced = arena.computation_force(named);
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let applied = arena.computation_application(forced, x);
        let path = arena.value_returned(applied);
        let returned = arena.computation_return(path);
        let lambda = arena.computation_lambda(returned);
        let body = arena.value_thunk(lambda);
        let returns_words = arena.comp_type_returner(word_type);
        let arrow = arena.comp_type_arrow(carrier, returns_words);
        let declared = arena.value_type_thunk(arrow);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(
            environment.add_decl(staged).is_err(),
            "a path at an open point is apart from the words at `base`"
        );
    }
}
