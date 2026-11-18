//! A presented type's terms read by their normal forms.
//!
//! A data declaration may present its type by constructor-headed rules, a
//! [`Presentation`]: two terms of the type are equal exactly when the rules
//! rewrite them to one normal form. The conversion machine takes a value
//! pair's normal forms before it plans the pair, as the kernel's replay takes
//! them after weak head reduction, so both compare the same terms and no
//! decision of the trace vocabulary records the step.
//!
//! The rewriting reads no definition. A constructor term is flattened through
//! the constructors of its own declaration only; every other field — a
//! variable, a neutral, a value of another type — is a leaf the rules carry.
//! Both sides run [`Presentation::normalize`], whose fixed strategy gives them
//! one normal form even for rules that are not confluent. A redex a definition
//! hides behind a leaf is not uncovered: the pair is then compared as written,
//! which can cost completeness and never soundness.
//!
//! One kind of leaf is read before the rules run: a held endpoint, a compound
//! endpoint stuck on a definition, which no decision of the trace can name
//! once it stands under a constructor. [`normal_form`] runs it as
//! [`crate::eval::Endpoints::Run`] would have, within the run's budget, and
//! flattens what it returns in its place, so `turn(unturn(n))` reads as
//! `S(P(n))` and then as `n`. The kernel's replay reads the same leaf by its
//! own evaluator; the decision, its alternative and its reversal are recorded
//! there, at `Replay::read_returned_leaves` in the kernel's `replay` module.
//!
//! A reflexivity at a looped point reads as the empty word of the type of words
//! over that point, the canonical form of the one path both spell. The
//! lowering reads `here(p)` so in types, and `syntax::empty_word` in core-term
//! compares the two spellings so. [`normal_form`] reads a value so at the root
//! of a side whose pair's other side is no reflexivity ([`Reflexive`]); two
//! reflexivities keep the rule that compares their points. The kernel's replay
//! reads the same reflexivity so in its own `present`, so the trace records
//! nothing.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::Normalized;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleTerm;

use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::ValueClosureId;
use crate::closure::Environment;
use crate::closure::ValueBody;
use crate::conv::ConversionFault;
use crate::domain::DomainValue;
use crate::domain::TermFace;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;

/// A presented type's rules beside its constructor table's arities.
///
/// # Specification
/// - provides: what conversion rewrites a presented type's terms by.
/// - panics: none.
/// - executable: none — data declaration; [`Presented::new`] builds it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Presented
{
    /// The rules, validated against the table.
    presentation: Presentation,
    /// Each constructor's field count, by tag.
    arities: Arc<[FieldCount]>,
    /// The classifier `Data(w, [])` of the type's own terms, when the checker
    /// gave it: the type an empty word the evaluator mints stands at.
    own: Option<ValueTypeId>,
}

impl Presented
{
    /// The rules `presentation` over a table whose constructors have
    /// `arities` fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        presentation: Presentation,
        arities: Arc<[FieldCount]>,
    ) -> Self
    {
        Self {
            presentation,
            arities,
            own: None,
        }
    }

    /// The same rules, with `own` the classifier `Data(w, [])` of the type's
    /// own terms.
    ///
    /// The evaluator writes no core node, so it mints an empty word at the
    /// classifier the checker gives here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn classified(
        self,
        own: ValueTypeId,
    ) -> Self
    {
        Self {
            own: Some(own),
            ..self
        }
    }

    /// The cells the presentation's words loop by, when it is a type of
    /// words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn cells(&self) -> Option<&gandr_kernel_term::FreeCells>
    {
        self.presentation.cells()
    }
}

/// What taking a value's normal form gave.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NormalForm
{
    /// The value is its own normal form: no presented constructor heads it,
    /// or no rule matches anywhere in its constructor term.
    Kept,
    /// The value minted for the normal form.
    Rewritten(DomainValueId),
    /// The fuel ran out first.
    Exhausted,
}

/// Whether a reflexivity at the root of a side reads as an empty word.
///
/// The pair's other side picks it: two reflexivities keep the rule that
/// compares their points, so each dialogue that rule recorded replays as
/// before.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reflexive
{
    /// The other side is no reflexivity: a reflexivity at a looped point
    /// reads as the empty word of its words.
    Worded,
    /// The other side is a reflexivity too: a reflexivity stays as it is.
    Kept,
}

impl Reflexive
{
    /// How a side reads its reflexivity when the pair's other side is
    /// `other`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn facing(
        domain: &DomainArena,
        other: DomainValueId,
    ) -> Self
    {
        if matches!(domain.value(other), Some(&DomainValue::Here { .. })) {
            Self::Kept
        }
        else {
            Self::Worded
        }
    }
}

/// Where a flattened constructor came from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Origin
{
    /// The node at this id, as written.
    Written(DomainValueId),
    /// A rewrite built it.
    Rewritten,
}

/// The declaration a constructor's classifier closure names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(Some(d))` exactly when the closure suspends a value type that
///   is the nominal head of declaration `d`; `Ok(None)` for any other
///   classifier.
/// - fails: [`DomainFault::Dangling`] for a closure the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
#[spec(ensures: |ret| ret.is_ok() || ret == Err(ConversionFault::Domain(DomainFault::Dangling)))]
fn declaration(
    core: &CoreArena,
    domain: &DomainArena,
    datatype: ValueClosureId,
) -> Result<Option<ConstantIndex>, ConversionFault>
{
    let closure = domain
        .value_closure(datatype)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    let ValueBody::ValueType(classifier) = closure.body()
    else {
        return Ok(None);
    };
    match core.value_type(classifier) {
        Some(&ValueType::Data { declaration, .. }) => Ok(Some(declaration)),
        Some(_) | None => Ok(None),
    }
}

/// What reading a leaf before the rules gave.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Held
{
    /// The value the leaf reads as, to flatten in its place.
    Read(DomainValueId),
    /// The leaf stays as written.
    Kept,
    /// The fuel ran out first.
    Exhausted,
}

/// What a held endpoint returns, its run charged to `fuel`.
///
/// # Specification
/// - requires: `value` lives in `domain`.
/// - ensures: [`Held::Read`] with what [`crate::eval::run_held`] returns for
///   `value`, [`Held::Kept`] when it returns nothing, each evaluation step
///   charged to `fuel`; [`Held::Exhausted`] with `fuel` at zero when the run
///   spends it.
/// - fails: [`ConversionFault::Evaluation`] for a run the evaluator refuses
///   otherwise than on fuel.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_held_call_under_a_presented_constructor_reads_as_what_it_returns`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && (ret != Ok(Held::Exhausted) || u64::from(*fuel) == 0))]
fn read_held(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    value: DomainValueId,
    fuel: &mut RewriteFuel,
) -> Result<Held, ConversionFault>
{
    let slice = Fuel::from(u32::try_from(u64::from(*fuel)).unwrap_or(u32::MAX));
    let (read, left) = match crate::eval::run_held(core, domain, definitions, slice, value) {
        Ok(ran) => ran,
        Err(EvalFault::OutOfFuel) => {
            *fuel = RewriteFuel::from(0_u64);
            return Ok(Held::Exhausted);
        },
        Err(fault) => return Err(ConversionFault::Evaluation(fault)),
    };
    let spent = u32::from(slice).saturating_sub(u32::from(left));
    *fuel = RewriteFuel::from(u64::from(*fuel).saturating_sub(u64::from(spent)));
    Ok(read.map_or(Held::Kept, Held::Read))
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
    /// It is another term, or a term a leaf stands in.
    Apart,
}

/// Whether `value` is the constructor term of `sort` that the closed rule side
/// `side` spells.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Spelling::Spelled`] exactly when reading `value` in pre-order
///   meets one constructor of `sort` for each node of `side`, each with the
///   node's tag, and no node is left over on either side; a variable node, and
///   a field that is no constructor, spell nothing.
/// - provides: the point comparison of [`reflexivity_word`], as
///   `syntax::spells` in core-term makes it on core terms.
/// - fails: [`ConversionFault::Domain`] for a node, a field span or a closure
///   the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: one `for` loop over `side`'s nodes, not recursion.
/// - measure: the nodes of `side` not yet read.
///
/// # Adequacy
/// - hypothesis: L3 — as [`reflexivity_word`].
/// - witness: `presented::tests::a_reflexivity_at_a_looped_point_presents_as_its_empty_word_6477`
#[spec(ensures: |ret| !matches!(ret, Ok(Spelling::Spelled)) || !side.is_empty())]
fn spells(
    core: &CoreArena,
    domain: &DomainArena,
    sort: ConstantIndex,
    value: DomainValueId,
    side: &[RuleNode],
) -> Result<Spelling, ConversionFault>
{
    let mut pending = Vec::with_capacity(side.len());
    pending.push(value);
    for &node in side {
        let (Some(at), RuleNode::Constructor(tag)) = (pending.pop(), node)
        else {
            return Ok(Spelling::Apart);
        };
        let Some(&DomainValue::Constructor {
            datatype,
            tag: written,
            fields,
            ..
        }) = domain.value(at)
        else {
            return Ok(Spelling::Apart);
        };
        if written != tag || declaration(core, domain, datatype)? != Some(sort) {
            return Ok(Spelling::Apart);
        }
        let fields = domain.fields(fields).map_err(ConversionFault::Domain)?;
        pending.extend(fields.iter().rev().copied());
    }
    Ok(if pending.is_empty() {
        Spelling::Spelled
    }
    else {
        Spelling::Apart
    })
}

/// The empty word a reflexivity at a looped point reads as.
///
/// # Specification
/// - requires: `value` lives in `domain`, its classifier closures over `core`.
/// - ensures: [`NormalForm::Rewritten`] with a fresh empty word of `w`, a
///   reduced constructor of tag zero and no fields at the classifier `w`'s
///   [`Presented`] carries, exactly when `value` is `here(q)`, `q` reads as a
///   point `p` wrapped in `r` reflexivities, `p` is a constructor term of a
///   sort `s`, and `definitions` presents `w` with cells over `s` wrapped `r`
///   times whose point `p` spells. A `q` that reads as the empty word of a type
///   of words over `p` wrapped `t` times reads as `p` wrapped `r + t + 1`
///   times. The reading takes the reflexivities off `q`, and each held endpoint
///   it then meets runs by [`read_held`] and is unwrapped in turn. A held
///   endpoint runs only while some presented type of words is wrapped at least
///   as often as the reflexivities taken off so far, and its run is charged to
///   `fuel`. [`NormalForm::Exhausted`] with `fuel` at zero when a run spends
///   it; [`NormalForm::Kept`] otherwise.
/// - provides: the reading of [`normal_form`] at a reflexivity: the empty word
///   is the canonical form of the path both terms spell, as the kernel's replay
///   reads it in `present`.
/// - fails: [`ConversionFault::Domain`] for a node, a field span or a closure
///   the arena does not hold; [`ConversionFault::Evaluation`] for a run the
///   evaluator refuses otherwise than on fuel.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `loop` runs one held endpoint for each turn, each run charged
///   to `fuel`; the `while let` inside it takes one reflexivity off for each
///   turn, each a strict subterm; the `for` loop reads each presented type
///   once.
/// - measure: `fuel`, then the reflexivities still to take off, then the
///   presented types not yet read.
///
/// # Adequacy
/// - hypothesis: L3 — `here(base)` reads as the circle's empty word,
///   `here(here(base))` as the empty word of the 2-cells, a held point reads
///   once it runs, and `here(other)` off the point stays as written. At a point
///   with loops and a 2-cell, `here` of the loops' empty word reads as the
///   2-cells' empty word; read at the loops' sort, it stays as written.
/// - witness: `presented::tests::a_reflexivity_at_a_looped_point_presents_as_its_empty_word_6477`
/// - witness: `presented::tests::a_reflexivity_at_the_loops_empty_word_presents_as_the_cells_empty_word_6741`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && match ret {
        Ok(NormalForm::Rewritten(word)) => domain.value(word).is_some(),
        Ok(NormalForm::Exhausted) => u64::from(*fuel) == 0,
        Ok(NormalForm::Kept) | Err(_) => true,
    })]
fn reflexivity_word(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    value: DomainValueId,
    fuel: &mut RewriteFuel,
) -> Result<NormalForm, ConversionFault>
{
    let Some(&DomainValue::Here { point, .. }) = domain.value(value)
    else {
        return Ok(NormalForm::Kept);
    };
    let mut base = point;
    let mut wraps = 0_usize;
    loop {
        while let Some(&DomainValue::Here { point: inner, .. }) = domain.value(base) {
            base = inner;
            wraps = wraps.saturating_add(1);
        }
        if matches!(domain.value(base), Some(&DomainValue::Constructor { .. })) {
            break;
        }
        let worded = definitions.presentations().any(|(_, presented)| {
            presented
                .cells()
                .is_some_and(|cells| usize::from(cells.reflexivities()) >= wraps)
        });
        if !worded {
            return Ok(NormalForm::Kept);
        }
        base = match read_held(core, domain, definitions, base, fuel)? {
            Held::Read(read) => read,
            Held::Kept => return Ok(NormalForm::Kept),
            Held::Exhausted => return Ok(NormalForm::Exhausted),
        };
    }
    let Some(&DomainValue::Constructor { datatype, tag, .. }) = domain.value(base)
    else {
        return Ok(NormalForm::Kept);
    };
    let Some(declared) = declaration(core, domain, datatype)?
    else {
        return Ok(NormalForm::Kept);
    };
    // The empty word of a type of words over `p` wrapped `r` times spells `p`
    // wrapped `r + 1` times, so a reflexivity around it reads one dimension up.
    let emptied = if tag == gandr_kernel_term::FreeCells::nil() {
        definitions.presented(declared).and_then(Presented::cells)
    }
    else {
        None
    };
    let (sort, wraps) = emptied.map_or((declared, wraps), |below| {
        (
            below.sort(),
            wraps
                .saturating_add(usize::from(below.reflexivities()))
                .saturating_add(1),
        )
    });
    for (words, presented) in definitions.presentations() {
        let (Some(cells), Some(own)) = (presented.cells(), presented.own)
        else {
            continue;
        };
        let classified = matches!(
            core.value_type(own),
            Some(&ValueType::Data { declaration, ref arguments })
                if declaration == words && arguments.is_empty()
        );
        if !classified || cells.sort() != sort || usize::from(cells.reflexivities()) != wraps {
            continue;
        }
        let apart = match emptied {
            Some(below) => below.point() != cells.point(),
            None => spells(core, domain, sort, base, cells.point())? == Spelling::Apart,
        };
        if apart {
            continue;
        }
        let datatype = domain.value_closure_node(ValueBody::ValueType(own), Environment::new());
        let none = domain.hold_fields([]);
        let word = domain.value_constructor(
            words,
            datatype,
            ConstructorTag::from(0_usize),
            none,
            TermFace::Reduced,
        );
        return Ok(NormalForm::Rewritten(word));
    }
    Ok(NormalForm::Kept)
}

/// A univalence facing a reflexivity, its held cell read as what the cell
/// returns, so the identity cell meets reflexivity by its syntax
/// ([`crate::identity::identity_cell`]).
///
/// # Specification
/// - requires: `value` lives in `domain`.
/// - ensures: for `value` a univalence whose cell is a held endpoint that
///   returns, [`NormalForm::Rewritten`] with the univalence of what the cell
///   returns beside the same forward map; [`NormalForm::Exhausted`] with `fuel`
///   at zero when the run spends it; [`NormalForm::Kept`] otherwise.
/// - provides: the read the conversion takes before it plans `ua` of a cell
///   against reflexivity; the kernel's replay reads the cell the same way.
/// - fails: [`ConversionFault::Evaluation`] for a run the evaluator refuses
///   otherwise than on fuel.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `ua(idEquiv(Circle))` reads its cell as the identity
///   equivalence and converts with reflexivity at the circle; unread, the cell
///   is a held call and the two stay apart.
/// - witness: `identity::tests::ua_of_the_identity_equivalence_is_reflexivity_6530`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && match ret {
        Ok(NormalForm::Rewritten(normal)) => matches!(domain.value(normal), Some(&DomainValue::Univalence { .. })),
        Ok(NormalForm::Exhausted) => u64::from(*fuel) == 0,
        Ok(NormalForm::Kept) | Err(_) => true,
    })]
pub fn univalence_cell(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    value: DomainValueId,
    fuel: &mut RewriteFuel,
) -> Result<NormalForm, ConversionFault>
{
    let Some(&DomainValue::Univalence {
        record,
        forward,
        face,
    }) = domain.value(value)
    else {
        return Ok(NormalForm::Kept);
    };
    Ok(match read_held(core, domain, definitions, record, fuel)? {
        Held::Read(read) => NormalForm::Rewritten(domain.value_univalence(read, forward, face)),
        Held::Kept => NormalForm::Kept,
        Held::Exhausted => NormalForm::Exhausted,
    })
}

/// The normal form of `value` under the rules of the presented type heading
/// it.
///
/// # Specification
/// - requires: `value` lives in `domain`, its classifier closures over `core`.
/// - ensures: for a reflexivity at the root, what [`reflexivity_word`] reads it
///   as when `reflexive` is [`Reflexive::Worded`], and [`NormalForm::Kept`]
///   otherwise. For any other value, [`NormalForm::Kept`] when `value` is not a
///   constructor of a type `definitions` presents, or no held endpoint among
///   its constructor term's leaves returns a value and no rule matches anywhere
///   in the term; otherwise [`NormalForm::Rewritten`] with the value minted for
///   the normal form of the term whose held leaves are read as the evaluator's
///   `run_held` reads them — every node the rewriting left as written kept at
///   its own id, every constructor it rebuilt minted with the classifier of the
///   one it stands for, or of the redex it replaced, and a reduced face. A
///   normal form that rewrites to a reflexivity reads again as the root does.
///   Each node compared or copied, and each evaluation step a read takes, costs
///   one unit of `fuel`; [`NormalForm::Exhausted`] when it runs out.
/// - provides: the forced step conversion takes before it plans a value pair,
///   reaching the kernel replay's normal form: the leaves it reads, the
///   flattening, the strategy and the rebuild are the kernel's own.
/// - fails: [`ConversionFault::Domain`] for a node, a field span or a closure
///   the arena does not hold; [`ConversionFault::Evaluation`] for a read the
///   evaluator refuses otherwise than on fuel.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loops over the flattening stack and over the
///   rewritten term, not recursion; the rewriting itself is
///   [`Presentation::normalize`]'s.
/// - measure: `fuel`, which every read leaf spends at least one unit of, then
///   the nodes still to flatten, each a strict subterm; the term nodes still to
///   rebuild.
///
/// # Adequacy
/// - hypothesis: L3 — `loop(unloop(loop(x)))` reads as `loop(x)` over the
///   variable written inside it, a reduced word is kept, the same word over a
///   type no definition presents is never read, `loop(⟨ident(unloop(base))⟩)`
///   reads as `base` once its held leaf runs, and a reflexivity at the looped
///   point reads as the empty word against a side that is no reflexivity.
/// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
/// - witness: `presented::tests::a_held_call_under_a_presented_constructor_reads_as_what_it_returns`
/// - witness: `presented::tests::a_reflexivity_at_a_looped_point_presents_as_its_empty_word_6477`
#[spec(captures: before = u64::from(*fuel), ensures: |ret| u64::from(*fuel) <= before
    && match ret {
        Ok(NormalForm::Rewritten(normal)) => domain.value(normal).is_some(),
        Ok(NormalForm::Exhausted) => u64::from(*fuel) == 0,
        Ok(NormalForm::Kept) | Err(_) => true,
    })]
pub fn normal_form(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    value: DomainValueId,
    reflexive: Reflexive,
    fuel: &mut RewriteFuel,
) -> Result<NormalForm, ConversionFault>
{
    let dangling = ConversionFault::Domain(DomainFault::Dangling);
    let Some(&DomainValue::Constructor { datatype, .. }) = domain.value(value)
    else {
        return match reflexive {
            Reflexive::Worded => reflexivity_word(core, domain, definitions, value, fuel),
            Reflexive::Kept => Ok(NormalForm::Kept),
        };
    };
    let Some(own) = declaration(core, domain, datatype)?
    else {
        return Ok(NormalForm::Kept);
    };
    let Some(presented) = definitions.presented(own)
    else {
        return Ok(NormalForm::Kept);
    };
    let mut term: Vec<RuleTerm<(ValueClosureId, Origin), DomainValueId>> = Vec::new();
    let mut pending = Vec::from([value]);
    let mut read_any = false;
    while let Some(id) = pending.pop() {
        let node = domain.value(id).copied().ok_or(dangling)?;
        let DomainValue::Constructor {
            datatype,
            tag,
            fields,
            ..
        } = node
        else {
            match read_held(core, domain, definitions, id, fuel)? {
                Held::Read(read) => {
                    read_any = true;
                    pending.push(read);
                },
                Held::Kept => term.push(RuleTerm::Leaf(id)),
                Held::Exhausted => return Ok(NormalForm::Exhausted),
            }
            continue;
        };
        if declaration(core, domain, datatype)? != Some(own) {
            term.push(RuleTerm::Leaf(id));
            continue;
        }
        let fields = domain.fields(fields).map_err(ConversionFault::Domain)?;
        term.push(RuleTerm::Constructor {
            tag,
            arity: FieldCount::from(fields.len()),
            payload: (datatype, Origin::Written(id)),
        });
        pending.extend(fields.iter().rev().copied());
    }
    let normalized = presented.presentation.normalize(
        &presented.arities,
        &mut term,
        |&(datatype, _)| (datatype, Origin::Rewritten),
        fuel,
    );
    match normalized {
        Err(_) => return Ok(NormalForm::Exhausted),
        Ok(Normalized::Unchanged) if !read_any => return Ok(NormalForm::Kept),
        Ok(Normalized::Unchanged | Normalized::Rewritten) => {},
    }
    let mut built: Vec<DomainValueId> = Vec::new();
    while let Some(node) = term.pop() {
        let RuleTerm::Constructor {
            tag,
            arity,
            payload: (datatype, origin),
        } = node
        else {
            if let RuleTerm::Leaf(id) = node {
                built.push(id);
            }
            continue;
        };
        let start = built.len().saturating_sub(usize::from(arity));
        let fields: Vec<DomainValueId> = built.drain(start ..).rev().collect();
        let kept = kept(domain, origin, &fields)?;
        let rebuilt = match kept {
            Origin::Written(id) => id,
            Origin::Rewritten => {
                let span = domain.hold_fields(fields);
                domain.value_constructor(own, datatype, tag, span, TermFace::Reduced)
            },
        };
        built.push(rebuilt);
    }
    let Some(normal) = built.pop()
    else {
        return Ok(NormalForm::Kept);
    };
    if reflexive == Reflexive::Worded
        && matches!(domain.value(normal), Some(&DomainValue::Here { .. }))
    {
        return Ok(
            match reflexivity_word(core, domain, definitions, normal, fuel)? {
                NormalForm::Kept => NormalForm::Rewritten(normal),
                read @ (NormalForm::Rewritten(_) | NormalForm::Exhausted) => read,
            },
        );
    }
    Ok(NormalForm::Rewritten(normal))
}

/// Whether a rebuilt constructor is the node it was flattened from.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `origin` itself when it names a written node whose fields are
///   `fields`, in order; [`Origin::Rewritten`] otherwise, so the caller mints.
/// - fails: [`ConversionFault::Domain`] for a written node or field span the
///   arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal_form`].
/// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
#[spec(ensures: |ret| ret.map_or(true, |found| found == Origin::Rewritten || found == origin))]
fn kept(
    domain: &DomainArena,
    origin: Origin,
    fields: &[DomainValueId],
) -> Result<Origin, ConversionFault>
{
    let Origin::Written(id) = origin
    else {
        return Ok(Origin::Rewritten);
    };
    let Some(&DomainValue::Constructor {
        fields: written, ..
    }) = domain.value(id)
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let written = domain.fields(written).map_err(ConversionFault::Domain)?;
    Ok(if written == fields {
        origin
    }
    else {
        Origin::Rewritten
    })
}

#[cfg(test)]
mod tests;
