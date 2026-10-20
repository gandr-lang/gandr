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

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::Normalized;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleTerm;

use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::ValueClosureId;
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

/// The normal form of `value` under the rules of the presented type heading
/// it.
///
/// # Specification
/// - requires: `value` lives in `domain`, its classifier closures over `core`.
/// - ensures: [`NormalForm::Kept`] when `value` is not a constructor of a type
///   `definitions` presents, or no held endpoint among its constructor term's
///   leaves returns a value and no rule matches anywhere in the term; otherwise
///   [`NormalForm::Rewritten`] with the value minted for the normal form of the
///   term whose held leaves are read as the evaluator's `run_held` reads them —
///   every node the rewriting left as written kept at its own id, every
///   constructor it rebuilt minted with the classifier of the one it stands
///   for, or of the redex it replaced, and a reduced face. Each node compared
///   or copied, and each evaluation step a read takes, costs one unit of
///   `fuel`; [`NormalForm::Exhausted`] when it runs out.
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
///   type no definition presents is never read, and
///   `loop(⟨ident(unloop(base))⟩)` reads as `base` once its held leaf runs.
/// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
/// - witness: `presented::tests::a_held_call_under_a_presented_constructor_reads_as_what_it_returns`
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
    fuel: &mut RewriteFuel,
) -> Result<NormalForm, ConversionFault>
{
    let dangling = ConversionFault::Domain(DomainFault::Dangling);
    let Some(&DomainValue::Constructor { datatype, .. }) = domain.value(value)
    else {
        return Ok(NormalForm::Kept);
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
            let slice = Fuel::from(u32::try_from(u64::from(*fuel)).unwrap_or(u32::MAX));
            let (read, left) = match crate::eval::run_held(core, domain, definitions, slice, id) {
                Ok(ran) => ran,
                Err(EvalFault::OutOfFuel) => {
                    *fuel = RewriteFuel::from(0_u64);
                    return Ok(NormalForm::Exhausted);
                },
                Err(fault) => return Err(ConversionFault::Evaluation(fault)),
            };
            let spent = u32::from(slice).saturating_sub(u32::from(left));
            *fuel = RewriteFuel::from(u64::from(*fuel).saturating_sub(u64::from(spent)));
            match read {
                Some(read) => {
                    read_any = true;
                    pending.push(read);
                },
                None => term.push(RuleTerm::Leaf(id)),
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
                domain.value_constructor(datatype, tag, span, TermFace::Reduced)
            },
        };
        built.push(rebuilt);
    }
    Ok(built.pop().map_or(NormalForm::Kept, NormalForm::Rewritten))
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
