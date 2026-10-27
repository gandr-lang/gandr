//! Where the explicit form writes the reduct or the forgetting map the
//! checker applies, `T.S(m)` or `forget[sort C = A](m) at Model(T)`, and the
//! sugared form leaves it to the checker, `m`.
//!
//! A theory `T` that includes a theory `S` takes a reduct `T.S` from the
//! models of `T` to the models of `S`, and the checker applies it where a
//! model of `T` stands where a model of `S` is asked; a model whose sorts are
//! manifest is read as a model of its theory by the forgetting map the
//! checker applies at the carriers it solves ([`crate::forget`] selects the
//! applications a form writes). The explicit form writes each application the
//! checker makes, around the value it made it at; the sugared form leaves out
//! each call of a reduct and each forgetting map the source writes, leaving
//! it to the checker. The two spellings lower to different cores — a call of
//! the map, and the value the checker applies it to — so a source rewritten
//! either way is checked by the bodies the checker elaborates
//! ([`crate::Elaborate`]): where a declaration then elaborates otherwise — a
//! map written where the checker would apply none, in a type it reads by its
//! value, or at carriers other than those it solves — its maps stay as
//! written and the formatting is tried again, unreported, as a thunk the
//! checker would not insert stays. A declaration the checker elaborates
//! nothing for keeps its maps, and without a checker no map is written or
//! left out.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::Naming;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Forgetting;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::composite::Token;
use crate::composite::tokens;
use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::meaning::Elaboration;

/// The reducts and forgetting maps a source's module mints, and where the
/// checker applies them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Reducts
{
    /// Each reduct's name, segment by segment, by its constant:
    /// `["Monoid", "Semigroup"]`.
    names: BTreeMap<ConstantIndex, Vec<String>>,
    /// Each value the checker applies a reduct or a forgetting map to: its
    /// span, in the source's own offsets, and the map; ascending by span.
    crossings: Vec<(ByteSpan, Crossed)>,
    /// The spans of the top-level forms the checker elaborates nothing for,
    /// ascending: their maps stay as written.
    unchecked: Vec<ByteSpan>,
    /// Whether the module mints a forgetting map, so a written one is left to
    /// the checker.
    forgetting: bool,
}

/// A map the checker applies at a value.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Crossed
{
    /// The reduct at this constant.
    Reduct(ConstantIndex),
    /// A forgetting map, as the explicit form spells it.
    Forget(Forget),
}

/// A forgetting map's form, `forget[sort C = A, …](m) at Model(T)`, but the
/// model.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Forget
{
    /// Each sort the map puts back, and its carrier's type as the printer
    /// spells it, in the map's order.
    pub sorts: Vec<(String, Vec<Token>)>,
    /// The theory's name, segment by segment.
    pub theory: Vec<String>,
}

/// How the explicit form writes the map the checker applies at a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Applied<'reducts>
{
    /// The reduct's call, its name segment by segment.
    Reduct(&'reducts [String]),
    /// The forgetting map's form.
    Forget(&'reducts Forget),
}

/// How a form writes a reduct.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reduct
{
    /// As the form the rewrite moves it to.
    Moved,
    /// As the source writes it.
    Kept,
}

impl Reducts
{
    /// The reducts and forgetting maps `module` mints, beside where
    /// `elaboration`, the checker's elaboration of `module` into `arena` from
    /// `text`, applies them: the values whose spans start at or after `base`
    /// — the source after the text its imports place before it — at their
    /// spans less `base`; `unchecked` holds the spans of the top-level forms
    /// the checker elaborates nothing for. A forgetting map's carriers are
    /// spelled by the shared printer under the names the source writes for
    /// the binders around the value; one the printer cannot spell faithfully
    /// is left to the checker.
    ///
    /// # Specification
    /// trivial.
    pub fn beside(
        module: &LoweredModule<'_>,
        elaboration: &Elaboration,
        (arena, text): (&CoreArena, SourceText<'_>),
        (base, mut unchecked): (ByteOffset, Vec<ByteSpan>),
    ) -> Self
    {
        let minted: BTreeSet<ConstantIndex> = module.reducts().iter().copied().collect();
        let names: BTreeMap<ConstantIndex, Vec<String>> = module
            .declarations()
            .iter()
            .filter(|declaration| minted.contains(&declaration.constant()))
            .map(|declaration| {
                (
                    declaration.constant(),
                    module
                        .path_of(declaration)
                        .iter()
                        .map(|segment| String::from(segment.as_ref()))
                        .collect(),
                )
            })
            .collect();
        let mut crossings: Vec<(ByteSpan, Crossed)> = elaboration
            .crossings
            .iter()
            .filter(|&(_, crossing)| names.contains_key(&crossing.by))
            .filter_map(|(&value, crossing)| {
                Some((located(module, value, base)?, Crossed::Reduct(crossing.by)))
            })
            .collect();
        let forgettings = crate::forget::forgettings(module, arena, &elaboration.crossings);
        if !forgettings.is_empty() {
            crossings.extend(forgets(module, (arena, text), &forgettings, base));
        }
        crossings.sort_by_key(|&(span, _)| span);
        crossings.dedup_by_key(|entry| entry.0);
        unchecked.sort_unstable();
        unchecked.dedup();
        Self {
            names,
            crossings,
            unchecked,
            forgetting: !module.forgets().is_empty(),
        }
    }

    /// The map the checker applies to the value spanning exactly `span`,
    /// outside the top-level forms at `kept` and those it elaborates nothing
    /// for.
    ///
    /// # Specification
    /// trivial.
    pub fn crossed(
        &self,
        span: ByteSpan,
        kept: &[ByteSpan],
    ) -> Option<Applied<'_>>
    {
        if self.within(span, kept) == Reduct::Kept {
            return None;
        }
        let at = self
            .crossings
            .binary_search_by_key(&span, |&(crossed, _)| crossed)
            .ok()?;
        match *self.crossings.get(at)? {
            (_, Crossed::Reduct(reduct)) => {
                self.names.get(&reduct).map(|name| Applied::Reduct(name))
            },
            (_, Crossed::Forget(ref forget)) => Some(Applied::Forget(forget)),
        }
    }

    /// How the sugared form writes the call spanning `span` whose callee's
    /// tokens are `callee`: moved to its argument when the callee names a
    /// reduct and the call stands outside the top-level forms at `kept` and
    /// those the checker elaborates nothing for.
    ///
    /// # Specification
    /// trivial.
    pub fn called(
        &self,
        (span, callee): (ByteSpan, &[SourceFragment<'_>]),
        kept: &[ByteSpan],
    ) -> Reduct
    {
        if self
            .names
            .values()
            .any(|name| spelling(name).eq(callee.iter().map(|&token| <&str>::from(token))))
        {
            self.within(span, kept)
        }
        else {
            Reduct::Kept
        }
    }

    /// How the sugared form writes the forgetting map's form spanning `span`:
    /// moved to its model when the module mints a forgetting map and the form
    /// stands outside the top-level forms at `kept` and those the checker
    /// elaborates nothing for.
    ///
    /// # Specification
    /// trivial.
    pub fn forgotten(
        &self,
        span: ByteSpan,
        kept: &[ByteSpan],
    ) -> Reduct
    {
        if self.forgetting {
            self.within(span, kept)
        }
        else {
            Reduct::Kept
        }
    }

    /// Whether the top-level forms at `forms`, whose leaves are among
    /// `leaves`, hold a map a rewrite moves: a value the checker applies a
    /// reduct or a forgetting map to, or a call the source writes of one.
    ///
    /// # Specification
    /// trivial.
    pub fn held(
        &self,
        leaves: &[Leaf<'_>],
        forms: &[ByteSpan],
    ) -> Reduct
    {
        let inside = |span: ByteSpan| {
            forms
                .iter()
                .any(|form| form.start() <= span.start() && span.end() <= form.end())
        };
        if self.crossings.iter().any(|&(span, _)| inside(span)) {
            return Reduct::Moved;
        }
        let tokens: Vec<&str> = leaves
            .iter()
            .filter(|leaf| leaf.material == Material::Token && inside(leaf.span))
            .map(|leaf| <&str>::from(leaf.text))
            .collect();
        let written = self.names.values().any(|name| {
            let width = name.len().saturating_mul(2).saturating_sub(1);
            tokens
                .windows(width.max(1))
                .any(|window| spelling(name).eq(window.iter().copied()))
        }) || (self.forgetting
            && tokens.windows(2).any(|window| window == ["forget", "["]));
        if written { Reduct::Moved } else { Reduct::Kept }
    }

    /// How a map at `span` is written: kept inside a top-level form at `kept`
    /// or one the checker elaborates nothing for, moved elsewhere.
    ///
    /// # Specification
    /// trivial.
    fn within(
        &self,
        span: ByteSpan,
        kept: &[ByteSpan],
    ) -> Reduct
    {
        let inside = |forms: &[ByteSpan]| {
            forms
                .iter()
                .any(|form| form.start() <= span.start() && span.end() <= form.end())
        };
        if inside(kept) || inside(&self.unchecked) {
            Reduct::Kept
        }
        else {
            Reduct::Moved
        }
    }
}

/// The span of the value `value`, in the offsets of the source starting at
/// `base`; none when it has no origin or starts before `base`.
///
/// # Specification
/// trivial.
fn located(
    module: &LoweredModule<'_>,
    value: ValueId,
    base: ByteOffset,
) -> Option<ByteSpan>
{
    let Maybe::Present(origin) = module.origins().value(value)
    else {
        return None;
    };
    let span = origin.span();
    let start = usize::from(span.start()).checked_sub(usize::from(base))?;
    let end = usize::from(span.end()).checked_sub(usize::from(base))?;
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
}

/// Each forgetting map of `forgettings` the explicit form writes, at the span
/// of the value it is applied to: its carriers spelled by the shared printer
/// under the names `text` writes for the binders around the value, each
/// faithfully, or the map is left out.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "one binder buffer per declaration, reused across its maps: its names borrow \
                  that declaration's scopes, which the next pass replaces"
    )
)]
fn forgets(
    module: &LoweredModule<'_>,
    (arena, text): (&CoreArena, SourceText<'_>),
    forgettings: &[(ValueId, Forgetting<'_>)],
    base: ByteOffset,
) -> Vec<(ByteSpan, Crossed)>
{
    let owned = constant_names(module);
    let names: Vec<Name<'_>> = owned.iter().map(|name| Name::from(name.as_str())).collect();
    let families = Families::of(module);
    let constructors = families.naming();
    let style = Style {
        form: Form::Explicit,
        spelling: gandr_surface_pretty::Spelling::Ascii,
    };
    let naming = Naming::of(module, text);
    let mut pending: Vec<&(ValueId, Forgetting<'_>)> = forgettings.iter().collect();
    let mut found = Vec::new();
    for (_, roots) in naming.declarations() {
        if pending.is_empty() {
            break;
        }
        let scoped = naming.scoped(arena, &owned, roots);
        let mut binders: Vec<Option<Name<'_>>> = Vec::new();
        pending.retain(|&&(value, ref forgetting)| {
            let Some(around) = scoped.around(CoreNode::Value(value))
            else {
                return true;
            };
            binders.clear();
            binders.extend(around.iter().map(|binder| binder.name.map(Name::from)));
            let source = CoreSource::new(arena, &names)
                .naming(&constructors)
                .within(&binders);
            let sorts: Option<Vec<(String, Vec<Token>)>> = forgetting
                .sorts
                .iter()
                .map(|&(sort, carrier)| {
                    let spelled =
                        present_type(&source, carrier, PageWidth::from(u32::MAX), style).ok()?;
                    if spelled.fidelity() != Fidelity::Faithful || !spelled.unspelled().is_empty() {
                        return None;
                    }
                    Some((
                        String::from(sort.as_ref()),
                        tokens(SourceFragment::from(spelled.as_ref()))?,
                    ))
                })
                .collect();
            let theory: Option<Vec<String>> = owned
                .get(usize::from(forgetting.theory))
                .map(|name| name.split('.').map(String::from).collect());
            if let (Some(sorts), Some(theory), Some(span)) =
                (sorts, theory, located(module, value, base))
            {
                found.push((span, Crossed::Forget(Forget { sorts, theory })));
            }
            false
        });
    }
    found
}

/// The tokens that spell the name whose segments are `name`, a `.` between
/// each two.
///
/// # Specification
/// trivial.
fn spelling(name: &[String]) -> impl Iterator<Item = &str>
{
    name.iter().enumerate().flat_map(|(index, segment)| {
        (index > 0)
            .then_some(".")
            .into_iter()
            .chain(core::iter::once(segment.as_str()))
    })
}
