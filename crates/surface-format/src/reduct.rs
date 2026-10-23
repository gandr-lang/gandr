//! Where the explicit form writes the reduct the checker applies, `T.S(m)`,
//! and the sugared form leaves it to the checker, `m`.
//!
//! A theory `T` that includes a theory `S` takes a reduct `T.S` from the
//! models of `T` to the models of `S`, and the checker applies it where a
//! model of `T` stands where a model of `S` is asked. The explicit form
//! writes each application the checker makes, around the value it made it
//! at; the sugared form leaves out each call of a reduct the source writes,
//! leaving it to the checker. The two spellings lower to different cores — a
//! call of the reduct, and the value the checker applies it to — so a source
//! rewritten either way is checked by the bodies the checker elaborates
//! ([`crate::Elaborate`]): where a declaration then elaborates otherwise — a
//! reduct written where the checker would apply none, in a type it reads by
//! its value — its reducts stay as written and the formatting is tried
//! again, unreported, as a thunk the checker would not insert stays. A
//! declaration the checker elaborates nothing for keeps its reducts, and
//! without a checker no reduct is written or left out.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::meaning::Elaboration;

/// The reducts a source's module mints, and where the checker applies them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Reducts
{
    /// Each reduct's name, segment by segment, by its constant:
    /// `["Monoid", "Semigroup"]`.
    names: BTreeMap<ConstantIndex, Vec<String>>,
    /// Each value the checker applies a reduct to: its span, in the source's
    /// own offsets, and the reduct's constant; ascending by span.
    crossings: Vec<(ByteSpan, ConstantIndex)>,
    /// The spans of the top-level forms the checker elaborates nothing for,
    /// ascending: their reducts stay as written.
    unchecked: Vec<ByteSpan>,
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
    /// The reducts `module` mints, beside where `elaboration`, the checker's
    /// elaboration of `module`, applies them: the values whose spans start at
    /// or after `base` — the source after the text its imports place before
    /// it — at their spans less `base`; `unchecked` holds the spans of the
    /// top-level forms the checker elaborates nothing for.
    ///
    /// # Specification
    /// trivial.
    pub fn beside(
        module: &LoweredModule<'_>,
        elaboration: &Elaboration,
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
        let mut crossings: Vec<(ByteSpan, ConstantIndex)> = elaboration
            .crossings
            .iter()
            .filter(|&(_, reduct)| names.contains_key(reduct))
            .filter_map(|(&value, &reduct)| {
                let Maybe::Present(origin) = module.origins().value(value)
                else {
                    return None;
                };
                let span = origin.span();
                let start = usize::from(span.start()).checked_sub(usize::from(base))?;
                let end = usize::from(span.end()).checked_sub(usize::from(base))?;
                let span = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()?;
                Some((span, reduct))
            })
            .collect();
        crossings.sort_unstable();
        crossings.dedup_by_key(|&mut (span, _)| span);
        unchecked.sort_unstable();
        unchecked.dedup();
        Self {
            names,
            crossings,
            unchecked,
        }
    }

    /// The name, segment by segment, of the reduct the checker applies to the
    /// value spanning exactly `span`, outside the top-level forms at `kept`
    /// and those it elaborates nothing for.
    ///
    /// # Specification
    /// trivial.
    pub fn crossed(
        &self,
        span: ByteSpan,
        kept: &[ByteSpan],
    ) -> Option<&[String]>
    {
        if self.within(span, kept) == Reduct::Kept {
            return None;
        }
        let at = self
            .crossings
            .binary_search_by_key(&span, |&(crossed, _)| crossed)
            .ok()?;
        let &(_, reduct) = self.crossings.get(at)?;
        self.names.get(&reduct).map(Vec::as_slice)
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

    /// Whether the top-level forms at `forms`, whose leaves are among
    /// `leaves`, hold a reduct a rewrite moves: a value the checker applies a
    /// reduct to, or a call the source writes of one.
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
        });
        if written { Reduct::Moved } else { Reduct::Kept }
    }

    /// How a reduct at `span` is written: kept inside a top-level form at
    /// `kept` or one the checker elaborates nothing for, moved elsewhere.
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
