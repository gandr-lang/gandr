//! The prelude: a gandr source laid before every program and imported by each
//! of its sources without being written.
//!
//! # A source, not a table
//!
//! The prelude is [`TEXT`], a source written in gandr and embedded here. A
//! program's [`Unit`] lays it first ([`Unit::preluded`]), every other source
//! after it, and the collection answers a name a source neither declares nor
//! imports from the prelude's top level, after every import the source writes:
//! a declaration or a written import binding the name shadows it. It holds the
//! `Eq` theory, its models at `Integer` and `String` — each operation the
//! primitive at that type — and `eq`, the function over any model of `Eq` the
//! operands' type resolves, which `a == b` calls; and the binary naturals
//! `Pos` and `Nat`, which a numeral annotated `(n : Nat)` names.
//!
//! - Choice: one embedded source, the implicit first import of every unit, as
//!   every language's prelude is (Haskell's `Prelude`, OCaml's `Stdlib`, Lean's
//!   `Init`). It grows by source only: a theory, a model or a data type written
//!   in gandr. Its declarations are content as any import's are, so an
//!   incremental store holds them once for every program; every program's
//!   admission positions start after them.
//! - Alternatives: laying it only for a program that compares at a type other
//!   than `Integer` or names `Eq`, which makes a program's constant positions
//!   depend on whether one of its sources writes such a comparison, so one
//!   comparison added renumbers every declaration after it; theories and models
//!   built in Rust, a second way to make them beside the language's.
//! - Reversal: a package system whose standard library is a package lays that
//!   package's interface where this text stands.
//!
//! # `==` calls the prelude's `eq`
//!
//! `a == b` is the prelude's `eq` applied to its operands, its model of `Eq`
//! omitted and resolved by the sort the operands force (the lowering's
//! `lower::implicit`); at `Integer` the resolved model's operation is the
//! integer primitive, so the comparison runs as it did when `==` lowered to
//! the primitive directly. A unit with no prelude, which only a test lays,
//! keeps the primitive. `eq` is the name the native operator table gives
//! `==`'s row, and `==` calls the prelude's declaration of it whatever else a
//! source declares under that name: neither a source's own `eq` nor a
//! model's member `eq` is what its `==` means.
//!
//! # `(n : Nat)` is the prelude's binary natural
//!
//! A numeral annotated `(n : Nat)`, the name resolving to the prelude's `Nat`,
//! lowers to the constructor term its binary digits spell, the lowest
//! outermost (the lowering's `lower::natural`). The kernel keeps a closed
//! native opaque, so a natural ordered by conversion is a constructor term,
//! never an `Integer`. A source's own `Nat` shadows the prelude's there, and
//! its numerals stay integers.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;

use crate::unit::ImportTarget;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitFault;
use crate::unit::UnitSource;

/// The prelude's text.
pub const TEXT: &str = include_str!("prelude.gandr");

/// The name of the file the prelude's text is embedded from, which names the
/// prelude where a source would be named by its path; no file is read under
/// it.
pub const NAME: &str = "prelude.gandr";

/// Where the first source laid after the prelude starts: past its text and
/// the newline that separates them.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn base() -> ByteOffset
{
    ByteOffset::from(TEXT.len().saturating_add(1_usize))
}

/// The prelude laid before `text`, whose sources `unit` lays out: the unit's
/// text, and the unit.
///
/// # Specification
/// - requires: `unit` lays out `text` and lays no prelude.
/// - ensures: [`TEXT`], a newline, then `text`; the unit of the prelude then
///   `unit`'s sources, each starting [`base`] bytes later and each of its
///   imports' sources one position later, the prelude being the first.
/// - provides: the layout of a program a caller read and laid out without the
///   prelude.
/// - fails: [`UnitFault`] as [`Unit::preluded`], never for a `unit` that
///   [`Unit::new`] made.
/// - panics: none.
///
/// # Errors
/// [`UnitFault`].
///
/// # Adequacy
/// - hypothesis: L3 — a unit of two sources, the second importing the first,
///   laid after the prelude, keeps each source's text at its new start and its
///   import's target.
/// - witness: `unit::tests::a_preluded_unit_lays_the_prelude_first`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref laid, ref preluded)| laid.len() == usize::from(base()).saturating_add(text.as_ref().len()) && preluded.sources().len() == unit.sources().len().saturating_add(1_usize)))]
#[inline]
pub fn lay(
    text: SourceText<'_>,
    unit: &Unit,
) -> Result<(String, Unit), UnitFault>
{
    let text: &str = text.as_ref();
    let base = base();
    let mut laid = String::with_capacity(usize::from(base).saturating_add(text.len()));
    laid.push_str(TEXT);
    laid.push('\n');
    laid.push_str(text);
    let sources: Vec<UnitSource> = unit
        .sources()
        .iter()
        .map(|source| {
            UnitSource::new(
                ByteOffset::from(usize::from(source.start()).saturating_add(usize::from(base))),
                source
                    .imports()
                    .iter()
                    .map(|&target| match target {
                        ImportTarget::Source(imported) => ImportTarget::Source(SourceIndex::from(
                            usize::from(imported).saturating_add(1_usize),
                        )),
                        held @ (ImportTarget::Unresolved
                        | ImportTarget::Cycle
                        | ImportTarget::Unlocked) => held,
                    })
                    .collect(),
            )
        })
        .collect();

    Ok((laid, Unit::preluded(sources)?))
}
