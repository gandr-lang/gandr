//! Where the sugared form writes a `thunk { e }` as `e`, leaving the thunk
//! for the checker to insert.
//!
//! The checker inserts a thunk where it checks a computation against an
//! expected thunk type `+U B` of the default grade: a definition's body
//! against its signature, a function's argument against its parameter. There
//! a written `thunk { e }` and the bare `e` elaborate to one body, though they
//! lower to different cores — a thunk node, and the computation the checker
//! wraps — so a source rewritten this way is checked by the bodies the
//! checker elaborates ([`crate::Elaborate`]). Which thunks stand so is the
//! checker's to say, and it says so only by elaborating: the rewrite is tried
//! in every declaration, and where a declaration then elaborates otherwise —
//! one the checker refuses as written elaborates to nothing on either side —
//! its thunks stay as written and the formatting is tried again, with no
//! withdrawal reported: the rewrite did not apply there, as a `return` the
//! lowering would not infer stays. Without a checker no thunk is left out.
//!
//! Only a thunk of one expression, no statement before it and no grade
//! written, is left out: a statement block has no spelling but its braces, a
//! written grade is not the one the checker inserts, and a `become` leaves
//! only a thunk's body, never the body of a definition.

use alloc::vec::Vec;

use gandr_surface_syntax::ByteSpan;

use crate::leaf::Leaf;
use crate::leaf::Material;

/// Where the sugared form leaves a `thunk { e }` to the checker.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Thunks
{
    /// Whether a checker elaborates the source.
    reach: Reach,
    /// The spans, in the source's own offsets, of the top-level forms whose
    /// thunks stay as written: those the checker elaborates no body for, and
    /// those that elaborated otherwise with their thunks left out.
    kept: Vec<ByteSpan>,
}

/// Whether a checker elaborates the source, so a thunk can be left out.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Reach
{
    /// No checker: every thunk stays.
    #[default]
    Nowhere,
    /// A checker: a thunk outside the kept forms is left out.
    Outside,
}

/// How the sugared form writes a `thunk { e }`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Thunk
{
    /// The checker inserts it: written as `e`.
    Inserted,
    /// Written as it is.
    Kept,
}

impl Thunks
{
    /// Every thunk left out but those in `kept`: the spans, in the source's
    /// own offsets, of the top-level forms holding a declaration the checker
    /// elaborates no body for.
    ///
    /// # Specification
    /// trivial.
    pub fn outside(mut kept: Vec<ByteSpan>) -> Self
    {
        kept.sort_unstable();
        kept.dedup();
        Self {
            reach: Reach::Outside,
            kept,
        }
    }

    /// How the sugared form writes the thunks in the top-level forms at
    /// `forms`: kept when every one of the forms keeps them.
    ///
    /// # Specification
    /// trivial.
    pub fn kept(
        &self,
        forms: &[ByteSpan],
    ) -> Thunk
    {
        if forms
            .iter()
            .all(|form| self.kept.binary_search(form).is_ok())
        {
            Thunk::Kept
        }
        else {
            Thunk::Inserted
        }
    }

    /// Keep the thunks in the top-level forms at `forms` as written.
    ///
    /// # Specification
    /// trivial.
    pub fn keep(
        &mut self,
        forms: &[ByteSpan],
    )
    {
        for &form in forms {
            if let Err(at) = self.kept.binary_search(&form) {
                self.kept.insert(at, form);
            }
        }
    }

    /// How the sugared form writes the `thunk` form spanning `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn thunk(
        &self,
        span: ByteSpan,
    ) -> Thunk
    {
        let kept = self
            .kept
            .iter()
            .any(|form| form.start() <= span.start() && span.end() <= form.end());
        match (self.reach, kept) {
            (Reach::Outside, false) => Thunk::Inserted,
            (Reach::Outside, true) | (Reach::Nowhere, _) => Thunk::Kept,
        }
    }
}

/// Whether a source writes a `thunk` in some forms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Thunked
{
    /// It writes one.
    Written,
    /// It writes none.
    Unwritten,
}

/// Whether `leaves` write a `thunk` inside one of the top-level forms at
/// `forms`, or anywhere where `forms` is none.
///
/// # Specification
/// trivial.
pub fn thunked(
    leaves: &[Leaf<'_>],
    forms: Option<&[ByteSpan]>,
) -> Thunked
{
    let written = leaves.iter().any(|leaf| {
        leaf.material == Material::Token
            && <&str>::from(leaf.text) == "thunk"
            && forms.is_none_or(|forms| {
                forms
                    .iter()
                    .any(|form| form.start() <= leaf.span.start() && leaf.span.end() <= form.end())
            })
    });
    if written {
        Thunked::Written
    }
    else {
        Thunked::Unwritten
    }
}
