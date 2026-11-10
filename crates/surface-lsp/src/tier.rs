//! Kernel tiers: how far the kernel certifies each declaration of an open
//! document, as a code lens above the declaration and as an entry of the
//! `gandr/kernelTiers` notification that an editor draws a gutter glyph from.
//!
//! The checker answers on the keystroke. The kernel replays the document's
//! declarations after it, off the keystroke path, in the revision's
//! admission. The judgement of a revision lists the declarations of the
//! document's own text ([`Declared`]), and each one that the checker accepts
//! is `pending` until the admission ends. The admission keeps one
//! [`KernelTier`] per declaration, and the document's copy takes them in
//! place of the pending marks ([`Tiers::settle`]). A lens request and the
//! notification read the copy, so no request computes a tier.
//!
//! Each tier maps onto one warrant of the visual language. The glyph and the
//! colour of a mark carry the warrant, and nothing else:
//!
//! | Kernel tier | Warrant | Glyph | Lens title |
//! | --- | --- | --- | --- |
//! | the admission has not ended | `pending` | `·` | `kernel pending` |
//! | replayed: a definition or a nominal declaration | `replayed` | `✓✓` | `kernel replayed` |
//! | assumed: the kernel owes the body | `checked` | `✓` | `kernel assumed: the body is owed` |
//! | refused: the kernel does not re-derive what the checker accepted | `refused` | `✗` | `kernel refused: <reason>` |
//! | withheld behind a declaration that did not cross | `withheld` | `○` | `kernel withheld: behind <name>` |
//! | outside the fragment | `withheld` | `○` | `kernel withheld: outside the fragment, <form> (<issue>)` |
//! | static | `withheld` | `○` | `kernel withheld: static, replayed where it is used` |
//! | unoffered: the checker refused it, suspended it or left a hole | none | none | none |
//!
//! An unoffered declaration draws nothing, because the checker's diagnostic
//! shows why. An assumed declaration takes the `checked` warrant, because the
//! kernel owes its body, and a mark never shows more than the kernel did. When
//! the kernel disagrees with the checker, the admission stops at that
//! declaration. It draws `refused` with the kernel's reason, and the
//! declarations after it draw nothing.
//!
//! When an admission ends, the server sends `gandr/kernelTiers` with the
//! document's version and one entry per marked declaration. It sends the
//! notification only to a client that declares `experimental.kernelTiers` at
//! `initialize`. Such a client draws each entry's glyph in its warrant's
//! colour, and it draws each glyph in the `pending` warrant once the document
//! moves past the notification's version.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the engine-surface
//!   blueprint (§ engine-surface-visual-warrant) — the five warrants, their
//!   glyphs and colours, and the map from the kernel's outcome classes.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: the core and kernel
//!   re-assessment (§ kernel-reassessment-design, item 9) — the editor shows
//!   each declaration's kernel tier, computed off the keystroke path.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_dispatcher::KernelTier;
use gandr_surface_dispatcher::Unruled;
use gandr_surface_render_remote::Glyph;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::Warrant;
use gandr_surface_session::KernelState;
use quenchant_shape::shape::Maybe;
use serde::Serialize;

use crate::goto::ranged;
use crate::position::Range;
use crate::protocol::CodeLens;
use crate::protocol::Command;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::recheck::Checked;
use crate::recheck::Declared;

/// Where the kernel stands on one declaration of an open document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tier
{
    /// The checker accepted it, and the revision's admission has not ended.
    Pending,
    /// The revision's admission ended at this tier.
    Settled(KernelTier),
    /// The kernel did not re-derive it, though the checker accepted it, for
    /// this reason: the admission stopped at it.
    Disagreed(Box<str>),
}

quenchant_shape::reason_enum! {
    /// Why a tier draws no mark.
    pub mod unmarked {
        /// The reason none is drawn.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The kernel was offered nothing, and the checker's diagnostic
            /// says why.
            Unoffered,
        }
    }
}

impl Tier
{
    /// The tier's warrant: none for an unoffered declaration.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: pending is `pending`; replayed is `replayed`; assumed is
    ///   `checked`; refused and disagreed are `refused`; withheld, outside and
    ///   static are `withheld`; unoffered is [`unmarked::Absent::Unoffered`].
    /// - provides: the warrant that the lens and the gutter both draw.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's declarations show their exact warrants
    ///   before and after its admission.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(Warrant::Pending) => *self == Self::Pending,
        Maybe::Present(Warrant::Replayed) => *self == Self::Settled(KernelTier::Replayed),
        Maybe::Present(Warrant::Checked) => *self == Self::Settled(KernelTier::Assumed),
        Maybe::Present(Warrant::Refused) => matches!(*self, Self::Settled(KernelTier::Refused(_)) | Self::Disagreed(_)),
        Maybe::Present(Warrant::Withheld) => matches!(*self, Self::Settled(
            KernelTier::Withheld { .. } | KernelTier::Outside { .. } | KernelTier::Static)),
        Maybe::Absent(unmarked::Absent::Unoffered) => *self == Self::Settled(KernelTier::Unoffered),
    })]
    #[inline]
    pub fn warrant(&self) -> Maybe<Warrant, unmarked::Absent>
    {
        match *self {
            Self::Pending => Maybe::Present(Warrant::Pending),
            Self::Settled(KernelTier::Replayed) => Maybe::Present(Warrant::Replayed),
            Self::Settled(KernelTier::Assumed) => Maybe::Present(Warrant::Checked),
            Self::Settled(KernelTier::Refused(_)) | Self::Disagreed(_) => {
                Maybe::Present(Warrant::Refused)
            },
            Self::Settled(
                KernelTier::Withheld { .. } | KernelTier::Outside { .. } | KernelTier::Static,
            ) => Maybe::Present(Warrant::Withheld),
            Self::Settled(KernelTier::Unoffered) => Maybe::Absent(unmarked::Absent::Unoffered),
        }
    }
}

/// One declaration of an open document with its kernel tier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tiered
{
    /// Its admission position in the document's report.
    constant: ConstantIndex,
    /// Its name, as the text spells it.
    name: Box<str>,
    /// Its range in the document's text.
    range: Range,
    /// Its tier.
    tier: Tier,
}

/// The kernel tiers of an open document's declarations, in admission order:
/// pending from its judgement until its admission ends.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Tiers
{
    /// The document's declarations, each with its tier.
    each: Vec<Tiered>,
}

impl Tiers
{
    /// The tiers of a judgement that lists `declared` over the text that
    /// `index` indexes: each declaration the checker refused is unoffered, and
    /// each one it accepted takes the kernel tier of its account row, which an
    /// earlier admission settled for the same content and verdict, or is
    /// pending.
    ///
    /// # Specification
    /// - requires: `declared` is in admission order, and its spans lie in the
    ///   text that `index` indexes.
    /// - ensures: one entry per declaration whose span has a range, in order; a
    ///   refused one unoffered; an accepted one at its row's settled tier, else
    ///   pending.
    /// - provides: what the document's copy holds between its judgement and its
    ///   admission.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's declarations read `kernel pending` before
    ///   its first admission ends, keep their tiers across an edit to a
    ///   comment, and an edited declaration alone reads `kernel pending` again.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    /// - witness: `server::tests::a_comment_edit_keeps_each_kernel_tier_6286`
    #[spec(captures: [listed = declared.iter().map(|declared| (declared.constant, Self::held(declared))).collect::<Vec<_>>()],
        ensures: |ret| ret.each.len() <= listed.len()
        && ret.each.iter().all(|tiered| listed.iter().any(|&(constant, ref tier)|
            constant == tiered.constant && tiered.tier == *tier)))]
    #[must_use]
    pub fn judged(
        declared: Vec<Declared>,
        index: &LineIndex<'_>,
    ) -> Self
    {
        Self {
            each: declared
                .into_iter()
                .filter_map(|declared| {
                    Some(Tiered {
                        constant: declared.constant,
                        range: ranged(index, declared.span)?,
                        tier: Self::held(&declared),
                        name: declared.name,
                    })
                })
                .collect(),
        }
    }

    /// The tier a judgement shows for `declared`: unoffered when the checker
    /// refused it, its account row's settled tier when it has one, and pending
    /// otherwise.
    ///
    /// # Specification
    /// trivial.
    fn held(declared: &Declared) -> Tier
    {
        match (declared.checked, declared.row) {
            (Checked::Refused, _) => Tier::Settled(KernelTier::Unoffered),
            (Checked::Accepted, Maybe::Present(row)) => match row.kernel() {
                KernelState::Settled(tier) => Tier::Settled(tier),
                KernelState::Pending => Tier::Pending,
            },
            (Checked::Accepted, Maybe::Absent(_)) => Tier::Pending,
        }
    }

    /// These tiers once the admission settled `settled`.
    ///
    /// # Specification
    /// - requires: `settled` is sorted by its positions, as an admission lists
    ///   them.
    /// - ensures: each declaration takes the tier settled at its position, and
    ///   one that the admission did not settle is unoffered; the order and the
    ///   ranges stay.
    /// - provides: the tiers that the lens and the notification read until the
    ///   next judgement.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module that imports another, admitted after a first
    ///   admission resumed part of its closure, shows each of its own
    ///   declarations' tiers at its own line.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(captures: [count = self.each.len()], ensures: |()| self.each.len() == count)]
    pub fn settle(
        &mut self,
        settled: Vec<(ConstantIndex, Tier)>,
    )
    {
        let mut settled = settled.into_iter().peekable();
        for tiered in &mut self.each {
            while settled
                .next_if(|&(constant, _)| constant < tiered.constant)
                .is_some()
            {}
            tiered.tier = settled
                .next_if(|&(constant, _)| constant == tiered.constant)
                .map_or(Tier::Settled(KernelTier::Unoffered), |(_, tier)| tier);
        }
    }

    /// The lens title of `tier`: its warrant's name in the kernel, then its
    /// reason; none for an unmarked tier.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `tier` has a warrant; it starts `kernel
    ///   `, and a withheld tier names the declaration it waits on when that
    ///   declaration is the document's own.
    /// - provides: the title of the lens and of the notification's entry.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's declarations show their exact titles
    ///   before and after its admission.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(ref title) => title.starts_with("kernel ") && matches!(tier.warrant(), Maybe::Present(_)),
        Maybe::Absent(_) => matches!(tier.warrant(), Maybe::Absent(_)),
    })]
    fn title(
        &self,
        tier: &Tier,
    ) -> Maybe<String, unmarked::Absent>
    {
        Maybe::Present(match *tier {
            Tier::Pending => String::from("kernel pending"),
            Tier::Settled(KernelTier::Replayed) => String::from("kernel replayed"),
            Tier::Settled(KernelTier::Assumed) => String::from("kernel assumed: the body is owed"),
            Tier::Settled(KernelTier::Refused(class)) => {
                alloc::format!("kernel refused: {class}")
            },
            Tier::Disagreed(ref reason) => alloc::format!("kernel refused: {reason}"),
            Tier::Settled(KernelTier::Withheld { behind }) => self
                .each
                .binary_search_by_key(&behind, |tiered| tiered.constant)
                .ok()
                .and_then(|found| self.each.get(found))
                .map_or_else(
                    || String::from("kernel withheld: behind an imported declaration"),
                    |named| alloc::format!("kernel withheld: behind {}", named.name),
                ),
            Tier::Settled(KernelTier::Outside { form, class }) => {
                let form = match form {
                    Unruled::Former(former) => alloc::format!("{former:?}"),
                    Unruled::Session => String::from("a session"),
                    Unruled::Located => String::from("a located form"),
                };
                match class.tracking() {
                    Maybe::Present(issue) => {
                        alloc::format!("kernel withheld: outside the fragment, {form} ({issue})")
                    },
                    Maybe::Absent(_) => {
                        alloc::format!("kernel withheld: outside the fragment, {form}")
                    },
                }
            },
            Tier::Settled(KernelTier::Static) => {
                String::from("kernel withheld: static, replayed where it is used")
            },
            Tier::Settled(KernelTier::Unoffered) => {
                return Maybe::Absent(unmarked::Absent::Unoffered);
            },
        })
    }

    /// One mark per marked declaration, in order: its range, its warrant and
    /// its title. Two declarations at one range with one title, as a module
    /// member and the member its signature exports, draw one mark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per marked declaration whose range and title differ
    ///   from the entry before it, in order, each title starting `kernel `.
    /// - provides: what the lenses and the notification both draw.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's declarations each show one mark at their
    ///   own lines, with the exact title.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(ensures: |ref ret| ret.len() <= self.each.len()
        && ret.iter().all(|&(_, _, ref title)| title.starts_with("kernel "))
        && ret.windows(2).all(|pair| matches!(pair, [earlier, later]
            if earlier.0 != later.0 || earlier.2 != later.2)))]
    #[must_use]
    fn marks(&self) -> Vec<(Range, Warrant, String)>
    {
        let mut marks: Vec<(Range, Warrant, String)> = Vec::with_capacity(self.each.len());
        for tiered in &self.each {
            let (Maybe::Present(warrant), Maybe::Present(title)) =
                (tiered.tier.warrant(), self.title(&tiered.tier))
            else {
                continue;
            };
            if marks
                .last()
                .is_some_and(|&(range, _, ref last)| range == tiered.range && *last == title)
            {
                continue;
            }
            marks.push((tiered.range, warrant, title));
        }
        marks
    }

    /// One lens above each mark, titled with its tier, running no command.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one lens per mark, in order, at its range, with a title
    ///   starting `kernel `, no command name, no arguments and no data.
    /// - provides: the tier lenses of `textDocument/codeLens`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's declarations each show one lens at their
    ///   own lines, with the exact title.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(ensures: |ref ret| ret.len() <= self.each.len()
        && ret.iter().all(|lens| lens.data.is_none() && lens.command.as_ref().is_some_and(|command|
            command.name.is_empty() && command.arguments.is_empty() && command.title.starts_with("kernel "))))]
    #[must_use]
    pub fn lenses(&self) -> Vec<CodeLens>
    {
        self.marks()
            .into_iter()
            .map(|(range, _, title)| CodeLens {
                range,
                command: Some(Command {
                    title,
                    name: "",
                    arguments: Vec::new(),
                }),
                data: None,
            })
            .collect()
    }

    /// The parameters of `gandr/kernelTiers` for the document at `uri`, at
    /// `version`: one entry per mark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the URI and the version as given; one entry per mark, in
    ///   order, at its range, with its warrant, the warrant's glyph and the
    ///   title its lens shows.
    /// - provides: what the extension draws its gutter glyphs from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's admission notifies each marked
    ///   declaration's exact warrant and its glyph.
    /// - witness: `server::tests::each_declaration_shows_its_kernel_tier_2517`
    #[spec(ensures: |ref ret| ret.uri == *uri && ret.version == version
        && ret.tiers.len() <= self.each.len()
        && ret.tiers.iter().all(|mark| mark.glyph == mark.warrant.glyph()))]
    #[must_use]
    pub fn notified(
        &self,
        uri: &DocumentUri,
        version: DocumentVersion,
    ) -> KernelTiersParams
    {
        KernelTiersParams {
            uri: uri.clone(),
            version,
            tiers: self
                .marks()
                .into_iter()
                .map(|(range, warrant, title)| TierMark {
                    range,
                    warrant,
                    glyph: warrant.glyph(),
                    title,
                })
                .collect(),
        }
    }
}

/// The parameters of `gandr/kernelTiers`: the kernel tiers of one open
/// document at one version.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct KernelTiersParams
{
    /// The document.
    pub uri: DocumentUri,
    /// The version whose admission settled the tiers.
    pub version: DocumentVersion,
    /// One entry per marked declaration, in the document's order.
    pub tiers: Vec<TierMark>,
}

/// One declaration's mark: where it is, its warrant, the warrant's glyph and
/// the title its lens shows.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TierMark
{
    /// The declaration's range.
    pub range: Range,
    /// Its warrant.
    pub warrant: Warrant,
    /// The warrant's glyph.
    pub glyph: Glyph,
    /// The title its lens shows.
    pub title: String,
}
