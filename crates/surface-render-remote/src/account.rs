//! The account card: one mutable block per declaration of a document, keyed
//! by the declaration's content, and the edits that move a renderer's copy of
//! the blocks from one state to the next.
//!
//! An [`AccountCard`] holds the checker's verdict, the kernel tier as its
//! warrant and its title, and the compile tier. Its counts and its timing stay
//! absent until the layers that measure them fill them, and an absent field
//! takes no bytes on the wire. The hub sends a renderer the whole list once,
//! then the [`account_edits`] between the list it sent and the list that the
//! account holds now. A list that did not change owes no edit, so an edit to a
//! comment sends nothing. [`apply_account_edits`] applies the edits in order.
//!
//! # Keys
//!
//! A key is the declaration's content key as 32 hexadecimal digits. The
//! content names no position and no name, so two declarations of one content
//! share a key. The producer gives the n-th repeat in document order the
//! suffix `#n`, so each key names one card of a list.
//!
//! # Edits
//!
//! The edits drop each held card that the new list does not keep, in the held
//! order. Then they put each card of the new list that is new or changed at
//! its position, in ascending order. A card is kept when its key is in both
//! lists and its held position follows the position of the card kept before
//! it. So the kept cards keep their order, and a card that moved is dropped
//! and put again. A put replaces the card at its position when that card has
//! the same key, and it goes before that card otherwise.
//!
//! The edits carry each changed card alone, and the diff takes one lookup for
//! each card of the two lists.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::visual::Count;
use crate::visual::Samples;
use crate::visual::Warrant;

/// The key of an account card: the declaration's content key as 32
/// hexadecimal digits, with `#n` after the n-th repeat of one content in a
/// document.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AccountKey(String);

impl From<String> for AccountKey
{
    /// The key spelled `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for AccountKey
{
    /// The key's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for AccountKey
{
    /// Write the key's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The checker's verdict on a declaration.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CheckerVerdict
{
    /// A nominal declaration that formed.
    Data,
    /// The body checked against the declared type.
    Checked,
    /// The unsigned body synthesised its type.
    Synthesised,
    /// The body is a hole under a declared type, owed.
    Owed,
    /// The declaration waits on owed holes.
    Suspended,
    /// The lowering, the checker or the corpus refused the declaration.
    Refused,
}

impl From<CheckerVerdict> for &'static str
{
    /// The verdict's name, as a face writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(verdict: CheckerVerdict) -> Self
    {
        match verdict {
            CheckerVerdict::Data => "data",
            CheckerVerdict::Checked => "checked",
            CheckerVerdict::Synthesised => "synthesised",
            CheckerVerdict::Owed => "owed",
            CheckerVerdict::Suspended => "suspended",
            CheckerVerdict::Refused => "refused",
        }
    }
}

/// How the emitter compiled a declaration.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompileTier
{
    /// The portable interpreter runs it.
    Interpreted,
    /// Stencil code runs it.
    Stencil,
    /// Code that the optimiser built runs it.
    Optimised,
}

impl From<CompileTier> for &'static str
{
    /// The tier's name, as a face writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tier: CompileTier) -> Self
    {
        match tier {
            CompileTier::Interpreted => "interpreted",
            CompileTier::Stencil => "stencil",
            CompileTier::Optimised => "optimised",
        }
    }
}

/// Where the kernel stands on a declaration: the warrant that its mark
/// draws, and the title that says why.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct KernelMark
{
    /// The warrant: the checker's while the kernel has not settled the
    /// declaration, the kernel's or the attested cache's once it has.
    pub warrant: Warrant,
    /// The title, as the declaration's lens shows it.
    pub title: String,
}

/// The engine's counts for one declaration in its latest recheck: the
/// checker's and the kernel's apart.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct AccountCounts
{
    /// The goals the checker's memo answered.
    pub hits: Count,
    /// The goals the checker's memo keyed and held no answer for.
    pub misses: Count,
    /// The arena nodes of its lowering and its judgement.
    pub nodes: Count,
    /// The forms of its halves that the parser molded.
    pub molded: Count,
    /// One when the incremental checker judged it, zero when it adopted it.
    pub judged: Count,
    /// One when it crossed to the kernel again.
    pub crossed: Count,
    /// The parse's completion obligations inside its halves.
    pub obligations: Count,
    /// The goals of the kernel's check that the kernel's memo recalled.
    pub recalled: Count,
    /// The goals of the kernel's check that the kernel expanded.
    pub expanded: Count,
    /// The goals of the kernel's check that a kept outcome answered.
    pub kept: Count,
}

/// One declaration's block of the account: its verdict, its tiers, and the
/// fields that the layers of the instrument fill.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct AccountCard
{
    /// The card's key.
    pub key: AccountKey,
    /// The declaration's name, as the text spells it.
    pub name: String,
    /// The checker's verdict.
    pub verdict: CheckerVerdict,
    /// Where the kernel stands; absent when the checker offered the kernel
    /// nothing, and the diagnostic says why.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub kernel: Option<KernelMark>,
    /// How the emitter compiled it; absent until it did.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub compile: Option<CompileTier>,
    /// The counts of its judgement; absent until the counts layer fills them.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub counts: Option<AccountCounts>,
    /// The wall time of its judgement in each of its last rechecks; absent
    /// until the timings layer fills it.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub timing: Option<Samples>,
}

/// One edit of a renderer's list of account cards.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum AccountEdit
{
    /// Put `card` at the zero-based position `at`: in place of the card there
    /// when that card has the same key, and before it otherwise.
    Put
    {
        /// The position.
        at: usize,
        /// The card.
        card: AccountCard,
    },
    /// Drop the card whose key is `key`.
    Drop
    {
        /// The key.
        key: AccountKey,
    },
}

/// The edits that take `held`, a list of cards in document order, to
/// `latest`.
///
/// # Specification
/// - requires: the keys of each list are distinct.
/// - ensures: [`apply_account_edits`] of the edits takes `held` to `latest`.
///   Equal lists owe no edit. The drops come first, in the held order, and the
///   puts follow, in ascending position. A card that is kept and unchanged owes
///   nothing.
/// - provides: the patch that the hub owes a renderer after a change.
/// - fails: never.
/// - panics: none.
/// - intension: one lookup for each card of either list, so the work is linear
///   in the cards up to the map's logarithm, and the edits are linear in the
///   cards that changed.
///
/// # Adequacy
/// - hypothesis: L2 — every pair of lists over four keys, each card at one of
///   two states, is taken to its latest list, and an unchanged list owes no
///   edit; L3 — a changed tier puts one card in place, and a changed
///   declaration drops its old key and puts its new one.
/// - witness: `account::tests::the_edits_take_every_list_to_every_other`
/// - witness: `account::tests::a_changed_tier_puts_one_card_in_place`
/// - witness: `account::tests::a_changed_declaration_drops_its_key_and_puts_the_new_one`
#[spec(ensures: |ref ret| (held != latest || ret.is_empty()) && {
    let mut moved = held.to_vec();
    apply_account_edits(&mut moved, ret.clone());
    moved == latest
})]
#[inline]
#[must_use]
pub fn account_edits(
    held: &[AccountCard],
    latest: &[AccountCard],
) -> Vec<AccountEdit>
{
    let positions: BTreeMap<&AccountKey, usize> = held
        .iter()
        .enumerate()
        .map(|(position, card)| (&card.key, position))
        .collect();
    // Each card of `latest` with the held position it keeps, when it keeps
    // one: the kept positions ascend, so the kept cards keep their order.
    let mut last: Option<usize> = None;
    let kept: Vec<Option<usize>> = latest
        .iter()
        .map(|card| {
            let position = positions
                .get(&card.key)
                .copied()
                .filter(|&position| last.is_none_or(|before| position > before))?;
            last = Some(position);
            Some(position)
        })
        .collect();
    let mut stays = alloc::vec![false; held.len()];
    for &position in kept.iter().flatten() {
        if let Some(stay) = stays.get_mut(position) {
            *stay = true;
        }
    }
    let mut edits: Vec<AccountEdit> = held
        .iter()
        .zip(&stays)
        .filter(|&(_, &stay)| !stay)
        .map(|(card, _)| AccountEdit::Drop {
            key: card.key.clone(),
        })
        .collect();
    edits.extend(
        latest
            .iter()
            .zip(&kept)
            .enumerate()
            .filter(|&(_, (card, &position))| {
                position
                    .and_then(|position| held.get(position))
                    .is_none_or(|before| before != card)
            })
            .map(|(at, (card, _))| AccountEdit::Put {
                at,
                card: card.clone(),
            }),
    );
    edits
}

/// Apply `edits` to `held`, in order.
///
/// # Specification
/// - requires: nothing; an edit that names no card is admissible input.
/// - ensures: a drop removes the card with its key, and changes nothing when
///   `held` has none. A put replaces the card at its position when that card
///   has the put card's key, and goes before it otherwise; a position past the
///   end puts the card at the end.
/// - provides: the step by which a renderer follows the hub's account.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — as [`account_edits`], whose edits this applies.
/// - witness: `account::tests::the_edits_take_every_list_to_every_other`
#[spec(captures: [puts = edits.iter().filter(|edit| matches!(edit, AccountEdit::Put { .. })).count(),
    count = held.len()],
    ensures: |()| held.len() <= count.saturating_add(puts))]
#[inline]
pub fn apply_account_edits(
    held: &mut Vec<AccountCard>,
    edits: Vec<AccountEdit>,
)
{
    for edit in edits {
        match edit {
            AccountEdit::Drop { key } => held.retain(|card| card.key != key),
            AccountEdit::Put { at, card } => match held.get_mut(at) {
                Some(there) if there.key == card.key => *there = card,
                Some(_) => held.insert(at, card),
                None => held.push(card),
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::vec::Vec;

    use super::AccountCard;
    use super::AccountEdit;
    use super::AccountKey;
    use super::CheckerVerdict;
    use super::KernelMark;
    use super::account_edits;
    use super::apply_account_edits;
    use crate::visual::Warrant;

    /// A key of the test lists.
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum Key
    {
        /// The key `a`.
        A,
        /// The key `b`.
        B,
        /// The key `c`.
        C,
        /// The key `d`.
        D,
        /// The key `x`.
        X,
    }

    impl Key
    {
        /// The text of the key, which is also the name of its declaration.
        ///
        /// # Specification
        /// trivial.
        fn text(self) -> String
        {
            String::from(match self {
                Self::A => "a",
                Self::B => "b",
                Self::C => "c",
                Self::D => "d",
                Self::X => "x",
            })
        }
    }

    /// The card keyed `key`, its kernel tier at `warrant`.
    ///
    /// # Specification
    /// trivial.
    fn card(
        key: Key,
        warrant: Warrant,
    ) -> AccountCard
    {
        AccountCard {
            key: AccountKey::from(key.text()),
            name: key.text(),
            verdict: CheckerVerdict::Checked,
            kernel: Some(KernelMark {
                warrant,
                title: String::from("kernel"),
            }),
            compile: None,
            counts: None,
            timing: None,
        }
    }

    /// Every list of distinct keys out of `keys`, in every order, each card
    /// pending or replayed.
    ///
    /// # Specification
    /// trivial.
    fn lists(keys: &[Key]) -> Vec<Vec<AccountCard>>
    {
        let mut lists = Vec::from([Vec::new()]);
        let mut frontier: Vec<(Vec<AccountCard>, BTreeSet<Key>)> =
            Vec::from([(Vec::new(), BTreeSet::new())]);
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for (list, used) in frontier {
                for &key in keys {
                    if used.contains(&key) {
                        continue;
                    }
                    for warrant in [Warrant::Pending, Warrant::Replayed] {
                        let mut longer = list.clone();
                        longer.push(card(key, warrant));
                        let mut using = used.clone();
                        let _new = using.insert(key);
                        lists.push(longer.clone());
                        next.push((longer, using));
                    }
                }
            }
            frontier = next;
        }
        lists
    }

    #[test]
    fn the_edits_take_every_list_to_every_other()
    {
        let lists = lists(&[Key::A, Key::B, Key::C, Key::D]);
        assert_eq!(lists.len(), 633, "every list over four keys at two states");
        let mut moved = Vec::new();
        for held in &lists {
            for latest in &lists {
                let edits = account_edits(held, latest);
                moved.clone_from(held);
                apply_account_edits(&mut moved, edits.clone());
                assert_eq!(&moved, latest, "{held:?} to {latest:?} by {edits:?}");
                if held == latest {
                    assert!(edits.is_empty(), "an unchanged list owes no edit");
                }
            }
        }
    }

    #[test]
    fn a_changed_tier_puts_one_card_in_place()
    {
        let held = Vec::from([
            card(Key::A, Warrant::Replayed),
            card(Key::B, Warrant::Pending),
            card(Key::C, Warrant::Replayed),
        ]);
        let latest = Vec::from([
            card(Key::A, Warrant::Replayed),
            card(Key::B, Warrant::Replayed),
            card(Key::C, Warrant::Replayed),
        ]);
        assert_eq!(account_edits(&held, &latest), [AccountEdit::Put {
            at: 1,
            card: card(Key::B, Warrant::Replayed),
        }]);
    }

    #[test]
    fn a_changed_declaration_drops_its_key_and_puts_the_new_one()
    {
        let held = Vec::from([
            card(Key::A, Warrant::Replayed),
            card(Key::B, Warrant::Replayed),
            card(Key::C, Warrant::Replayed),
        ]);
        let latest = Vec::from([
            card(Key::A, Warrant::Replayed),
            card(Key::X, Warrant::Pending),
            card(Key::C, Warrant::Replayed),
        ]);
        assert_eq!(account_edits(&held, &latest), [
            AccountEdit::Drop {
                key: AccountKey::from(Key::B.text()),
            },
            AccountEdit::Put {
                at: 1,
                card: card(Key::X, Warrant::Pending),
            },
        ]);
    }

    #[test]
    fn an_absent_field_takes_no_bytes_on_the_wire()
    {
        let image = serde_json::to_value(card(Key::A, Warrant::Pending)).expect("a card encodes");
        assert_eq!(
            image,
            serde_json::json!({
                "key": "a",
                "name": "a",
                "verdict": "checked",
                "kernel": { "warrant": "pending", "title": "kernel" },
            }),
            "the counts, the timing and the compile tier are left out"
        );
        let decoded: AccountCard = serde_json::from_value(image).expect("a card decodes");
        assert_eq!(decoded, card(Key::A, Warrant::Pending));
    }
}
