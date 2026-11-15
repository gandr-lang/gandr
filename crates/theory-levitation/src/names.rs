//! The names of the levitation code: the table that a description owns, and
//! the id that a name of its code holds.
//!
//! A name of the levitation code is an id, the index of its text in the table
//! of the description that holds it. The lowering session mints each name into
//! the table once, at its decode, and the table stays with the description
//! after the session ends. So a copy of a term that holds ids copies each id
//! and no text.
//!
//! The table keeps the text of each distinct name once, in the order of
//! minting, and its ids in the order of their text. The order of minting is
//! deterministic, but it is not the order of the text: a reader that sorts by
//! text sorts through [`Names::compare`], and an id has no order of its own.
//!
//! A [`FreeTerm`] is generic in its names over [`TermName`]: its builders take
//! text, and a decode mints the form that holds ids.
//!
//! [`FreeTerm`]: crate::FreeTerm
//!
//! # References
//! - `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: line 1 of the
//!   performance picture. The steady state of a worker allocates nothing, so a
//!   name of a code is an id into its description's table, and a copy of a term
//!   copies its ids.

use alloc::alloc::Global;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::NameRef;
use crate::code::Name;

/// A name of the levitation code: the index of its text in its description's
/// [`Names`].
///
/// An id has no order: the order of ids is the order of minting, not the
/// order of the text. [`Names::compare`] orders two ids by their text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NameId(u32);

impl From<NameId> for usize
{
    /// The id's index in its table: the place of its entry in a table that a
    /// reader keeps by id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: NameId) -> Self
    {
        Self::try_from(id.0).unwrap_or(Self::MAX)
    }
}

/// The text of a numbered name, written on the stack: a `char` takes at most 4
/// bytes and a `usize` at most 20 digits, so 24 bytes hold it.
struct Numbered
{
    /// The bytes written so far, then zeros.
    bytes: [u8; 24],
    /// How many bytes are written.
    len: usize,
}

impl fmt::Write for Numbered
{
    /// Append `s` to the bytes written: a text that does not fit is the
    /// formatter's error.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_str(
        &mut self,
        s: &str,
    ) -> fmt::Result
    {
        let end = self.len.checked_add(s.len()).ok_or(fmt::Error)?;
        let slot = self.bytes.get_mut(self.len .. end).ok_or(fmt::Error)?;
        slot.copy_from_slice(s.as_bytes());
        self.len = end;
        Ok(())
    }
}

quenchant_shape::reason_enum! {
    /// Why a table holds no text for an id.
    pub mod name_text {
        /// The reason the table holds no text for the id.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The id is past the table's last name: another table minted it.
            Unminted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a table mints no id for a name.
    pub mod name_mint {
        /// The reason the table mints no id.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The table holds 2³² names or 4 GiB of text, the bound of the
            /// `u32` an id and an end are.
            Full,
        }
    }
}

/// The table of a description's names: the text of each distinct name once,
/// by its [`NameId`], in the allocator `A`.
///
/// Two tables are equal when they hold the same texts in the same order of
/// minting, so an id names the same text in both.
#[derive(Clone, Debug)]
pub struct Names<A = Global>
where
    A: Allocator,
{
    /// The text of every name, in the order of minting.
    text: Vec<u8, A>,
    /// The end of each name's text in `text`, by id.
    ends: Vec<u32, A>,
    /// Every id, in the order of its text.
    sorted: Vec<NameId, A>,
}

impl Names
{
    /// An empty table over the global allocator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::new_in(Global)
    }
}

impl<A> Default for Names<A>
where
    A: Allocator + Clone + Default,
{
    /// An empty table over the allocator's default.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new_in(A::default())
    }
}

impl<A> Names<A>
where
    A: Allocator + Clone,
{
    /// An empty table over `alloc`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new_in(alloc: A) -> Self
    {
        Self {
            text: Vec::new_in(alloc.clone()),
            ends: Vec::new_in(alloc.clone()),
            sorted: Vec::new_in(alloc),
        }
    }

    /// The id of `name`, minted when the table holds no name of its text.
    ///
    /// # Specification
    /// - ensures: the id the table reads back as `name`; a second mint of the
    ///   same text gives the same id, and two texts get two ids.
    /// - fails: [`name_mint::Absent::Full`] when one more name passes the `u32`
    ///   bound of an id or of the text's end.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the text, its end and its order, growth within the table
    ///
    /// # Adequacy
    /// - hypothesis: L3 — names minted out of text order, a name minted twice,
    ///   and the empty name read back as their texts; a mint that keeps no
    ///   order or mints a text twice changes the ids or the order.
    /// - witness: `names::tests::a_name_minted_twice_keeps_its_one_id`
    /// - witness: `names::tests::each_id_reads_back_as_the_text_it_was_minted_from`
    #[inline]
    #[spec(ensures: |ref minted| match *minted {
        | Maybe::Present(id) => self.text(id) == Maybe::Present(name),
        | Maybe::Absent(_) => true,
    })]
    pub fn mint(
        &mut self,
        name: NameRef<'_>,
    ) -> Maybe<NameId, name_mint::Absent>
    {
        let spelled = name.as_ref().as_bytes();
        let at = match self
            .sorted
            .binary_search_by(|&held| self.order(held).cmp(&name))
        {
            Ok(at) => match self.sorted.get(at) {
                Some(&held) => return Maybe::Present(held),
                None => at,
            },
            Err(at) => at,
        };
        let (Ok(id), Ok(end)) = (
            u32::try_from(self.ends.len()),
            u32::try_from(self.text.len().saturating_add(spelled.len())),
        )
        else {
            return Maybe::Absent(name_mint::Absent::Full);
        };
        self.text.extend_from_slice(spelled);
        self.ends.push(end);
        let id = NameId(id);
        self.sorted.insert(at, id);
        Maybe::Present(id)
    }

    /// The id of the name `prefix` followed by `number` in decimal, `x3` or
    /// `_1`, minted when the table holds no name of its text.
    ///
    /// # Specification
    /// - ensures: the id that [`Self::mint`] gives the text.
    /// - fails: as [`Self::mint`].
    /// - panics: none.
    /// - executable: none — the clause would spell the number again, which is
    ///   the body's work.
    ///
    /// # Cost
    /// - allocation: as [`Self::mint`], growth within the table
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a numbered name and the same text minted whole get
    ///   one id, and the largest number reads back whole.
    /// - witness: `names::tests::a_numbered_name_is_the_name_of_its_text`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            primitive_signature,
            reason = "a numbered name is spelled from a character and a number, the parts of its text"
        )
    )]
    pub fn mint_numbered(
        &mut self,
        prefix: char,
        number: usize,
    ) -> Maybe<NameId, name_mint::Absent>
    {
        let mut spelled = Numbered {
            bytes: [0_u8; 24],
            len: 0,
        };
        let written = fmt::Write::write_fmt(&mut spelled, format_args!("{prefix}{number}"));
        let text = spelled.bytes.get(.. spelled.len).map(core::str::from_utf8);
        match (written, text) {
            (Ok(()), Some(Ok(text))) => self.mint(NameRef::from(text)),
            (Err(_), _) | (_, Some(Err(_)) | None) => Maybe::Absent(name_mint::Absent::Full),
        }
    }
}

impl<A> Names<A>
where
    A: Allocator,
{
    /// The text of `id`.
    ///
    /// # Specification
    /// - ensures: the text `id` was minted from, for an id this table minted.
    /// - fails: [`name_text::Absent::Unminted`] for an id past the table's last
    ///   name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint`], and an id that another, larger
    ///   table minted is absent here.
    /// - witness: `names::tests::each_id_reads_back_as_the_text_it_was_minted_from`
    /// - witness: `names::tests::an_id_past_the_table_reads_no_text`
    #[inline]
    #[spec(ensures: |ref read| matches!(*read, Maybe::Present(_)) == (usize::try_from(id.0).is_ok_and(|index| index < self.ends.len())))]
    pub fn text(
        &self,
        id: NameId,
    ) -> Maybe<NameRef<'_>, name_text::Absent>
    {
        let unminted = Maybe::Absent(name_text::Absent::Unminted);
        let index = usize::from(id);
        let start = index.checked_sub(1).map_or(0_u32, |before| {
            self.ends.get(before).copied().unwrap_or_default()
        });
        let Some(&end) = self.ends.get(index)
        else {
            return unminted;
        };
        let range = usize::try_from(start).unwrap_or(usize::MAX)
            .. usize::try_from(end).unwrap_or(usize::MAX);
        match self.text.get(range).map(core::str::from_utf8) {
            Some(Ok(text)) => Maybe::Present(NameRef::from(text)),
            Some(Err(_)) | None => unminted,
        }
    }

    /// The order of `left` and `right` by their text: the order a reader
    /// that sorts names by text holds.
    ///
    /// # Specification
    /// - ensures: the order of the two texts as strings; an id this table did
    ///   not mint orders as the empty text.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — names minted against their text order compare by
    ///   text, so an order by id fails the witness.
    /// - witness: `names::tests::ids_minted_out_of_text_order_compare_by_text`
    #[inline]
    #[must_use]
    #[spec(ensures: |ord| ord == self.order(left).cmp(&self.order(right)))]
    pub fn compare(
        &self,
        left: NameId,
        right: NameId,
    ) -> Ordering
    {
        self.order(left).cmp(&self.order(right))
    }

    /// The text of `id` as the order reads it: the empty text for an id this
    /// table did not mint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn order(
        &self,
        id: NameId,
    ) -> NameRef<'_>
    {
        match self.text(id) {
            Maybe::Present(text) => text,
            Maybe::Absent(_) => NameRef::from(""),
        }
    }
}

impl<A> PartialEq for Names<A>
where
    A: Allocator,
{
    /// Whether the two tables hold the same texts in the same order of
    /// minting.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.ends == other.ends && self.text == other.text
    }
}

impl<A> Eq for Names<A> where A: Allocator
{
}

impl<A> Hash for Names<A>
where
    A: Allocator,
{
    /// Hashes the texts and their order of minting, as equality reads them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: Hasher,
    {
        self.text.hash(state);
        self.ends.hash(state);
    }
}

/// The names a [`FreeTerm`] holds: the text of a builder, or the id of a
/// description's table.
///
/// [`FreeTerm`]: crate::FreeTerm
pub trait TermName: Clone + fmt::Debug + Eq + Hash
{
    /// The name's text: its own for a text, its entry in `names` for an id.
    ///
    /// # Specification
    /// - ensures: a text reads as itself; an id reads as [`Names::text`] reads
    ///   it.
    /// - fails: [`name_text::Absent::Unminted`] for an id that `names` did not
    ///   mint.
    /// - panics: none.
    /// - executable: none — each impl's body is the reading the clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a text and the id minted from it spell alike.
    /// - witness: `names::tests::a_text_and_its_id_spell_alike`
    fn spelled<'name, A>(
        &'name self,
        names: &'name Names<A>,
    ) -> Maybe<NameRef<'name>, name_text::Absent>
    where
        A: Allocator;
}

impl TermName for Name
{
    /// The name's own text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn spelled<'name, A>(
        &'name self,
        _names: &'name Names<A>,
    ) -> Maybe<NameRef<'name>, name_text::Absent>
    where
        A: Allocator,
    {
        Maybe::Present(self.as_name_ref())
    }
}

impl TermName for NameId
{
    /// The id's entry in `names`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn spelled<'name, A>(
        &'name self,
        names: &'name Names<A>,
    ) -> Maybe<NameRef<'name>, name_text::Absent>
    where
        A: Allocator,
    {
        names.text(*self)
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// Mint `text` into `names`, which has room.
    ///
    /// # Specification
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(primitive_signature, reason = "a fixture mints the text a test writes")
    )]
    fn minted(
        names: &mut Names,
        text: &str,
    ) -> NameId
    {
        match names.mint(NameRef::from(text)) {
            Maybe::Present(id) => id,
            Maybe::Absent(absent) => panic!("a table with room mints {text}: {absent:?}"),
        }
    }

    #[test]
    fn a_name_minted_twice_keeps_its_one_id()
    {
        let mut names = Names::new();
        let mul = minted(&mut names, "mul");
        let inv = minted(&mut names, "inv");
        assert_ne!(mul, inv);
        assert_eq!(minted(&mut names, "mul"), mul);
        assert_eq!(minted(&mut names, "inv"), inv);
        let mut fresh = Names::new();
        let _mul = minted(&mut fresh, "mul");
        let _inv = minted(&mut fresh, "inv");
        assert_eq!(names, fresh, "a second mint of a held text adds nothing");
    }

    #[test]
    fn each_id_reads_back_as_the_text_it_was_minted_from()
    {
        let mut names = Names::new();
        let texts = ["mul", "a", "", "Carrier", "inv", "b"];
        let ids: Vec<NameId> = texts.iter().map(|text| minted(&mut names, text)).collect();
        for (&text, &id) in texts.iter().zip(&ids) {
            assert_eq!(names.text(id), Maybe::Present(NameRef::from(text)));
        }
    }

    #[test]
    fn an_id_past_the_table_reads_no_text()
    {
        let mut larger = Names::new();
        let _a = minted(&mut larger, "a");
        let b = minted(&mut larger, "b");
        let mut smaller = Names::new();
        let _a = minted(&mut smaller, "a");
        assert_eq!(smaller.text(b), Maybe::Absent(name_text::Absent::Unminted));
    }

    #[test]
    fn ids_minted_out_of_text_order_compare_by_text()
    {
        let mut names = Names::new();
        let mul = minted(&mut names, "mul");
        let carrier = minted(&mut names, "Carrier");
        let a = minted(&mut names, "a");
        assert_eq!(names.compare(mul, carrier), Ordering::Greater);
        assert_eq!(names.compare(carrier, a), Ordering::Less);
        assert_eq!(names.compare(a, mul), Ordering::Less);
        assert_eq!(names.compare(a, a), Ordering::Equal);
        let mut sorted = [mul, carrier, a];
        sorted.sort_by(|&left, &right| names.compare(left, right));
        assert_eq!(sorted, [carrier, a, mul]);
    }

    #[test]
    fn a_text_and_its_id_spell_alike()
    {
        let mut names = Names::new();
        let text = Name::from("Carrier");
        let id = minted(&mut names, "Carrier");
        assert_eq!(text.spelled(&names), id.spelled(&names));
        assert_eq!(id.spelled(&names), Maybe::Present(NameRef::from("Carrier")));
    }

    #[test]
    fn a_numbered_name_is_the_name_of_its_text()
    {
        let mut names = Names::new();
        let whole = minted(&mut names, "x3");
        assert_eq!(names.mint_numbered('x', 3), Maybe::Present(whole));
        let placeholder = names.mint_numbered('_', 10);
        let Maybe::Present(placeholder) = placeholder
        else {
            panic!("a table with room mints _10: {placeholder:?}");
        };
        assert_eq!(
            names.text(placeholder),
            Maybe::Present(NameRef::from("_10"))
        );
        let widest = names.mint_numbered('𝔵', usize::MAX);
        let Maybe::Present(widest) = widest
        else {
            panic!("a table with room mints the widest numbered name: {widest:?}");
        };
        let expected = alloc::format!("𝔵{}", usize::MAX);
        assert_eq!(
            names.text(widest),
            Maybe::Present(NameRef::from(expected.as_str()))
        );
    }
}
