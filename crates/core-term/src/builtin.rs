//! The one table of builtins: each thing that the toolchain knows, by a key.
//!
//! A reader wants each built-in name to have one declaration and one row that
//! states what the toolchain gives it. A declaration of `std` takes its row by
//! the attribute `@[builtin("key")]`, whose text is the row's key. The key is
//! the name that the tree knows the row by.
//!
//! | Kind | Rows | Direction |
//! | ---- | ---- | --------- |
//! | a native value | each row of [`PRELUDE`], keyed by its name | given: the toolchain gives the value, and the declaration is a signature with no body that states the row's type |
//! | an atom | each nullary value type of [`TypeAtom::ALL`], keyed by its word | given: the toolchain gives the type, and the declaration is a type signature with no body that states its kind |
//! | a former | each unary type former of [`TypeFormer::ROWS`], keyed by its word | given: the toolchain gives the former, and the declaration is a type signature with one parameter and no body |
//! | a role | each role of [`Builtin`], keyed by its word | found: the library gives the declaration with its body, and a former of the core reads it by its role |
//!
//! A lookup reads the table in its order, so the work of one key is bounded by
//! the table's fixed size.
//!
//! # References
//!
//! - `vault:01a1f320-0881-7ed1-9a54-c0c713ccf7cf` — anchor: one table of the
//!   toolchain with a key, a kind and a direction for each row, and one
//!   attribute that binds a declaration of `std` to a row.

use gandr_kernel_term::Builtin;
use quenchant_shape::shape::Maybe;

use crate::primitive::PRELUDE;
use crate::primitive::Primitive;

/// The text that names a row of the table, as an attribute's payload spells
/// it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Key<'key>(pub &'key str);

impl AsRef<str> for Key<'_>
{
    /// The key's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl core::fmt::Display for Key<'_>
{
    /// The key's text, as a source spells it inside its quotes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

/// A nullary value type that the toolchain gives: an atom of the fragment.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeAtom
{
    /// `Bool`, the canonical sum of two unit types.
    Boolean,
    /// `Unit`, the type inhabited by the unit value alone.
    Unit,
    /// `Integer`, the integer base atom.
    Integer,
    /// `String`, the text base atom.
    Text,
    /// `Char`, the character base atom.
    Character,
    /// `f64`, the IEEE 754 binary64 base atom.
    Float64,
    /// `u32`, `u64`, `i32` or `i64`, an integer width atom.
    Fixed(gandr_kernel_term::IntegerWidth),
    /// `Void`, the sum of no summands, eliminated by a case of no arms.
    Void,
    /// `Buf`, the opaque buffer a receive places live and a send returns.
    Buffer,
    /// `Web`, the causal webs `decompose` returns.
    Web,
    /// `Qubit`, one quantum bit, which carries no comonoid.
    Qubit,
    /// `Row`, the kind of effect rows a row variable ranges over.
    Row,
}

impl TypeAtom
{
    /// Every atom with the word that keys its row, in the order of the
    /// table.
    ///
    /// # Specification
    /// trivial.
    pub const ALL: [(&'static str, Self); 21_usize] = [
        ("unit", Self::Unit),
        ("void", Self::Void),
        ("bool", Self::Boolean),
        ("integer", Self::Integer),
        ("string", Self::Text),
        ("char", Self::Character),
        ("f64", Self::Float64),
        ("u32", Self::Fixed(gandr_kernel_term::IntegerWidth::U32)),
        ("u64", Self::Fixed(gandr_kernel_term::IntegerWidth::U64)),
        ("i32", Self::Fixed(gandr_kernel_term::IntegerWidth::I32)),
        ("i64", Self::Fixed(gandr_kernel_term::IntegerWidth::I64)),
        ("u8", Self::Fixed(gandr_kernel_term::IntegerWidth::U8)),
        ("u16", Self::Fixed(gandr_kernel_term::IntegerWidth::U16)),
        ("i8", Self::Fixed(gandr_kernel_term::IntegerWidth::I8)),
        ("i16", Self::Fixed(gandr_kernel_term::IntegerWidth::I16)),
        ("usize", Self::Fixed(gandr_kernel_term::IntegerWidth::Usize)),
        ("isize", Self::Fixed(gandr_kernel_term::IntegerWidth::Isize)),
        ("row", Self::Row),
        ("buf", Self::Buffer),
        ("web", Self::Web),
        ("qubit", Self::Qubit),
    ];

    /// The key of the atom's row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(self) -> Key<'static>
    {
        Key(Self::ALL
            .iter()
            .find_map(|&(word, atom)| (atom == self).then_some(word))
            .unwrap_or(""))
    }
}

/// A unary type head: a type former of the fragment.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeFormer
{
    /// `+U C`, the thunk of a computation type, which is a value type.
    Thunk,
    /// `-F A`, the returner over a value type, which is a computation type.
    Returner,
    /// `List(A)`, the native finite lists over a value type.
    List,
    /// `Run(S)`, the value type of the complete recorded runs of the session
    /// code `S`, which is read as a value.
    Run,
    /// `Prefix(S)`, the value type of the recorded prefixes of the session
    /// code `S`, closed or still open, which is read as a value.
    Prefix,
    /// `Dialogue(S)`, the value type of the complete dialogues over the
    /// session code `S`, its left endpoint following `S` and its right the
    /// dual, which is read as a value.
    Dialogue,
}

impl TypeFormer
{
    /// Every former that a declaration of `std` binds, with the word that keys
    /// its row, in the order of the table. `+U` and `-F` are operators of the
    /// grammar, so no row holds them.
    ///
    /// # Specification
    /// trivial.
    pub const ROWS: [(&'static str, Self); 4_usize] = [
        ("list", Self::List),
        ("run", Self::Run),
        ("prefix", Self::Prefix),
        ("dialogue", Self::Dialogue),
    ];

    /// The key of the former's row, empty for an operator of the grammar.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(self) -> Key<'static>
    {
        Key(Self::ROWS
            .iter()
            .find_map(|&(word, former)| (former == self).then_some(word))
            .unwrap_or(""))
    }
}

/// What a row of the table is.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Kind
{
    /// A value of the native table.
    Native,
    /// A nullary value type that the toolchain gives.
    Atom,
    /// A unary type former that the toolchain gives.
    Former,
    /// A role that a former of the core reads.
    Role,
}

/// Who gives the meaning of a row.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Direction
{
    /// The toolchain gives the meaning. The declaration is a signature with no
    /// body, and the checker compares the declared type with the row's type.
    Given,
    /// The library gives the meaning. The declaration has its body, and the
    /// checker compares it with the canonical form of the row.
    Found,
}

/// One row of the table: what the toolchain knows by one key.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Row
{
    /// A value of the native table, which gives the value and its type.
    Native(Primitive),
    /// A nullary value type, which the toolchain gives with no body.
    Atom(TypeAtom),
    /// A unary type former, which the toolchain gives with no body.
    Former(TypeFormer),
    /// A role that a former of the core reads, which states the canonical form
    /// of its holder.
    Role(Builtin),
}

impl Row
{
    /// The text that names the row: a native value's name, an atom's or a
    /// former's word, or a role's word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(self) -> Key<'static>
    {
        Key(match self {
            Self::Native(primitive) => primitive.name().into(),
            Self::Atom(atom) => atom.key().0,
            Self::Former(former) => former.key().0,
            Self::Role(role) => role.word().0,
        })
    }

    /// What the row is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(self) -> Kind
    {
        match self {
            Self::Native(_) => Kind::Native,
            Self::Atom(_) => Kind::Atom,
            Self::Former(_) => Kind::Former,
            Self::Role(_) => Kind::Role,
        }
    }

    /// Who gives the meaning of the row: the toolchain for a native value, an
    /// atom and a former, the library for a role.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn direction(self) -> Direction
    {
        match self {
            Self::Native(_) | Self::Atom(_) | Self::Former(_) => Direction::Given,
            Self::Role(_) => Direction::Found,
        }
    }

    /// Every row of the table: the native values in the order of
    /// [`PRELUDE`], then the atoms in the order of [`TypeAtom::ALL`], then the
    /// formers in the order of [`TypeFormer::ROWS`], then the roles in the
    /// order of [`Builtin::ALL`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn all() -> impl Iterator<Item = Self>
    {
        PRELUDE
            .iter()
            .copied()
            .map(Self::Native)
            .chain(TypeAtom::ALL.into_iter().map(|(_, atom)| Self::Atom(atom)))
            .chain(
                TypeFormer::ROWS
                    .into_iter()
                    .map(|(_, former)| Self::Former(former)),
            )
            .chain(Builtin::ALL.into_iter().map(Self::Role))
    }

    /// The row that `key` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the row whose [`Self::key`] is `key`, and
    ///   [`row::Absent::Unkeyed`] when no row of the table has that key.
    /// - panics: none.
    /// - executable: none — the predicate would read the whole table again, and
    ///   the witnesses read each row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each row is named back by its key, the keys are
    ///   distinct, and a key that differs from a row's key by one character
    ///   names no row.
    /// - witness: `builtin::tests::each_row_is_named_back_by_its_key`
    /// - witness: `builtin::tests::a_key_that_no_row_holds_names_none`
    #[inline]
    pub fn named(key: Key<'_>) -> Maybe<Self, row::Absent>
    {
        for row in Self::all() {
            if row.key() == key {
                return Maybe::Present(row);
            }
        }
        Maybe::Absent(row::Absent::Unkeyed)
    }
}

quenchant_shape::reason_enum! {
    /// Why a key names no row.
    pub mod row {
        /// The reason a key names no row.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No row of the table has the key.
            Unkeyed,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;

    use gandr_kernel_term::Builtin;
    use quenchant_shape::shape::Maybe;

    use super::Direction;
    use super::Key;
    use super::Kind;
    use super::Row;
    use super::TypeAtom;
    use super::TypeFormer;
    use super::row;
    use crate::primitive::PRELUDE;

    #[test]
    fn each_row_is_named_back_by_its_key()
    {
        let mut keys = BTreeSet::new();
        for row in Row::all() {
            assert!(
                keys.insert(row.key()),
                "the key {} names two rows",
                row.key()
            );
            assert_eq!(Row::named(row.key()), Maybe::Present(row));
        }
        assert_eq!(
            keys.len(),
            PRELUDE.len() + TypeAtom::ALL.len() + TypeFormer::ROWS.len() + Builtin::ALL.len()
        );
        let append = Row::named(Key("string.append"));
        assert!(
            matches!(append, Maybe::Present(Row::Native(primitive)) if primitive.name().as_ref() == "string.append")
        );
        assert_eq!(
            Row::named(Key("irPair")),
            Maybe::Present(Row::Role(Builtin::IrPair))
        );
        assert_eq!(
            Row::named(Key("integer")),
            Maybe::Present(Row::Atom(TypeAtom::Integer))
        );
        assert_eq!(
            Row::named(Key("list")),
            Maybe::Present(Row::Former(TypeFormer::List))
        );
    }

    #[test]
    fn a_native_row_is_given_and_a_role_is_found()
    {
        for row in Row::all() {
            match row {
                Row::Native(_) => {
                    assert_eq!(
                        (row.kind(), row.direction()),
                        (Kind::Native, Direction::Given)
                    );
                },
                Row::Atom(_) => {
                    assert_eq!(
                        (row.kind(), row.direction()),
                        (Kind::Atom, Direction::Given)
                    );
                },
                Row::Former(_) => {
                    assert_eq!(
                        (row.kind(), row.direction()),
                        (Kind::Former, Direction::Given)
                    );
                },
                Row::Role(_) => {
                    assert_eq!(
                        (row.kind(), row.direction()),
                        (Kind::Role, Direction::Found)
                    );
                },
            }
        }
    }

    #[test]
    fn a_key_that_no_row_holds_names_none()
    {
        for key in [
            "string.join",
            "String.append",
            "irpair",
            "",
            "irElim",
            "Integer",
            "int",
            "List",
            "session",
        ] {
            assert_eq!(
                Row::named(Key(key)),
                Maybe::Absent(row::Absent::Unkeyed),
                "{key}"
            );
        }
    }

    /// The rows of `ledger/builtins.sql` whose place is this table are the
    /// rows of [`Row::all`], each with its key, its kind and its direction.
    /// A macro makes the rows of the widths, so no reader of the text finds
    /// them, and this test reads the table itself.
    #[test]
    fn the_listing_holds_each_row_of_the_table_and_no_other()
    {
        const PLACE: &str = "crates/core-term/src/builtin.rs";
        let listed: BTreeSet<(&str, &str, &str)> = include_str!("../../../ledger/builtins.sql")
            .lines()
            .filter_map(|line| {
                let values = line
                    .strip_prefix("INSERT INTO builtin VALUES('")?
                    .strip_suffix("');")?;
                let mut fields = values.split("','");
                let (name, place, kind, direction) = (
                    fields.next()?,
                    fields.next()?,
                    fields.next()?,
                    fields.next()?,
                );
                (place == PLACE).then_some((name, kind, direction))
            })
            .collect();
        let tabled: BTreeSet<(&str, &str, &str)> = Row::all()
            .map(|row| {
                let kind = match row.kind() {
                    Kind::Native => "value",
                    Kind::Atom => "atom",
                    Kind::Former => "former",
                    Kind::Role => "role",
                };
                let direction = match row.direction() {
                    Direction::Given => "given",
                    Direction::Found => "found",
                };
                (row.key().0, kind, direction)
            })
            .collect();
        assert_eq!(
            (
                tabled.difference(&listed).collect::<alloc::vec::Vec<_>>(),
                listed.difference(&tabled).collect::<alloc::vec::Vec<_>>()
            ),
            (alloc::vec::Vec::new(), alloc::vec::Vec::new()),
            "the rows of the table that the listing lacks, then the rows of the listing that the table lacks; add or delete each in ledger/builtins.sql, then run `mise run ledger:builtins`"
        );
    }
}
