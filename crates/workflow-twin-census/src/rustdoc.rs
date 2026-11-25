//! The count of generic public items of one crate, read from the JSON that
//! rustdoc writes for its library.
//!
//! An item is generic when it has a type parameter or a trait bound. An entry
//! under the C convention carries neither, so a generic item has no twin
//! without a wrapper. The reader takes:
//!
//! - each public function, method, structure, enumeration, union, trait and
//!   type alias that the crate itself defines; a re-export counts in the crate
//!   that defines its item;
//! - as generic: a type parameter of the item, an `impl Trait` parameter too; a
//!   `where` clause with a trait bound; a supertrait of a trait; and each
//!   method of an inherent implementation that is generic by the same rule.
//!
//! A lifetime parameter and a const parameter are not generic by this rule.
//! The items of a trait implementation are not public items of the crate,
//! because the trait fixes their signatures.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use serde::Deserialize;
use serde::de::IgnoredAny;

use crate::CensusError;

/// The format of rustdoc's JSON that the reader reads.
pub const FORMAT: u32 = 61;

/// The format of a file, read alone when the whole file does not read.
#[derive(Deserialize)]
struct Version
{
    /// The format of the file.
    format_version: u32,
}

/// The parts of the file that the reader reads.
#[derive(Deserialize)]
struct Crate
{
    /// Each item, by its identifier.
    index: BTreeMap<u32, Item>,
    /// The format of the file, its last key.
    format_version: u32,
}

/// The visibility of an item.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum Visibility
{
    /// `pub`.
    Public,
    /// The visibility of an item of a trait or of a trait implementation.
    Default,
    /// `pub(crate)`.
    Crate,
    /// `pub(in path)`.
    Restricted(IgnoredAny),
}

/// One item of the index.
#[derive(Deserialize)]
struct Item
{
    /// `0` for an item of the crate itself.
    crate_id: u32,
    /// The visibility of the item.
    visibility: Visibility,
    /// The kind of the item, with its generics when it has them.
    inner: Inner,
}

/// The kind of a parameter.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum ParamKind
{
    /// A lifetime parameter.
    Lifetime(IgnoredAny),
    /// A type parameter, `impl Trait` too.
    Type(IgnoredAny),
    /// A const parameter.
    Const(IgnoredAny),
}

/// One parameter of the generics.
#[derive(Deserialize)]
struct Param
{
    /// Its kind.
    kind: ParamKind,
}

/// One bound.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum Bound
{
    /// A trait bound.
    #[serde(rename = "trait_bound")]
    Trait(IgnoredAny),
    /// A lifetime bound.
    Outlives(IgnoredAny),
    /// A `use<…>` bound.
    Use(IgnoredAny),
}

/// One predicate of a `where` clause.
#[derive(Deserialize)]
enum WhereClause
{
    /// `Type: Bound + …`.
    #[serde(rename = "bound_predicate")]
    Bounded
    {
        /// The bounds.
        bounds: Vec<Bound>,
    },
    /// `'a: 'b`.
    #[serde(rename = "lifetime_predicate")]
    Lifetime(IgnoredAny),
    /// `Type = Type`.
    #[serde(rename = "eq_predicate")]
    Equal(IgnoredAny),
}

/// The generics of an item.
#[derive(Deserialize)]
struct Generics
{
    /// The parameters.
    params: Vec<Param>,
    /// The `where` clause.
    where_predicates: Vec<WhereClause>,
}

impl Generics
{
    /// Whether a parameter is a type, or a predicate has a trait bound.
    ///
    /// # Specification
    /// trivial.
    fn generic(&self) -> bool
    {
        self.params
            .iter()
            .any(|param| matches!(param.kind, ParamKind::Type(_)))
            || self.where_predicates.iter().any(|predicate| {
                matches!(*predicate, WhereClause::Bounded { ref bounds } if trait_bound(bounds))
            })
    }
}

/// Whether one of `bounds` is a trait bound.
///
/// # Specification
/// trivial.
fn trait_bound(bounds: &[Bound]) -> bool
{
    bounds.iter().any(|bound| matches!(*bound, Bound::Trait(_)))
}

/// The content of an item of a kind that carries generics.
#[derive(Deserialize)]
struct Plain
{
    /// The generics.
    generics: Generics,
}

/// The content of a trait.
#[derive(Deserialize)]
struct Trait
{
    /// The generics.
    generics: Generics,
    /// The supertraits.
    bounds: Vec<Bound>,
}

/// The content of an implementation.
#[derive(Deserialize)]
struct Impl
{
    /// The generics.
    generics: Generics,
    /// The trait, absent for an inherent implementation.
    #[serde(rename = "trait")]
    implemented: Option<IgnoredAny>,
    /// The identifier of each item.
    items: Vec<u32>,
}

/// The kind of an item, as the reader reads it.
enum Inner
{
    /// A function, a structure, an enumeration, a union or a type alias.
    Plain(Generics),
    /// A trait.
    Trait(Trait),
    /// An implementation.
    Impl(Impl),
    /// Each other kind.
    Other,
}

/// Reads the object of `inner`, which has one key: the kind. A kind with no
/// content, such as `extern_type`, is a string.
struct InnerVisitor;

impl<'de> serde::de::Visitor<'de> for InnerVisitor
{
    type Value = Inner;

    /// What the visitor reads.
    ///
    /// # Specification
    /// trivial.
    fn expecting(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        formatter.write_str("the kind of an item")
    }

    /// A kind with no content.
    ///
    /// # Specification
    /// trivial.
    fn visit_str<E>(
        self,
        _kind: &str,
    ) -> Result<Inner, E>
    where
        E: serde::de::Error,
    {
        Ok(Inner::Other)
    }

    /// A kind with its content.
    ///
    /// # Specification
    /// trivial.
    fn visit_map<A>(
        self,
        mut map: A,
    ) -> Result<Inner, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut inner = Inner::Other;
        while let Some(kind) = map.next_key::<String>()? {
            inner = match kind.as_str() {
                "function" | "struct" | "enum" | "union" | "type_alias" => {
                    Inner::Plain(map.next_value::<Plain>()?.generics)
                },
                "trait" => Inner::Trait(map.next_value()?),
                "impl" => Inner::Impl(map.next_value()?),
                _ => {
                    map.next_value::<IgnoredAny>()?;
                    Inner::Other
                },
            };
        }
        Ok(inner)
    }
}

impl<'de> Deserialize<'de> for Inner
{
    /// Reads the kind of an item with [`InnerVisitor`].
    ///
    /// # Specification
    /// trivial.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(InnerVisitor)
    }
}

/// The count of generic public items in `rustdoc`, the JSON that rustdoc
/// writes for the library of one crate.
///
/// # Specification
/// - requires: nothing; a text that is not the JSON of format [`FORMAT`] is
///   refused.
/// - ensures: the count of public items of the crate, of the kinds that the
///   module lists, that are generic by its rule.
/// - fails: [`CensusError::RustdocFormat`] when the format is not [`FORMAT`];
///   [`CensusError::Rustdoc`] when the text is not the JSON of rustdoc.
/// - panics: none.
/// - executable: none — the rule is the fixture's to show.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the index of the file without the content that the rule does
///   not read, and the methods of generic implementations, growth within the
///   file
///
/// # Adequacy
/// - hypothesis: L3 — a crate with one item of each case: a type parameter, an
///   `impl Trait` parameter, a `where` bound, a supertrait, a method of a
///   generic implementation, a lifetime parameter, a const parameter, a method
///   of a trait implementation, a private item, an item of a different crate
///   and a kind with no content; a text of a different format and a text that
///   is not JSON are each refused by name.
/// - witness: `tests::census::a_generic_public_item_counts_and_each_other_item_does_not`
/// - witness: `tests::census::rustdoc_of_another_format_or_no_json_is_refused_by_name`
#[inline]
pub fn generic_items(rustdoc: &[u8]) -> Result<usize, CensusError>
{
    // rustdoc writes the format last, so a file of a different format can
    // fail in its index first. The format is read alone only then.
    let parsed: Crate = serde_json::from_slice(rustdoc).map_err(|error| {
        match serde_json::from_slice::<Version>(rustdoc) {
            Ok(version) if version.format_version != FORMAT => CensusError::RustdocFormat {
                found: version.format_version,
            },
            Ok(_) | Err(_) => CensusError::Rustdoc {
                reason: error.to_string(),
            },
        }
    })?;
    if parsed.format_version != FORMAT {
        return Err(CensusError::RustdocFormat {
            found: parsed.format_version,
        });
    }
    let own = || parsed.index.iter().filter(|&(_, item)| item.crate_id == 0);
    let in_generic_impl: BTreeSet<u32> = own()
        .filter_map(|(_, item)| match item.inner {
            Inner::Impl(ref implementation)
                if implementation.implemented.is_none() && implementation.generics.generic() =>
            {
                Some(implementation.items.iter().copied())
            },
            Inner::Plain(_) | Inner::Trait(_) | Inner::Impl(_) | Inner::Other => None,
        })
        .flatten()
        .collect();
    Ok(own()
        .filter(|&(id, item)| {
            matches!(item.visibility, Visibility::Public)
                && match item.inner {
                    Inner::Plain(ref generics) => {
                        generics.generic() || in_generic_impl.contains(id)
                    },
                    Inner::Trait(ref definition) => {
                        definition.generics.generic() || trait_bound(&definition.bounds)
                    },
                    Inner::Impl(_) | Inner::Other => false,
                }
        })
        .count())
}
