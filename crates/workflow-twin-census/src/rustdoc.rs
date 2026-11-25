//! What the census reads in the JSON that rustdoc writes for one library.
//!
//! The reader gives three counts: the generic public items, the public
//! functions, and the public functions that an export can carry.
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
//!
//! A public function is a public function or method of the crate by the same
//! rule. An export can carry it when it is not generic, each operand is a
//! fixed-width integer or an address, and it has a result that is one of the
//! two. The fixed-width integers are the widths of gandr: `u8` to `u64`, `i8`
//! to `i64`, `usize` and `isize`. An address is a reference or a raw pointer
//! to a sized type: `self` by reference too, and not a slice, a `str` or a
//! trait object, whose pointer has a length or a table beside the address.

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

/// The fixed-width integers of gandr, by the names of Rust's primitives.
const FIXED_WIDTH: [&str; 10] = [
    "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "usize", "isize",
];

/// What the census reads of the library of one crate.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Surface
{
    /// The count of generic public items.
    pub generic_items: usize,
    /// The count of public functions and methods.
    pub functions: usize,
    /// The count of public functions and methods that an export can carry.
    pub exportable: usize,
    /// Each public function and method, in the order of its name, with what
    /// an export needs to carry it.
    pub entries: Vec<Entry>,
}

/// One public function or method of a library.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// The name: `Type::method` for a method, the name alone for a function.
    pub name: String,
    /// What an export needs to carry it.
    pub carry: Carry,
}

/// What an export needs to carry a function.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Carry
{
    /// The function is in the export fragment.
    Fragment,
    /// A wrapper passes each operand as its words and gives the result as its
    /// words. A result of more than one word goes to an address that the
    /// caller gives.
    Wrapper
    {
        /// The count of words of the operands.
        operands: usize,
        /// The count of words of the result: zero for `()`.
        result: usize,
    },
    /// No wrapper carries the function, for the reason that the text gives.
    Refused(String),
}

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
    /// The path of each item that the index names, external items too.
    paths: BTreeMap<u32, Summary>,
    /// The format of the file, its last key.
    format_version: u32,
}

/// The path of an item.
#[derive(Deserialize)]
struct Summary
{
    /// The names of the path, the crate first.
    path: Vec<String>,
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
    /// The name of the item, absent for an implementation.
    name: Option<String>,
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

/// A type of a signature or of a field, as the census reads it.
#[derive(Clone, Debug)]
enum Ty
{
    /// A fixed-width integer.
    Integer,
    /// A reference or a raw pointer to a sized type.
    Address,
    /// A slice, `str` or a trait object: a type with no size.
    Unsized,
    /// `bool` or `char`: one word in a wrapper.
    Scalar,
    /// A tuple; `()` is the tuple with no member.
    Tuple(Vec<Self>),
    /// A named type: its identifier, its last name and its type arguments.
    Path
    {
        /// The identifier, a key of `paths`.
        id: u32,
        /// The last name of its path.
        name: String,
        /// Its type arguments.
        args: Vec<Self>,
    },
    /// Each other type, by a text that names it.
    Other(String),
}

impl Ty
{
    /// Whether an export carries a value of the type.
    ///
    /// # Specification
    /// trivial.
    const fn carried(&self) -> bool
    {
        matches!(*self, Self::Integer | Self::Address)
    }
}

/// The content of a reference or of a raw pointer.
#[derive(Deserialize)]
struct Pointer
{
    /// The type that the pointer reaches.
    #[serde(rename = "type")]
    pointee: Ty,
}

/// One argument of a path.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum GenericArg
{
    /// A type.
    Type(Ty),
    /// A lifetime.
    Lifetime(IgnoredAny),
    /// A constant.
    Const(IgnoredAny),
    /// `_`.
    Infer,
}

/// The arguments of a path.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum Args
{
    /// `<…>`.
    AngleBracketed
    {
        /// The arguments.
        args: Vec<GenericArg>,
    },
    /// `Fn(…) -> …`.
    Parenthesized(IgnoredAny),
    /// `(..)` of a return type notation.
    ReturnTypeNotation,
}

/// The content of a named type.
#[derive(Deserialize)]
struct Resolved
{
    /// The path as the source writes it.
    path: String,
    /// The identifier.
    id: u32,
    /// The arguments.
    args: Option<Args>,
}

/// Reads the object of a type, which has one key: the kind. A kind with no
/// content, such as `infer`, is a string.
struct TyVisitor;

impl<'de> serde::de::Visitor<'de> for TyVisitor
{
    type Value = Ty;

    /// What the visitor reads.
    ///
    /// # Specification
    /// trivial.
    fn expecting(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        formatter.write_str("a type")
    }

    /// A kind with no content.
    ///
    /// # Specification
    /// trivial.
    fn visit_str<E>(
        self,
        _kind: &str,
    ) -> Result<Ty, E>
    where
        E: serde::de::Error,
    {
        Ok(Ty::Other(String::from("an inferred type")))
    }

    /// A kind with its content.
    ///
    /// # Specification
    /// trivial.
    fn visit_map<A>(
        self,
        mut map: A,
    ) -> Result<Ty, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut ty = Ty::Other(String::from("a type"));
        while let Some(kind) = map.next_key::<String>()? {
            ty = match kind.as_str() {
                "primitive" => {
                    let name = map.next_value::<String>()?;
                    if FIXED_WIDTH.contains(&name.as_str()) {
                        Ty::Integer
                    }
                    else if name == "str" {
                        Ty::Unsized
                    }
                    else if name == "bool" || name == "char" {
                        Ty::Scalar
                    }
                    else {
                        Ty::Other(alloc::format!("`{name}`"))
                    }
                },
                "borrowed_ref" | "raw_pointer" => match map.next_value::<Pointer>()?.pointee {
                    Ty::Unsized => Ty::Other(String::from(
                        "a pointer to a slice, a `str` or a trait object",
                    )),
                    Ty::Integer
                    | Ty::Address
                    | Ty::Scalar
                    | Ty::Tuple(_)
                    | Ty::Path { .. }
                    | Ty::Other(_) => Ty::Address,
                },
                "slice" | "dyn_trait" => {
                    map.next_value::<IgnoredAny>()?;
                    Ty::Unsized
                },
                "tuple" => Ty::Tuple(map.next_value()?),
                "resolved_path" => {
                    let resolved = map.next_value::<Resolved>()?;
                    let args = match resolved.args {
                        Some(Args::AngleBracketed { args }) => args
                            .into_iter()
                            .filter_map(|arg| match arg {
                                GenericArg::Type(ty) => Some(ty),
                                GenericArg::Lifetime(_)
                                | GenericArg::Const(_)
                                | GenericArg::Infer => None,
                            })
                            .collect(),
                        Some(Args::Parenthesized(_) | Args::ReturnTypeNotation) | None => {
                            Vec::new()
                        },
                    };
                    let name = resolved
                        .path
                        .rsplit("::")
                        .next()
                        .unwrap_or(&resolved.path)
                        .to_owned();
                    Ty::Path {
                        id: resolved.id,
                        name,
                        args,
                    }
                },
                "generic" => Ty::Other(alloc::format!("`{}`", map.next_value::<String>()?)),
                _ => {
                    map.next_value::<IgnoredAny>()?;
                    Ty::Other(alloc::format!("a type of the kind `{kind}`"))
                },
            };
        }
        Ok(ty)
    }
}

impl<'de> Deserialize<'de> for Ty
{
    /// Reads a type with [`TyVisitor`].
    ///
    /// # Specification
    /// trivial.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(TyVisitor)
    }
}

/// The signature of a function.
#[derive(Deserialize)]
struct Signature
{
    /// Each operand: its name and its type.
    inputs: Vec<(IgnoredAny, Ty)>,
    /// The result, absent for `()`.
    output: Option<Ty>,
}

impl Signature
{
    /// Whether an export carries each operand and the result.
    ///
    /// # Specification
    /// trivial.
    fn carried(&self) -> bool
    {
        self.inputs.iter().all(|&(_, ref ty)| ty.carried())
            && self.output.as_ref().is_some_and(Ty::carried)
    }
}

/// The content of a function.
#[derive(Deserialize)]
struct Function
{
    /// The signature.
    sig: Signature,
    /// The generics.
    generics: Generics,
}

/// The content of an item of a kind that carries generics.
#[derive(Deserialize)]
struct Plain
{
    /// The generics.
    generics: Generics,
}

/// The fields of a structure.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum StructKind
{
    /// `struct A;`.
    Unit,
    /// `struct A(…);`: a field that the JSON strips is `null`.
    Tuple(Vec<Option<u32>>),
    /// `struct A { … }`.
    Plain
    {
        /// The fields that the JSON has.
        fields: Vec<u32>,
        /// Whether the JSON strips a field.
        has_stripped_fields: bool,
    },
}

impl StructKind
{
    /// Each field, or none when the JSON strips one.
    ///
    /// # Specification
    /// trivial.
    fn fields(&self) -> Option<Vec<u32>>
    {
        match *self {
            Self::Unit => Some(Vec::new()),
            Self::Tuple(ref fields) => fields.iter().copied().collect(),
            Self::Plain {
                ref fields,
                has_stripped_fields,
            } => (!has_stripped_fields).then(|| fields.clone()),
        }
    }
}

/// The content of a structure.
#[derive(Deserialize)]
struct Struct
{
    /// The fields.
    kind: StructKind,
    /// The generics.
    generics: Generics,
}

/// The content of an enumeration.
#[derive(Deserialize)]
struct Enum
{
    /// The generics.
    generics: Generics,
    /// Each variant.
    variants: Vec<u32>,
    /// Whether the JSON strips a variant.
    has_stripped_variants: bool,
}

/// The fields of a variant.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum VariantKind
{
    /// A variant with no field.
    Plain,
    /// `A(…)`: a field that the JSON strips is `null`.
    Tuple(Vec<Option<u32>>),
    /// `A { … }`.
    Struct
    {
        /// The fields that the JSON has.
        fields: Vec<u32>,
        /// Whether the JSON strips a field.
        has_stripped_fields: bool,
    },
}

impl VariantKind
{
    /// Each field, or none when the JSON strips one.
    ///
    /// # Specification
    /// trivial.
    fn fields(&self) -> Option<Vec<u32>>
    {
        match *self {
            Self::Plain => Some(Vec::new()),
            Self::Tuple(ref fields) => fields.iter().copied().collect(),
            Self::Struct {
                ref fields,
                has_stripped_fields,
            } => (!has_stripped_fields).then(|| fields.clone()),
        }
    }
}

/// The content of a variant.
#[derive(Deserialize)]
struct Variant
{
    /// The fields.
    kind: VariantKind,
}

/// The content of a type alias.
#[derive(Deserialize)]
struct Alias
{
    /// The type that the alias names.
    #[serde(rename = "type")]
    aliased: Ty,
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
    /// The type that the implementation is for.
    #[serde(rename = "for")]
    for_type: Ty,
    /// The identifier of each item.
    items: Vec<u32>,
}

/// The kind of an item, as the reader reads it.
enum Inner
{
    /// A function or a method.
    Function(Function),
    /// A structure.
    Struct(Struct),
    /// An enumeration.
    Enum(Enum),
    /// A variant of an enumeration.
    Variant(Variant),
    /// A field of a structure or of a variant.
    Field(Ty),
    /// A type alias.
    Alias(Alias),
    /// A union.
    Union(Generics),
    /// A trait.
    Trait(Trait),
    /// An implementation.
    Impl(Impl),
    /// Each other kind.
    Other,
}

impl Inner
{
    /// The generics of an item of a kind that has a public signature.
    ///
    /// # Specification
    /// trivial.
    const fn generics(&self) -> Option<&Generics>
    {
        match *self {
            Self::Function(Function { ref generics, .. })
            | Self::Struct(Struct { ref generics, .. })
            | Self::Enum(Enum { ref generics, .. })
            | Self::Alias(Alias { ref generics, .. })
            | Self::Union(ref generics) => Some(generics),
            Self::Variant(_) | Self::Field(_) | Self::Trait(_) | Self::Impl(_) | Self::Other => {
                None
            },
        }
    }
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
                "function" => Inner::Function(map.next_value()?),
                "struct" => Inner::Struct(map.next_value()?),
                "enum" => Inner::Enum(map.next_value()?),
                "variant" => Inner::Variant(map.next_value()?),
                "struct_field" => Inner::Field(map.next_value()?),
                "type_alias" => Inner::Alias(map.next_value()?),
                "union" => Inner::Union(map.next_value::<Plain>()?.generics),
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

/// The deepest nesting of types that [`Crate::words`] follows.
const DEPTH: u8 = 8;

impl Crate
{
    /// The count of words that a wrapper passes for a value of `ty`, or the
    /// type that no wrapper passes as words.
    ///
    /// # Specification
    /// trivial.
    fn words(
        &self,
        ty: &Ty,
        depth: u8,
    ) -> Result<usize, String>
    {
        let Some(deeper) = depth.checked_sub(1)
        else {
            return Err(String::from("a type nested too deep"));
        };
        match *ty {
            Ty::Integer | Ty::Address | Ty::Scalar => Ok(1),
            Ty::Unsized => Err(String::from("a slice, a `str` or a trait object")),
            Ty::Other(ref name) => Err(name.clone()),
            Ty::Tuple(ref members) => members.iter().try_fold(0_usize, |sum, member| {
                Ok(sum.saturating_add(self.words(member, deeper)?))
            }),
            Ty::Path {
                id,
                ref name,
                ref args,
            } => {
                let refused = || alloc::format!("`{name}`");
                let generic = |generics: &Generics| generics.generic() || !args.is_empty();
                match self
                    .index
                    .get(&id)
                    .filter(|item| item.crate_id == 0)
                    .map(|item| &item.inner)
                {
                    Some(&Inner::Struct(ref definition)) if !generic(&definition.generics) => self
                        .fields(definition.kind.fields(), deeper)
                        .ok_or_else(refused),
                    Some(&Inner::Enum(ref definition))
                        if !generic(&definition.generics) && !definition.has_stripped_variants =>
                    {
                        let mut widest = 0_usize;
                        for variant in &definition.variants {
                            let Some(&Inner::Variant(ref variant)) =
                                self.index.get(variant).map(|item| &item.inner)
                            else {
                                return Err(refused());
                            };
                            let words = self
                                .fields(variant.kind.fields(), deeper)
                                .ok_or_else(refused)?;
                            widest = widest.max(words);
                        }
                        Ok(widest.saturating_add(1))
                    },
                    Some(&Inner::Alias(ref definition)) if !generic(&definition.generics) => {
                        self.words(&definition.aliased, deeper)
                    },
                    Some(_) => Err(refused()),
                    None => self.foreign_words(id, args, deeper).ok_or_else(refused),
                }
            },
        }
    }

    /// The sum of the words of `fields`, or none when the JSON strips a field
    /// or a field has no words.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &self,
        fields: Option<Vec<u32>>,
        depth: u8,
    ) -> Option<usize>
    {
        fields?.iter().try_fold(0_usize, |sum, field| {
            let Some(&Inner::Field(ref ty)) = self.index.get(field).map(|item| &item.inner)
            else {
                return None;
            };
            Some(sum.saturating_add(self.words(ty, depth).ok()?))
        })
    }

    /// The words of a type of a different crate: `Ordering` is one word;
    /// `Option` and `Result` are a tag word and the words of the widest
    /// argument.
    ///
    /// # Specification
    /// trivial.
    fn foreign_words(
        &self,
        id: u32,
        args: &[Ty],
        depth: u8,
    ) -> Option<usize>
    {
        let path = &self.paths.get(&id)?.path;
        let (first, rest) = path.split_first()?;
        if !matches!(first.as_str(), "core" | "alloc" | "std") {
            return None;
        }
        let tail: Vec<&str> = rest.iter().map(String::as_str).collect();
        match *tail.as_slice() {
            ["cmp", "Ordering"] => Some(1),
            ["option", "Option"] | ["result", "Result"] => args
                .iter()
                .try_fold(0_usize, |widest, arg| {
                    Some(widest.max(self.words(arg, depth).ok()?))
                })
                .map(|widest| widest.saturating_add(1)),
            _ => None,
        }
    }

    /// What an export needs to carry `function`, which is generic when
    /// `generic` holds.
    ///
    /// # Specification
    /// trivial.
    fn carry(
        &self,
        function: &Function,
        generic: bool,
    ) -> Carry
    {
        if generic {
            return Carry::Refused(String::from("it is generic"));
        }
        if function.sig.carried() {
            return Carry::Fragment;
        }
        let words = || -> Result<Carry, String> {
            let operands = function
                .sig
                .inputs
                .iter()
                .try_fold(0_usize, |sum, &(_, ref ty)| {
                    Ok::<usize, String>(sum.saturating_add(self.words(ty, DEPTH)?))
                })?;
            let result = function
                .sig
                .output
                .as_ref()
                .map_or(Ok(0), |ty| self.words(ty, DEPTH))?;
            Ok(Carry::Wrapper { operands, result })
        };
        words().unwrap_or_else(|ty| Carry::Refused(alloc::format!("{ty} has no words")))
    }
}

/// What the census reads in `rustdoc`, the JSON that rustdoc writes for the
/// library of one crate.
///
/// # Specification
/// - requires: nothing; a text that is not the JSON of format [`FORMAT`] is
///   refused.
/// - ensures: the counts of the public items of the crate that the module
///   names: the generic items, the functions, and the functions that an export
///   can carry; and each public function with its [`Carry`].
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
///   not read, the methods of generic implementations and the entries, growth
///   within the file
///
/// # Adequacy
/// - hypothesis: L3 — a crate with one item of each case: a type parameter, an
///   `impl Trait` parameter, a `where` bound, a supertrait, a method of a
///   generic implementation, a lifetime parameter, a const parameter, a method
///   of a trait implementation, a private item, an item of a different crate
///   and a kind with no content; functions over integers, over references to a
///   sized type, to a slice and to `str`, with no result and with a result of a
///   type of the crate; functions over structures, enumerations, aliases,
///   `Option`, `Result` and `Ordering`, and over a structure with a stripped
///   field; a text of a different format and a text that is not JSON are each
///   refused by name.
/// - witness: `tests::census::a_generic_public_item_counts_and_each_other_item_does_not`
/// - witness: `tests::census::an_export_carries_integers_and_addresses_of_sized_types`
/// - witness: `tests::census::a_wrapper_passes_the_words_of_each_type_of_the_crate`
/// - witness: `tests::census::rustdoc_of_another_format_or_no_json_is_refused_by_name`
#[inline]
pub fn read(rustdoc: &[u8]) -> Result<Surface, CensusError>
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
    let mut in_generic_impl: BTreeSet<u32> = BTreeSet::new();
    let mut owner: BTreeMap<u32, &str> = BTreeMap::new();
    for (_, item) in own() {
        let Inner::Impl(ref implementation) = item.inner
        else {
            continue;
        };
        if implementation.implemented.is_some() {
            continue;
        }
        if implementation.generics.generic() {
            in_generic_impl.extend(implementation.items.iter().copied());
        }
        if let Ty::Path { ref name, .. } = implementation.for_type {
            for &method in &implementation.items {
                let _first = owner.insert(method, name.as_str());
            }
        }
    }
    let mut surface = Surface::default();
    for (id, item) in own() {
        if !matches!(item.visibility, Visibility::Public) {
            continue;
        }
        let in_impl = in_generic_impl.contains(id);
        let generic = match item.inner {
            Inner::Trait(ref definition) => {
                definition.generics.generic() || trait_bound(&definition.bounds)
            },
            Inner::Function(_)
            | Inner::Struct(_)
            | Inner::Enum(_)
            | Inner::Variant(_)
            | Inner::Field(_)
            | Inner::Alias(_)
            | Inner::Union(_)
            | Inner::Impl(_)
            | Inner::Other => item
                .inner
                .generics()
                .is_some_and(|generics| generics.generic() || in_impl),
        };
        if let Inner::Function(ref function) = item.inner {
            surface.functions = surface.functions.saturating_add(1);
            let carry = parsed.carry(function, generic);
            if carry == Carry::Fragment {
                surface.exportable = surface.exportable.saturating_add(1);
            }
            let name = item.name.as_deref().unwrap_or("_");
            surface.entries.push(Entry {
                name: owner.get(id).map_or_else(
                    || String::from(name),
                    |owner| alloc::format!("{owner}::{name}"),
                ),
                carry,
            });
        }
        if generic {
            surface.generic_items = surface.generic_items.saturating_add(1);
        }
    }
    surface
        .entries
        .sort_by(|left, right| left.name.cmp(&right.name));
    Ok(surface)
}
