//! The generator of the store's refusal mirror.
//!
//! The checker states each refusal once, as a variant of `CheckRefusal`. The
//! store keeps each in item coordinates, projects it from the checker's, seats
//! it back into an arena, and writes and reads it in a checkpoint. This script
//! reads the checker's enum and `refusals.toml` and writes all five as
//! `macro_rules!` macros the crate expands where each belongs: the enum in
//! `typing.rs` under its own documentation, the projection in
//! `Projection::refusal`, the seat in `failure.rs`, and the arms in
//! `write_refusal` and `read_refusal`. A sixth macro gives the type contents
//! each refusal holds, which the codec bounds by their levels.
//!
//! A field's role follows its type, from the table's `[roles]`; a type no row
//! names is kept as the checker states it. A role's row states whether its
//! stored type holds type contents. The table's row for a refusal states its
//! wire tag and the fields of a two-role type read as sites. The store keeps
//! every field. The script refuses a refusal without a row, a row without a
//! refusal, a tag two refusals share, and a field a row names that the refusal
//! lacks.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Write as _;
use std::env;
use std::fs;
use std::path::PathBuf;

/// Why the generator refused its inputs.
#[derive(Debug)]
enum Refusal
{
    /// Cargo did not set a variable every build script receives.
    Environment(&'static str),
    /// Reading or writing a file failed.
    Io(std::io::Error),
    /// Writing the generated text failed.
    Format(core::fmt::Error),
    /// A source did not parse.
    Parse(String),
    /// The checker's enum and the table disagree.
    Table(String),
}

impl core::fmt::Display for Refusal
{
    /// The refusal, for the build log.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Environment(name) => write!(f, "cargo did not set {name}"),
            Self::Io(ref error) => write!(f, "file access failed: {error}"),
            Self::Format(error) => write!(f, "the generated text did not format: {error}"),
            Self::Parse(ref detail) | Self::Table(ref detail) => write!(f, "{detail}"),
        }
    }
}

impl From<core::fmt::Error> for Refusal
{
    /// The formatting failure, as the generator's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: core::fmt::Error) -> Self
    {
        Self::Format(error)
    }
}

impl From<std::io::Error> for Refusal
{
    /// The I/O error, as the generator's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: std::io::Error) -> Self
    {
        Self::Io(error)
    }
}

/// A documentation line, as the checker writes it.
#[repr(transparent)]
struct Doc(String);

/// The indentation a generated line opens with.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Indent(&'static str);

/// The indentation of a refusal in the generated enum, and of an arm.
const VARIANT: Indent = Indent("            ");

/// The indentation of a field in the generated enum.
const FIELD: Indent = Indent("                ");

/// A field of a checker refusal: its name, a tuple field's position, its type
/// as written and its documentation.
struct Field
{
    /// The name, or the position of a tuple field.
    name: String,
    /// The type's path as the checker writes it.
    ty: Vec<String>,
    /// The documentation lines.
    docs: Vec<Doc>,
}

/// The shape of a refusal's payload.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Shape
{
    /// No payload.
    Unit,
    /// Positional fields.
    Tuple,
    /// Named fields.
    Named,
}

/// A checker refusal: its name, documentation, shape and fields.
struct Variant
{
    /// The name.
    name: String,
    /// The documentation lines.
    docs: Vec<Doc>,
    /// The shape.
    shape: Shape,
    /// The fields, in declaration order.
    fields: Vec<Field>,
}

/// Whether a stored type holds type contents: the tables the codec writes
/// and bounds by their levels.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Holds
{
    /// It holds type contents.
    Contents,
    /// It holds none.
    Nothing,
}

/// A row of the table's `[roles]`: the type the store keeps, and the
/// projection method that reads it, beside the method that reads it as a
/// site.
struct Role
{
    /// The stored type.
    stored: String,
    /// The projection method.
    by: String,
    /// The projection method that reads a field `sites` names, if any.
    site: Option<String>,
    /// Whether the stored type holds type contents.
    holds: Holds,
}

/// A row of the table's `[refusals]`.
struct Row
{
    /// The wire tag; none for a refusal the codec writes by hand.
    tag: Option<u8>,
    /// The fields read as sites.
    sites: BTreeSet<String>,
    /// Whether the codec writes and reads the refusal by a hand-written arm.
    hand: bool,
}

/// A kept field, as the generated code spells it: its binding, its stored
/// type, its projection, its seat, and whether it holds type contents.
struct Kept<'variant>
{
    /// The checker's field.
    field: &'variant Field,
    /// The local the patterns bind it to.
    binding: String,
    /// The stored type.
    stored: String,
    /// The projection of the binding.
    projected: String,
    /// The seat of the stored binding, back to the checker's type.
    seated: String,
    /// Whether the stored type holds type contents.
    holds: Holds,
}

/// Write `$OUT_DIR/refusal.rs`, the store's refusal mirror.
///
/// # Specification
/// - ensures: the macros `refusal_enum`, `refusal_projection`, `refusal_seat`,
///   `refusal_kept`, `refusal_write`, `refusal_read` and `refusal_contents`,
///   one arm per checker refusal, each built from the refusal's fields and its
///   row; the script reruns when the checker's refusals, the checker's root or
///   the table change.
/// - executable: none — the output is code the crate compiles.
///
/// # Errors
/// As [`Refusal`]: an environment variable, a file, a parse, or a
/// disagreement between the enum and the table.
///
/// # Adequacy
/// - hypothesis: L2 — every refusal round-trips under the generated codec, and
///   every refusal projects to the stored refusal of its kind.
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
/// - witness: `codec::tests::every_refusal_holding_a_capped_level_is_refused_when_written_4451`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn main() -> Result<(), Refusal>
{
    let manifest = PathBuf::from(
        env::var_os("CARGO_MANIFEST_DIR").ok_or(Refusal::Environment("CARGO_MANIFEST_DIR"))?,
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").ok_or(Refusal::Environment("OUT_DIR"))?);
    let checker = manifest.join("../core-checker/src/refusal.rs");
    let failure = manifest.join("../core-checker/src/failure.rs");
    let root = manifest.join("../core-checker/src/lib.rs");
    let table = manifest.join("refusals.toml");
    for path in [&checker, &failure, &root, &table] {
        println!("cargo::rerun-if-changed={}", path.display());
    }
    let source = fs::read_to_string(&checker)?;
    let file =
        syn::parse_file(&source).map_err(|error| Refusal::Parse(format!("refusal.rs: {error}")))?;
    let frames = syn::parse_file(&fs::read_to_string(&failure)?)
        .map_err(|error| Refusal::Parse(format!("failure.rs: {error}")))?;
    let lib = syn::parse_file(&fs::read_to_string(&root)?)
        .map_err(|error| Refusal::Parse(format!("lib.rs: {error}")))?;
    let table: toml::Table = fs::read_to_string(&table)?
        .parse()
        .map_err(|error| Refusal::Parse(format!("refusals.toml: {error}")))?;
    let variants = variants(&file)?;
    let paths = paths(&file, &lib);
    let roles = roles(&table)?;
    let rows = rows(&table, &variants)?;
    let mut generated = String::from(
        "// The store's refusal mirror, generated by `build.rs` from the checker's\n// `CheckRefusal` and \
         `refusals.toml`.\n\n",
    );
    emit(&mut generated, &variants, &rows, &roles, &paths)?;
    emit_frame_roles(&mut generated, &frame_roles(&frames)?)?;
    fs::write(out.join("refusal.rs"), generated)?;
    Ok(())
}

/// The variants of `CheckRefusal`, in declaration order.
///
/// # Specification
/// - ensures: one [`Variant`] per variant of the checker's enum, each field's
///   type read as the segments of its path.
/// - executable: none — a reading of a parsed file.
///
/// # Errors
/// [`Refusal::Parse`] when the file holds no `CheckRefusal`, or a field's type
/// is not a plain path.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn variants(file: &syn::File) -> Result<Vec<Variant>, Refusal>
{
    let refusal = file
        .items
        .iter()
        .find_map(|item| {
            if let syn::Item::Enum(ref item) = *item
                && item.ident == "CheckRefusal"
            {
                Some(item)
            }
            else {
                None
            }
        })
        .ok_or_else(|| Refusal::Parse(String::from("refusal.rs holds no `CheckRefusal`")))?;
    refusal
        .variants
        .iter()
        .map(|variant| {
            let (shape, fields) = match variant.fields {
                syn::Fields::Unit => (Shape::Unit, Vec::new()),
                syn::Fields::Unnamed(ref fields) => (
                    Shape::Tuple,
                    fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(position, field)| field_of(position.to_string(), field))
                        .collect::<Result<_, _>>()?,
                ),
                syn::Fields::Named(ref fields) => (
                    Shape::Named,
                    fields
                        .named
                        .iter()
                        .map(|field| {
                            let name = field
                                .ident
                                .as_ref()
                                .map_or_else(String::new, ToString::to_string);
                            field_of(name, field)
                        })
                        .collect::<Result<_, _>>()?,
                ),
            };
            Ok(Variant {
                name: variant.ident.to_string(),
                docs: docs(&variant.attrs),
                shape,
                fields,
            })
        })
        .collect()
}

/// The names of the unit variants of `FrameRole`, in declaration order.
///
/// # Specification
/// - ensures: the name of each variant without a payload; a variant with a
///   payload is the caller's to write by hand.
/// - executable: none — a reading of a parsed file.
///
/// # Errors
/// [`Refusal::Parse`] when the file holds no `FrameRole`.
///
/// # Adequacy
/// - hypothesis: L2 — a kept failure's roles, a fold's among them, read back as
///   written.
/// - witness: `codec::tests::a_failure_content_round_trips`
fn frame_roles(file: &syn::File) -> Result<Vec<String>, Refusal>
{
    let roles = file
        .items
        .iter()
        .find_map(|item| {
            if let syn::Item::Enum(ref item) = *item
                && item.ident == "FrameRole"
            {
                Some(item)
            }
            else {
                None
            }
        })
        .ok_or_else(|| Refusal::Parse(String::from("failure.rs holds no `FrameRole`")))?;
    Ok(roles
        .variants
        .iter()
        .filter(|variant| matches!(variant.fields, syn::Fields::Unit))
        .map(|variant| variant.ident.to_string())
        .collect())
}

/// Write the macros that name a frame role and read it from its name into
/// `out`.
///
/// # Specification
/// - ensures: `frame_role_name` maps each role without a payload to its
///   variant's name, beside the arms the caller passes; `frame_role_named` maps
///   each such name back to its role, beside the arms the caller passes.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`frame_roles`].
/// - witness: `codec::tests::a_failure_content_round_trips`
fn emit_frame_roles(
    out: &mut String,
    roles: &[String],
) -> Result<(), Refusal>
{
    let mut named = String::new();
    let mut naming = String::new();
    for role in roles {
        writeln!(
            named,
            "{}::gandr_core_checker::FrameRole::{role} => b\"{role}\",",
            VARIANT.0
        )?;
        writeln!(
            naming,
            "{}b\"{role}\" => ::gandr_core_checker::FrameRole::{role},",
            VARIANT.0
        )?;
    }
    write!(
        out,
        "\n/// The stable name of a frame role, beside the arms the caller passes for\n/// the roles that hold a \
         payload.\nmacro_rules! frame_role_name {{\n    ($role:expr, {{ $($hand:tt)* }}) => {{\n        match \
         $role {{\n{named}            $($hand)*\n        }}\n    }};\n}}\n\n/// The frame role of a stable \
         name, beside the arms the caller passes.\nmacro_rules! frame_role_named {{\n    ($name:expr, {{ \
         $($hand:tt)* }}) => {{\n        match $name {{\n{naming}            $($hand)*\n        }}\n    \
         }};\n}}\n"
    )?;
    Ok(())
}

/// A field, read.
///
/// # Specification
/// - ensures: the field named `name`, its type's path segments and its
///   documentation.
/// - executable: none — a reading of a parsed field.
///
/// # Errors
/// [`Refusal::Parse`] when the type is not a path without arguments.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn field_of(
    name: String,
    field: &syn::Field,
) -> Result<Field, Refusal>
{
    let syn::Type::Path(ref path) = field.ty
    else {
        return Err(Refusal::Parse(format!("the field `{name}` is not a path")));
    };
    let ty = path
        .path
        .segments
        .iter()
        .map(|segment| {
            if matches!(segment.arguments, syn::PathArguments::None) {
                Ok(segment.ident.to_string())
            }
            else {
                Err(Refusal::Parse(format!(
                    "the field `{name}` carries type arguments"
                )))
            }
        })
        .collect::<Result<_, _>>()?;
    Ok(Field {
        name,
        ty,
        docs: docs(&field.attrs),
    })
}

/// The documentation lines of an item.
///
/// # Specification
/// - ensures: each `doc` attribute's text, in order, a link into the checker's
///   own modules named from the checker's crate.
/// - executable: none — a reading of parsed attributes.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn docs(attrs: &[syn::Attribute]) -> Vec<Doc>
{
    attrs
        .iter()
        .filter_map(|attr| {
            if let syn::Meta::NameValue(ref meta) = attr.meta
                && meta.path.is_ident("doc")
                && let syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(ref text),
                    ..
                }) = meta.value
            {
                // A link into the checker's own modules names them from the
                // store's crate.
                Some(Doc(text
                    .value()
                    .replace("`crate::", "`gandr_core_checker::")))
            }
            else {
                None
            }
        })
        .collect()
}

/// The absolute path of each name the checker's refusals module brings into
/// scope or declares, as the store's crate spells it.
///
/// # Specification
/// - ensures: a name the module imports maps to its import's path, with `crate`
///   read as `gandr_core_checker`; a name the module declares, or one the
///   checker's root re-exports, maps to the root's re-export.
/// - executable: none — a reading of parsed files.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn paths(
    file: &syn::File,
    lib: &syn::File,
) -> BTreeMap<String, String>
{
    let mut paths = BTreeMap::new();
    let mut reexported = BTreeSet::new();
    for item in &lib.items {
        if let syn::Item::Use(ref used) = *item
            && matches!(used.vis, syn::Visibility::Public(_))
            && let Some(segments) = use_path(&used.tree)
            && let Some(last) = segments.last()
        {
            reexported.insert(last.clone());
            paths.insert(segments.join("::"), format!("::gandr_core_checker::{last}"));
        }
    }
    for item in &file.items {
        if let syn::Item::Use(ref used) = *item
            && let Some(segments) = use_path(&used.tree)
        {
            let last = segments.last().cloned().unwrap_or_default();
            paths.insert(last, absolute(&segments, &reexported));
        }
        let declared = if let syn::Item::Enum(ref item) = *item {
            Some(&item.ident)
        }
        else if let syn::Item::Struct(ref item) = *item {
            Some(&item.ident)
        }
        else {
            None
        };
        if let Some(ident) = declared {
            paths.insert(ident.to_string(), format!("::gandr_core_checker::{ident}"));
        }
    }
    paths
}

/// The segments of a single-name `use` tree; none for a group or a glob.
///
/// # Specification
/// - ensures: the path's segments ending at the name it brings into scope.
/// - executable: none — a reading of a parsed tree.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn use_path(tree: &syn::UseTree) -> Option<Vec<String>>
{
    let mut segments = Vec::new();
    let mut tree = tree;
    loop {
        if let syn::UseTree::Path(ref path) = *tree {
            segments.push(path.ident.to_string());
            tree = &path.tree;
        }
        else if let syn::UseTree::Name(ref name) = *tree {
            segments.push(name.ident.to_string());
            return Some(segments);
        }
        else {
            return None;
        }
    }
}

/// A checker path as the store's crate spells it.
///
/// # Specification
/// - ensures: a path from `crate` names the checker's root re-export when the
///   root re-exports its last segment, and its module path otherwise; any other
///   path is made absolute.
/// - executable: none — string assembly.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn absolute(
    segments: &[String],
    reexported: &BTreeSet<String>,
) -> String
{
    match segments.split_first() {
        Some((first, rest)) if first == "crate" => match rest.last() {
            Some(last) if reexported.contains(last) => format!("::gandr_core_checker::{last}"),
            _ => format!("::gandr_core_checker::{}", rest.join("::")),
        },
        _ => format!("::{}", segments.join("::")),
    }
}

/// The table's `[roles]`, by the checker type each reads.
///
/// # Specification
/// - ensures: one [`Role`] per row, keyed by the type's name; a row's `contents
///   = true` marks a stored type that holds type contents.
/// - executable: none — a reading of a parsed table.
///
/// # Errors
/// [`Refusal::Table`] for a row without `stored` or `by`, or whose `contents`
/// is no boolean.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn roles(table: &toml::Table) -> Result<BTreeMap<String, Role>, Refusal>
{
    let roles = table
        .get("roles")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| Refusal::Table(String::from("the table has no `[roles]`")))?;
    roles
        .iter()
        .map(|(ty, row)| {
            let text = |key: &str| row.get(key).and_then(toml::Value::as_str).map(String::from);
            let stored = text("stored")
                .ok_or_else(|| Refusal::Table(format!("the role `{ty}` keeps no type")))?;
            let by = text("by")
                .ok_or_else(|| Refusal::Table(format!("the role `{ty}` names no method")))?;
            let holds = match row.get("contents").map(toml::Value::as_bool) {
                None | Some(Some(false)) => Holds::Nothing,
                Some(Some(true)) => Holds::Contents,
                Some(None) => {
                    return Err(Refusal::Table(format!(
                        "the role `{ty}` states `contents` as no boolean"
                    )));
                },
            };
            Ok((ty.clone(), Role {
                stored,
                by,
                site: text("site"),
                holds,
            }))
        })
        .collect()
}

/// The table's `[refusals]`, by refusal, checked against the checker's.
///
/// # Specification
/// - ensures: one [`Row`] per checker refusal.
/// - executable: none — a reading of a parsed table.
///
/// # Errors
/// [`Refusal::Table`] for a refusal without a row, a row without a refusal, a
/// row without a tag that the codec does not write by hand, a tag two rows
/// share, and a field a row names that its refusal lacks.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
fn rows(
    table: &toml::Table,
    variants: &[Variant],
) -> Result<BTreeMap<String, Row>, Refusal>
{
    let listed = table
        .get("refusals")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| Refusal::Table(String::from("the table has no `[refusals]`")))?;
    let mut rows = BTreeMap::new();
    let mut tags = BTreeMap::new();
    for variant in variants {
        let name = &variant.name;
        let row = listed
            .get(name)
            .ok_or_else(|| Refusal::Table(format!("the refusal `{name}` has no row")))?;
        let names = |key: &str| -> Result<BTreeSet<String>, Refusal> {
            let Some(list) = row.get(key)
            else {
                return Ok(BTreeSet::new());
            };
            let list = list
                .as_array()
                .ok_or_else(|| Refusal::Table(format!("`{name}`'s `{key}` is not a list")))?;
            let listed = list
                .iter()
                .map(|field| {
                    field.as_str().map(String::from).ok_or_else(|| {
                        Refusal::Table(format!("`{name}`'s `{key}` lists a non-name"))
                    })
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            let known = variant
                .fields
                .iter()
                .filter(|field| listed.contains(&field.name))
                .count();
            if known == listed.len() {
                Ok(listed)
            }
            else {
                Err(Refusal::Table(format!(
                    "`{name}`'s `{key}` names a field the refusal lacks"
                )))
            }
        };
        let hand = row.get("codec").and_then(toml::Value::as_str) == Some("hand");
        let tag = match row.get("tag").and_then(toml::Value::as_integer) {
            Some(tag) => Some(
                u8::try_from(tag)
                    .map_err(|_wide| Refusal::Table(format!("`{name}`'s tag is past a byte")))?,
            ),
            None if hand => None,
            None => return Err(Refusal::Table(format!("the refusal `{name}` has no tag"))),
        };
        if let Some(tag) = tag
            && let Some(other) = tags.insert(tag, name.clone())
        {
            return Err(Refusal::Table(format!(
                "`{other}` and `{name}` share the tag {tag}"
            )));
        }
        rows.insert(name.clone(), Row {
            tag,
            sites: names("sites")?,
            hand,
        });
    }
    if let Some(stray) = listed.keys().find(|name| !rows.contains_key(*name)) {
        return Err(Refusal::Table(format!(
            "the row `{stray}` names no refusal"
        )));
    }
    Ok(rows)
}

/// The fields of a refusal, as the generated code spells them.
///
/// # Specification
/// - ensures: each field, bound to its own name or to `field_<position>`,
///   beside its stored type, its projection and its seat by its type's role, or
///   the checker's type kept, the binding itself projected and the bound value
///   copied back; a field holds type contents exactly when its role's row says
///   so and the row does not read it as a site.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Table`] for a field `sites` names whose type's role reads no
/// site.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn kept<'variant>(
    variant: &'variant Variant,
    row: &Row,
    roles: &BTreeMap<String, Role>,
    paths: &BTreeMap<String, String>,
) -> Result<Vec<Kept<'variant>>, Refusal>
{
    variant
        .fields
        .iter()
        .map(|field| {
            let binding = match variant.shape {
                Shape::Tuple => format!("field_{}", field.name),
                Shape::Unit | Shape::Named => field.name.clone(),
            };
            let last = field.ty.last().cloned().unwrap_or_default();
            let (stored, projected, seated, holds) = match roles.get(&last) {
                Some(role) if row.sites.contains(&field.name) => {
                    let site = role.site.as_ref().ok_or_else(|| {
                        Refusal::Table(format!(
                            "`{}`'s `{}` reads no site",
                            variant.name, field.name
                        ))
                    })?;
                    (
                        String::from("Site"),
                        format!("$projection.{site}({binding})"),
                        format!("$seat.{site}({binding})?"),
                        Holds::Nothing,
                    )
                },
                Some(role) => (
                    role.stored.clone(),
                    format!("$projection.{}({binding})", role.by),
                    format!("$seat.{}({binding})?", role.by),
                    role.holds,
                ),
                None => (
                    spelled(&field.ty, paths),
                    binding.clone(),
                    format!("*{binding}"),
                    Holds::Nothing,
                ),
            };
            Ok(Kept {
                field,
                binding,
                stored,
                projected,
                seated,
                holds,
            })
        })
        .collect()
}

/// A kept checker type, as the store's crate spells it.
///
/// # Specification
/// - ensures: a single name the module brings into scope by its absolute path;
///   a longer path the checker's root re-exports by the re-export; any other
///   made absolute as [`absolute`] makes it.
/// - executable: none — string assembly.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn spelled(
    ty: &[String],
    paths: &BTreeMap<String, String>,
) -> String
{
    match *ty {
        [ref name] => paths.get(name).cloned().unwrap_or_else(|| name.clone()),
        _ => paths
            .get(&ty.join("::"))
            .cloned()
            .unwrap_or_else(|| absolute(ty, &BTreeSet::new())),
    }
}

/// What a generated construction builds each kept field from.
#[derive(Clone, Copy)]
enum Value
{
    /// The field's projection of its checker binding.
    Projected,
    /// The field read from the codec's reader.
    Read,
}

/// Write a refusal's stored construction into `out`.
///
/// # Specification
/// - ensures: `Refusal::<name>` built in its stored shape, each kept field from
///   its projection or its read, in declaration order.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn write_built(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
    value: Value,
) -> Result<(), Refusal>
{
    write!(out, "Refusal::{}", variant.name)?;
    let (open, close) = match variant.shape {
        Shape::Unit => return Ok(()),
        Shape::Tuple => ("(", ")"),
        Shape::Named => (" { ", " }"),
    };
    out.push_str(open);
    for (position, kept) in kept.iter().enumerate() {
        if position > 0 {
            out.push_str(", ");
        }
        let built = match value {
            Value::Projected => kept.projected.as_str(),
            Value::Read => "Field::read($reader)?",
        };
        if variant.shape == Shape::Named && built != kept.field.name {
            write!(out, "{}: ", kept.field.name)?;
        }
        out.push_str(built);
    }
    out.push_str(close);
    Ok(())
}

/// Write a refusal's stored pattern into `out`, its kept fields bound by
/// reference.
///
/// # Specification
/// - ensures: `Refusal::<name>` with each kept field bound to its binding by
///   `ref`, in its stored shape.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
fn write_stored_pattern(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
) -> Result<(), Refusal>
{
    write!(out, "Refusal::{}", variant.name)?;
    let (open, close) = match variant.shape {
        Shape::Unit => return Ok(()),
        Shape::Tuple => ("(", ")"),
        Shape::Named => (" { ", " }"),
    };
    out.push_str(open);
    for (position, kept) in kept.iter().enumerate() {
        if position > 0 {
            out.push_str(", ");
        }
        write!(out, "ref {}", kept.binding)?;
    }
    out.push_str(close);
    Ok(())
}

/// Write a refusal's stored pattern into `out`, binding by reference only
/// the kept fields that hold type contents.
///
/// # Specification
/// - ensures: `Refusal::<name>` in its stored shape, each kept field that holds
///   type contents bound to its binding by `ref`, and each other field skipped.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `codec::tests::every_refusal_holding_a_capped_level_is_refused_when_written_4451`
fn write_contents_pattern(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
) -> Result<(), Refusal>
{
    write!(out, "Refusal::{}", variant.name)?;
    match variant.shape {
        Shape::Unit => {},
        Shape::Tuple => {
            out.push('(');
            for (position, kept) in kept.iter().enumerate() {
                if position > 0 {
                    out.push_str(", ");
                }
                match kept.holds {
                    Holds::Contents => write!(out, "ref {}", kept.binding)?,
                    Holds::Nothing => out.push('_'),
                }
            }
            out.push(')');
        },
        Shape::Named => {
            out.push_str(" { ");
            for kept in kept.iter().filter(|kept| kept.holds == Holds::Contents) {
                write!(out, "ref {}, ", kept.binding)?;
            }
            out.push_str(".. }");
        },
    }
    Ok(())
}

/// Write a checker refusal's pattern into `out`, its fields bound.
///
/// # Specification
/// - ensures: `::gandr_core_checker::CheckRefusal::<name>` with each field
///   bound to its binding.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn write_checker_pattern(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
) -> Result<(), Refusal>
{
    write!(out, "::gandr_core_checker::CheckRefusal::{}", variant.name)?;
    let (open, close) = match variant.shape {
        Shape::Unit => return Ok(()),
        Shape::Tuple => ("(", ")"),
        Shape::Named => (" { ", " }"),
    };
    out.push_str(open);
    for (position, kept) in kept.iter().enumerate() {
        if position > 0 {
            out.push_str(", ");
        }
        out.push_str(&kept.binding);
    }
    out.push_str(close);
    Ok(())
}

/// Write a checker refusal's construction into `out`, each field seated from
/// the stored refusal's binding.
///
/// # Specification
/// - ensures: `::gandr_core_checker::CheckRefusal::<name>` with each field
///   built by its seat, in declaration order: the order the projection reads
///   the fields in.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L3 — a refused corpus item's refusal, seated from its
///   checkpoint, renders the diagnostic of the whole judgement.
/// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
fn write_seated(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
) -> Result<(), Refusal>
{
    write!(out, "::gandr_core_checker::CheckRefusal::{}", variant.name)?;
    let (open, close) = match variant.shape {
        Shape::Unit => return Ok(()),
        Shape::Tuple => ("(", ")"),
        Shape::Named => (" { ", " }"),
    };
    out.push_str(open);
    for (position, kept) in kept.iter().enumerate() {
        if position > 0 {
            out.push_str(", ");
        }
        if variant.shape == Shape::Named {
            write!(out, "{}: ", kept.field.name)?;
        }
        out.push_str(&kept.seated);
    }
    out.push_str(close);
    Ok(())
}

/// Write a documentation line into `out` as a `doc` attribute, indented by
/// `indent`.
///
/// # Specification
/// - ensures: `#[doc = "<line>"]`, each character a Rust string literal cannot
///   hold as itself escaped.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn write_doc(
    out: &mut String,
    indent: Indent,
    line: &Doc,
) -> Result<(), Refusal>
{
    writeln!(out, "{}#[doc = \"{}\"]", indent.0, line.0.escape_default())?;
    Ok(())
}

/// Write a refusal's stored declaration into `out`.
///
/// # Specification
/// - ensures: the checker's documentation, then the refusal in its stored
///   shape, each kept field at its stored type under its own documentation.
/// - executable: none — string assembly.
///
/// # Errors
/// [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `typing::tests::each_refusal_projects_its_payload`
fn write_declared(
    out: &mut String,
    variant: &Variant,
    kept: &[Kept<'_>],
) -> Result<(), Refusal>
{
    for line in &variant.docs {
        write_doc(out, VARIANT, line)?;
    }
    write!(out, "{}{}", VARIANT.0, variant.name)?;
    match variant.shape {
        Shape::Unit => {},
        Shape::Tuple => {
            out.push('(');
            for (position, kept) in kept.iter().enumerate() {
                if position > 0 {
                    out.push_str(", ");
                }
                out.push_str(&kept.stored);
            }
            out.push(')');
        },
        Shape::Named => {
            out.push_str(" {\n");
            for kept in kept {
                for line in &kept.field.docs {
                    write_doc(out, FIELD, line)?;
                }
                writeln!(out, "{}{}: {},", FIELD.0, kept.field.name, kept.stored)?;
            }
            out.push_str(VARIANT.0);
            out.push('}');
        },
    }
    out.push_str(",\n");
    Ok(())
}

/// Write the seven macros into `out`.
///
/// # Specification
/// - ensures: `refusal_enum` declares the store's enum, each refusal with the
///   checker's documentation and its fields at their stored types;
///   `refusal_projection` projects each checker refusal; `refusal_seat` builds
///   each checker refusal again from a stored one, each field by its seat in
///   declaration order; `refusal_kept` compares a checker refusal's kind with a
///   stored one's; `refusal_write` and `refusal_read` hold one arm per refusal
///   not written by hand, each its tag followed by its fields in declaration
///   order, beside the arms the caller passes; `refusal_contents` passes each
///   field that holds type contents to the caller's visitor in declaration
///   order, one arm for the refusals that bind the same fields at the same
///   types.
/// - executable: none — string assembly.
///
/// # Errors
/// As [`kept`], or [`Refusal::Format`] when the text does not format.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `codec::tests::every_refusal_round_trips_under_its_own_encoding`
/// - witness: `codec::tests::every_refusal_holding_a_capped_level_is_refused_when_written_4451`
fn emit(
    out: &mut String,
    variants: &[Variant],
    rows: &BTreeMap<String, Row>,
    roles: &BTreeMap<String, Role>,
    paths: &BTreeMap<String, String>,
) -> Result<(), Refusal>
{
    let mut declared = String::new();
    let mut projection = String::new();
    let mut seat = String::new();
    let mut kinds = String::new();
    let mut write = String::new();
    let mut read = String::new();
    // The refusals by the fields that hold type contents, each with its stored
    // type: refusals that bind the same fields share one arm.
    let mut held: BTreeMap<Vec<(String, String)>, Vec<String>> = BTreeMap::new();
    for variant in variants {
        let Some(row) = rows.get(&variant.name)
        else {
            continue;
        };
        let kept = kept(variant, row, roles, paths)?;
        let name = &variant.name;
        write_declared(&mut declared, variant, &kept)?;
        let mut pattern = String::new();
        write_contents_pattern(&mut pattern, variant, &kept)?;
        held.entry(
            kept.iter()
                .filter(|kept| kept.holds == Holds::Contents)
                .map(|kept| (kept.binding.clone(), kept.stored.clone()))
                .collect(),
        )
        .or_default()
        .push(pattern);
        projection.push_str(VARIANT.0);
        write_checker_pattern(&mut projection, variant, &kept)?;
        projection.push_str(" => ");
        write_built(&mut projection, variant, &kept, Value::Projected)?;
        projection.push_str(",\n");
        seat.push_str(VARIANT.0);
        write_stored_pattern(&mut seat, variant, &kept)?;
        seat.push_str(" => ");
        write_seated(&mut seat, variant, &kept)?;
        seat.push_str(",\n");
        if !kinds.is_empty() {
            kinds.push_str("\n            | ");
        }
        write!(
            kinds,
            "(::gandr_core_checker::CheckRefusal::{name} {{ .. }}, Refusal::{name} {{ .. }})"
        )?;
        let Some(tag) = row.tag.filter(|_tag| !row.hand)
        else {
            continue;
        };
        write.push_str(VARIANT.0);
        write_stored_pattern(&mut write, variant, &kept)?;
        write!(write, " => {{ $writer.tag(Tag({tag}));")?;
        for kept in &kept {
            write!(write, " Field::write({}, $writer)?;", kept.binding)?;
        }
        writeln!(write, " }},")?;
        write!(read, "{}{tag} => ", VARIANT.0)?;
        write_built(&mut read, variant, &kept, Value::Read)?;
        read.push_str(",\n");
    }
    let mut contents = String::new();
    for (fields, patterns) in &held {
        contents.push_str(VARIANT.0);
        for (position, pattern) in patterns.iter().enumerate() {
            if position > 0 {
                write!(contents, "\n{}| ", VARIANT.0)?;
            }
            contents.push_str(pattern);
        }
        contents.push_str(" => {");
        match fields.split_last() {
            None => contents.push_str(" Ok(())"),
            Some((&(ref last, _), rest)) => {
                for &(ref binding, _) in rest {
                    write!(contents, " Contents::each_content({binding}, $visit)?;")?;
                }
                write!(contents, " Contents::each_content({last}, $visit)")?;
            },
        }
        contents.push_str(" },\n");
    }
    write!(
        out,
        "/// The store's `Refusal`, declared under the attributes and the name the\n/// caller writes: one \
         variant per checker refusal.\nmacro_rules! refusal_enum {{\n    ($(#[$meta:meta])* $vis:vis enum \
         $name:ident) => {{\n        $(#[$meta])*\n        $vis enum $name {{\n{declared}        }}\n    \
         }};\n}}\n\n"
    )?;
    write!(
        out,
        "/// The projection of a checker refusal through the projection `$projection`.\nmacro_rules! \
         refusal_projection {{\n    ($projection:ident, $refusal:expr) => {{\n        match $refusal \
         {{\n{projection}        }}\n    }};\n}}\n\n"
    )?;
    write!(
        out,
        "/// The checker refusal a stored one seats to through the seat `$seat`; each\n/// failed seat returns \
         its reason from the caller.\nmacro_rules! refusal_seat {{\n    ($seat:ident, $refusal:expr) => {{\n        \
         match *$refusal {{\n{seat}        }}\n    }};\n}}\n\n"
    )?;
    write!(
        out,
        "/// Whether a checker refusal and a stored one are of the same kind.\nmacro_rules! refusal_kept {{\n    \
         ($checker:expr, $stored:expr) => {{\n        matches!(($checker, $stored), {kinds})\n    }};\n}}\n\n"
    )?;
    write!(
        out,
        "/// The arms of `write_refusal`, beside the hand-written arms the caller passes.\nmacro_rules! \
         refusal_write {{\n    ($writer:ident, $refusal:expr, {{ $($hand:tt)* }}) => {{\n        match \
         *$refusal {{\n{write}            $($hand)*\n        }}\n    }};\n}}\n\n"
    )?;
    write!(
        out,
        "/// The arms of `read_refusal` by tag, beside the hand-written arms the caller\n/// passes.\nmacro_rules! \
         refusal_read {{\n    ($reader:ident, $tag:expr, {{ $($hand:tt)* }}) => {{\n        match $tag \
         {{\n{read}            $($hand)*\n        }}\n    }};\n}}\n"
    )?;
    write!(
        out,
        "\n/// The type contents a stored refusal holds, each passed to `$visit` in the\n/// order the codec \
         writes them; the first error stops the walk.\nmacro_rules! refusal_contents {{\n    \
         ($refusal:expr, $visit:ident) => {{\n        match *$refusal {{\n{contents}        }}\n    }};\n}}\n"
    )?;
    Ok(())
}
