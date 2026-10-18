//! The source lines of every `#[spec]` attribute in the workspace.
//!
//! anodized expands each clause with the clause's own spans, so the machine
//! code that checks a specification carries the attribute's lines in its line
//! table. A sampled frame whose line falls inside an attribute is that
//! specification's check; the attribute is the region the sample is charged
//! to.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::error::CostError;

/// A one-based line number in a source file.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Line(usize);

impl From<usize> for Line
{
    /// Reads `line` as a one-based line number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(line: usize) -> Self
    {
        Self(line)
    }
}

impl fmt::Display for Line
{
    /// Writes the line number in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The item a specification is attached to, as `Type::method`, `function`,
/// `<Type as Trait>::method` or `Type`, prefixed by the inline modules that
/// enclose it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ItemName(String);

impl fmt::Display for ItemName
{
    /// Writes the name as built.
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

impl From<&str> for ItemName
{
    /// Adopts `name` as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

/// The text of one Rust source file.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct SourceText<'text>(&'text str);

impl<'text> From<&'text str> for SourceText<'text>
{
    /// Adopts `text` as a source file's contents.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// One `#[spec]` attribute: its file, the lines it spans and its item.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Region
{
    /// The file, as the scan named it.
    pub file: PathBuf,
    /// The line of the attribute's `#`.
    pub first: Line,
    /// The line of its closing `]`.
    pub last: Line,
    /// The item it specifies.
    pub item: ItemName,
}

quenchant_shape::reason_enum! {
    /// Why a source line belongs to no specification.
    pub mod lookup {
        /// The reason a line has no region.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The scan read no specification in the file.
            UnscannedFile,
            /// The line lies outside every attribute of the file.
            OutsideEveryAttribute,
        }
    }
}

/// Every specification region, grouped by file and ordered by first line.
///
/// # Specification
/// - provides: the lookup from a sampled source line to the attribute enclosing
///   it; attributes never overlap, so a line has at most one.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Regions(BTreeMap<PathBuf, Vec<Region>>);

impl Regions
{
    /// Reads every `.rs` file under `root/crates`, skipping `target` and hidden
    /// directories.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one region per `#[spec]` attribute on a function, method,
    ///   trait or type item of every file read, keyed by `root/crates/…`.
    /// - provides: the regions a ranking charges samples to.
    /// - fails: [`CostError::Io`] for a directory or file that cannot be read;
    ///   [`CostError::Source`] for a file the parser rejects.
    /// - panics: none.
    /// - executable: none — the outcome depends on the tree on disk.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fake workspace with specifications in two crates
    ///   and a `target` directory holding one more; a scan that read `target`,
    ///   missed a crate or keyed files differently changes the ranking.
    /// - witness: `tests::cli::a_profile_is_charged_to_its_outermost_specification`
    #[inline]
    pub fn scan(root: &Path) -> Result<Self, CostError>
    {
        let mut regions = Self::default();
        let mut pending = vec![root.join("crates")];
        while let Some(dir) = pending.pop() {
            let entries = std::fs::read_dir(&dir).map_err(|error| CostError::Io {
                path: dir.clone(),
                message: error.to_string(),
            })?;
            for entry in entries {
                let path = entry
                    .map_err(|error| CostError::Io {
                        path: dir.clone(),
                        message: error.to_string(),
                    })?
                    .path();
                let hidden = path.file_name().is_some_and(|name| {
                    name == "target" || name.to_string_lossy().starts_with('.')
                });
                if hidden {
                    continue;
                }
                if path.is_dir() {
                    pending.push(path);
                }
                else if path.extension().is_some_and(|extension| extension == "rs") {
                    let text = std::fs::read_to_string(&path).map_err(|error| CostError::Io {
                        path: path.clone(),
                        message: error.to_string(),
                    })?;
                    regions.insert_source(&path, SourceText::from(text.as_str()))?;
                }
            }
        }
        Ok(regions)
    }

    /// Reads the specification regions of one file.
    ///
    /// # Specification
    /// - requires: nothing — any text is admissible input.
    /// - ensures: the file's regions replace any recorded for `path`, ordered
    ///   by first line; a file with none records nothing.
    /// - provides: the per-file step of [`Regions::scan`].
    /// - fails: [`CostError::Source`] when `text` is not a Rust file.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CostError::Source`] — the parser rejected the file.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free functions, inherent and trait impls, trait
    ///   methods, types and an inline module, with one- and multi-line
    ///   attributes beside doc comments; a missed item kind, a wrong last line
    ///   or a lost module prefix changes the asserted regions.
    /// - witness: `region::tests::every_spec_attribute_is_a_region`
    #[spec(ensures: |ref ret| ret.is_err() || self.0.get(path).is_none_or(|regions| regions.is_sorted_by(|left, right| left.last < right.first)))]
    #[inline]
    pub fn insert_source(
        &mut self,
        path: &Path,
        text: SourceText<'_>,
    ) -> Result<(), CostError>
    {
        let file = syn::parse_file(text.0).map_err(|error| CostError::Source {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        let mut found = Vec::new();
        let mut pending: Vec<(&syn::Item, String)> = file
            .items
            .iter()
            .rev()
            .map(|item| (item, String::new()))
            .collect();
        while let Some((item, prefix)) = pending.pop() {
            let mut attach = |attrs: &[syn::Attribute], name: String| {
                // Matching the last segment counts `#[spec]` and
                // `#[anodized::spec]` alike.
                let specs = attrs.iter().filter(|attr| {
                    attr.path()
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident == "spec")
                });
                for attr in specs {
                    found.push(Region {
                        file: path.to_path_buf(),
                        first: Line(attr.pound_token.span.start().line),
                        last: Line(attr.bracket_token.span.close().end().line),
                        item: ItemName(name.clone()),
                    });
                }
            };
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "`syn::Item` is non-exhaustive, so a wildcard arm is required; only a \
                          function, an impl, a trait, a struct, an enum or a module carries a \
                          specification region"
            )]
            match *item {
                syn::Item::Fn(ref function) => {
                    attach(&function.attrs, format!("{prefix}{}", function.sig.ident));
                },
                syn::Item::Impl(ref block) => {
                    let owner = owner_of(block);
                    for member in &block.items {
                        if let syn::ImplItem::Fn(ref method) = *member {
                            attach(
                                &method.attrs,
                                format!("{prefix}{owner}::{}", method.sig.ident),
                            );
                        }
                    }
                },
                syn::Item::Trait(ref interface) => {
                    attach(&interface.attrs, format!("{prefix}{}", interface.ident));
                    for member in &interface.items {
                        if let syn::TraitItem::Fn(ref method) = *member {
                            attach(
                                &method.attrs,
                                format!("{prefix}{}::{}", interface.ident, method.sig.ident),
                            );
                        }
                    }
                },
                syn::Item::Struct(ref record) => {
                    attach(&record.attrs, format!("{prefix}{}", record.ident));
                },
                syn::Item::Enum(ref choice) => {
                    attach(&choice.attrs, format!("{prefix}{}", choice.ident));
                },
                syn::Item::Mod(ref module) => {
                    if let Some((_, ref items)) = module.content {
                        let inner = format!("{prefix}{}::", module.ident);
                        pending.extend(items.iter().rev().map(|item| (item, inner.clone())));
                    }
                },
                _ => {},
            }
        }
        if found.is_empty() {
            self.0.remove(path);
        }
        else {
            found.sort_by_key(|region| region.first);
            self.0.insert(path.to_path_buf(), found);
        }
        Ok(())
    }

    /// The region enclosing `line` of `file`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the region of `file` whose lines include `line`, if any.
    /// - provides: [`lookup::Absent::UnscannedFile`] for a file without
    ///   regions; [`lookup::Absent::OutsideEveryAttribute`] for a line outside
    ///   all of them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first and last line of an attribute, the lines
    ///   either side, a line between two attributes and an unscanned file; an
    ///   off-by-one bound or a search that took the next region changes a
    ///   lookup.
    /// - witness: `region::tests::a_line_finds_the_attribute_enclosing_it`
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(region) => region.file == file && region.first <= line && line <= region.last,
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn find(
        &self,
        file: &Path,
        line: Line,
    ) -> Maybe<&Region, lookup::Absent>
    {
        let Some(regions) = self.0.get(file)
        else {
            return Maybe::Absent(lookup::Absent::UnscannedFile);
        };
        let after = regions.partition_point(|region| region.first <= line);
        match after.checked_sub(1).and_then(|index| regions.get(index)) {
            Some(region) if line <= region.last => Maybe::Present(region),
            Some(_) | None => Maybe::Absent(lookup::Absent::OutsideEveryAttribute),
        }
    }
}

/// The name an impl block's methods are listed under: `Type`, or
/// `<Type as Trait>` for a trait impl; `_` stands for a type that is not a
/// path.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the self type's last path segment, wrapped with the trait's last
///   segment when the block implements one.
/// - provides: method names a reader can find in the source.
/// - panics: none.
/// - executable: none — the name is built from the same segments it would be
///   checked against.
///
/// # Adequacy
/// - hypothesis: L3 — an inherent and a trait impl; a swapped type and trait or
///   a lost wrapper changes the asserted item names.
/// - witness: `region::tests::every_spec_attribute_is_a_region`
fn owner_of(block: &syn::ItemImpl) -> ItemName
{
    let last = |path: &syn::Path| {
        path.segments
            .last()
            .map_or_else(|| "_".to_owned(), |segment| segment.ident.to_string())
    };
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "`syn::Type` is non-exhaustive, so a wildcard arm is required; only a path names \
                  the implementing type"
    )]
    let owner = match *block.self_ty {
        syn::Type::Path(ref typed) => last(&typed.path),
        _ => "_".to_owned(),
    };
    ItemName(match block.trait_ {
        Some((ref interface, _)) => format!("<{owner} as {}>", last(interface)),
        None => owner,
    })
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use quenchant_shape::shape::Maybe;

    use super::ItemName;
    use super::Line;
    use super::Region;
    use super::Regions;
    use super::SourceText;
    use super::lookup;

    const SOURCE: &str = r#"
/// A free function.
#[spec(ensures: |ret| ret)]
fn free() -> bool { true }

struct Counter(u8);

#[spec(predicate: |counter| counter.0 < 9)]
struct Bounded(u8);

impl Counter
{
    /// Two lines of attribute.
    #[spec(
        ensures: |ret| ret <= self.0)]
    #[inline]
    fn get(&self) -> u8 { self.0 }

    fn bare(&self) {}
}

impl Clone for Counter
{
    #[anodized::spec(ensures: |ret| ret.0 == self.0)]
    fn clone(&self) -> Self { Self(self.0) }
}

trait Count
{
    #[spec(ensures: |ret| ret > 0)]
    fn count(&self) -> u8;
}

mod inner
{
    #[spec(requires: true)]
    fn nested() {}
}
"#;

    #[test]
    fn every_spec_attribute_is_a_region()
    {
        let mut regions = Regions::default();
        regions
            .insert_source(Path::new("crates/a/src/lib.rs"), SourceText::from(SOURCE))
            .unwrap();
        let region = |first, last, item: &str| Region {
            file: Path::new("crates/a/src/lib.rs").to_path_buf(),
            first: Line(first),
            last: Line(last),
            item: ItemName(item.to_owned()),
        };
        assert_eq!(
            regions.0.get(Path::new("crates/a/src/lib.rs")),
            Some(&vec![
                region(3, 3, "free"),
                region(8, 8, "Bounded"),
                region(14, 15, "Counter::get"),
                region(24, 24, "<Counter as Clone>::clone"),
                region(30, 30, "Count::count"),
                region(36, 36, "inner::nested"),
            ]),
            "each attribute's `#` to `]`, under the item it specifies"
        );
        let mut empty = Regions::default();
        empty
            .insert_source(
                Path::new("crates/b/src/lib.rs"),
                SourceText::from("fn f() {}"),
            )
            .unwrap();
        assert_eq!(
            empty,
            Regions::default(),
            "a file without specifications records nothing"
        );
        assert!(
            empty
                .insert_source(
                    Path::new("crates/b/src/lib.rs"),
                    SourceText::from("fn f( {")
                )
                .is_err(),
            "a file the parser rejects is refused"
        );
    }

    #[test]
    fn a_line_finds_the_attribute_enclosing_it()
    {
        let mut regions = Regions::default();
        regions
            .insert_source(Path::new("crates/a/src/lib.rs"), SourceText::from(SOURCE))
            .unwrap();
        let file = Path::new("crates/a/src/lib.rs");
        let find = |line| match regions.find(file, Line(line)) {
            Maybe::Present(found) => Maybe::Present(found.item.clone()),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let named = |name: &str| Maybe::Present(ItemName(name.to_owned()));
        assert_eq!(find(3), named("free"), "a one-line attribute");
        assert_eq!(find(14), named("Counter::get"), "the `#` line");
        assert_eq!(find(15), named("Counter::get"), "the `]` line");
        assert_eq!(
            find(13),
            Maybe::Absent(lookup::Absent::OutsideEveryAttribute),
            "the doc comment above"
        );
        assert_eq!(
            find(16),
            Maybe::Absent(lookup::Absent::OutsideEveryAttribute),
            "the line below"
        );
        assert_eq!(
            find(20),
            Maybe::Absent(lookup::Absent::OutsideEveryAttribute),
            "between two attributes"
        );
        assert_eq!(
            find(1),
            Maybe::Absent(lookup::Absent::OutsideEveryAttribute),
            "before the first attribute"
        );
        assert_eq!(
            regions.find(Path::new("crates/b/src/lib.rs"), Line(3)),
            Maybe::Absent(lookup::Absent::UnscannedFile),
            "a file the scan did not record"
        );
    }
}
