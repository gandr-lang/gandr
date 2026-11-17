//! An import as its tiles spell it, read before any import binds.
//!
//! The import gives the address, the alias, the signature, the translation and
//! the list. The description route reads the imports of each source through
//! [`unqualified_imports`], and the lowering's collection reads each import
//! through [`read_import`].

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::unit::ImportTarget;
use crate::unit::PathImportOrdinal;
use crate::unit::SourceIndex;
use crate::unit::Unit;

/// The reason the import policy gives for refusing a second binding of one
/// alias.
pub const ONE_SOURCE: &str = "an import alias must name one source";

/// The address an import names, its escapes decoded and nothing resolved.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportUri(String);

impl From<String> for ImportUri
{
    /// The address `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for ImportUri
{
    /// The address's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

impl fmt::Display for ImportUri
{
    /// Writes the address's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_str())
    }
}

/// A translation as its tiles spell it, after an import's signature or after
/// an offer's module.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum WrittenTranslation
{
    /// `via f`: the flow's name tile.
    Via(Placed),
    /// `renaming { fetch as get, … }`: each pair's tiles, the member read
    /// first and the name it is read as second, in written order.
    Renaming(Vec<(Placed, Placed)>),
}

quenchant_shape::reason_enum! {
    /// Why an import or an offer is read through no flow.
    pub mod direct {
        /// The reason none is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No translation follows the import's signature or the offer's
            /// module, so it is read as it is.
            Unwritten,
            /// A renaming follows it, so it is read by name through the
            /// renaming and through no flow.
            Renamed,
        }
    }
}

/// Whether an import's address names a scheme, a package's coordinate, a
/// path or a module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Address
{
    /// `scheme:…`: a letter, then letters, digits, `+`, `-` or `.`, then a
    /// colon (RFC 3986 § 3.1), the scheme no coordinate's.
    Scheme,
    /// `path:…`: the coordinate of a package rooted at the directory the rest
    /// names, whose root module the import reads.
    Coordinate,
    /// Anything else written between quotes: a path relative to the importing
    /// source.
    Path,
    /// A module path written bare, `text.greet`: the file `text/greet.gandr`
    /// relative to the directory of the package's root module.
    Module,
}

impl Address
{
    /// What `uri` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Address::Coordinate`] exactly when `uri` opens with the
    ///   scheme [`PATH_SCHEME`] or [`GITHUB_SCHEME`] and its colon;
    ///   [`Address::Scheme`] when it opens with another RFC 3986 scheme and its
    ///   colon; [`Address::Path`] otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `file:` URL, a `path:` and a `gh:` coordinate, a
    ///   relative path, a path holding a colon after a slash and a scheme
    ///   opening with a digit each classify exactly.
    /// - witness: `written_import::tests::an_address_names_a_scheme_a_coordinate_or_a_path`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == Self::Path || uri.as_ref().contains(':'))]
    pub fn of(uri: &ImportUri) -> Self
    {
        let text = uri.as_ref();
        let Some(colon) = text.find(':')
        else {
            return Self::Path;
        };
        let scheme = text.get(.. colon).unwrap_or_default();
        let mut characters = scheme.chars();
        let opens = characters
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic());
        let rest = characters
            .all(|later| later.is_ascii_alphanumeric() || matches!(later, '+' | '-' | '.'));
        if !(opens && rest) {
            Self::Path
        }
        else if scheme == PATH_SCHEME || scheme == GITHUB_SCHEME {
            Self::Coordinate
        }
        else {
            Self::Scheme
        }
    }
}

/// The scheme of a package's coordinate on disk, `path:../hello`: a
/// directory, read from the importing package's root, that roots the package.
pub const PATH_SCHEME: &str = "path";

/// The scheme of a package's coordinate on GitHub, `gh:acme-org/rope`: the
/// repository whose top directory roots the package, at the revision the
/// importing package's lock records.
pub const GITHUB_SCHEME: &str = "gh";

/// One import as its tiles spell it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenImport
{
    /// The address, its escapes decoded; for a module path, the file it names
    /// relative to the root module's directory, `text/greet.gandr`.
    pub uri: ImportUri,
    /// The alias, when one is written.
    pub alias: Maybe<Placed, unaliased::Absent>,
    /// The names the import's list binds by their own names, in the order
    /// written; empty when no list is written.
    pub listed: Vec<Placed>,
    /// The signature the import is written at, `: Gandr.Package`: the
    /// segments of its path, the theory's name last; empty when none is
    /// written.
    pub signature: Vec<Placed>,
    /// The translation the signature is read through, `via f` or `renaming
    /// { fetch as get }`, as its tiles spell it.
    pub translation: Maybe<WrittenTranslation, direct::Absent>,
    /// The bytes the import covers.
    pub span: ByteSpan,
    /// The bytes between the address's quotes, as written, escapes included;
    /// for a module path, the path's from its first name to its last.
    pub addressed: ByteSpan,
    /// What the address names.
    pub address: Address,
}

quenchant_shape::reason_enum! {
    /// Why an import has no alias.
    pub mod unaliased {
        /// The reason none is written.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The import binds its sibling's exports unqualified.
            Unqualified,
            /// The import binds its module qualified, under the module path
            /// it names.
            Pathed,
        }
    }
}

/// Read one import form's pieces.
///
/// # Specification
/// - requires: `pieces` is the reading of the import `import`.
/// - ensures: the import the tiles `import " … " (as name)? (: Path
///   (translation)?)? (( names ))? ;` spell, in that order with nothing after
///   them, its address read between the quotes; or the tiles `import name (.
///   name)* (as name)? (: Path (translation)?)? (( names ))? ;`, its address
///   the module path's file, as [`module_file`] names it, and bound under the
///   path when no alias is written. `Path` is a type name then any number of
///   dotted names of either case, each kept in `signature`; the translation, as
///   [`read_translation`] reads it, is kept in `translation`. `names` is one
///   name or more, separated by commas, a trailing one admitted, each kept in
///   `listed`.
/// - provides: the reading the collection and [`written_imports`] share.
/// - fails: [`LoweringRefusal::MalformedForm`] for a repair, naming the form
///   inside the import that holds it or else `form`, as
///   [`Repaired::refusal`](crate::form::Repaired::refusal) names it; and naming
///   `form` for a tile out of place.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`].
///
/// # Adequacy
/// - hypothesis: L3 — exact address decoding with and without an alias, and a
///   tile out of place, distinguish reading from binding refusal.
/// - witness: `gandr-surface-lowering::tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `gandr-surface-lowering::tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `gandr-surface-lowering::tests::namespace::an_import_repaired_inside_a_nested_form_is_refused_by_that_form`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref entry) => entry.span == import.span && {
            let (outer, inner) = (import.span, entry.addressed);
            outer.start() <= inner.start() && inner.end() <= outer.end()
        },
        | Err(LoweringRefusal::MalformedForm { form: found, .. }) => found == form
            || matches!(pieces.repair, Maybe::Present(crate::form::Repaired { nested: Maybe::Present(inner), .. }) if inner == found),
        | Err(_) => false,
    },
)]
#[inline]
pub fn read_import<'source>(
    tree: &SyntaxTree<'source>,
    import: Placed,
    form: FormName,
    pieces: &Pieces,
) -> Result<WrittenImport, LoweringRefusal<'source>>
{
    if let Maybe::Present(repaired) = pieces.repair {
        return Err(repaired.refusal(form));
    }
    let out_of_place = |cursor: &Cursor<'_>| LoweringRefusal::MalformedForm {
        span: cursor.here(),
        form,
        fault: FormFault::MisplacedTile,
    };
    let mut cursor = Cursor::new(&pieces.pieces, import.span);
    if let Maybe::Absent(_) = cursor.tile(TileName::IMPORT) {
        return Err(out_of_place(&cursor));
    }
    let (uri, addressed, address) = match quoted(tree, &mut cursor) {
        Maybe::Present((written, addressed)) => {
            let uri = ImportUri::from(written);
            let address = Address::of(&uri);
            (uri, addressed, address)
        },
        Maybe::Absent(quoted_text::Absent::Unclosed) => return Err(out_of_place(&cursor)),
        Maybe::Absent(quoted_text::Absent::Unopened) => {
            let Maybe::Present(first) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(out_of_place(&cursor));
            };
            let mut last = first;
            while let Maybe::Present(_) = cursor.tile(TileName::DOT) {
                let Maybe::Present(next) = cursor.tile(TileName::IDENTIFIER)
                else {
                    return Err(out_of_place(&cursor));
                };
                last = next;
            }
            let addressed = ByteSpan::new(first.span.start(), last.span.end())
                .map_err(|_inverted| out_of_place(&cursor))?;
            let Some(path) = tree.spanned(addressed)
            else {
                return Err(out_of_place(&cursor));
            };
            (module_file(path), addressed, Address::Module)
        },
    };
    let alias = match cursor.tile(TileName::AS) {
        Maybe::Present(_) => match cursor.tile(TileName::IDENTIFIER) {
            Maybe::Present(alias) => Maybe::Present(alias),
            Maybe::Absent(_) => return Err(out_of_place(&cursor)),
        },
        Maybe::Absent(_) if address == Address::Module => Maybe::Absent(unaliased::Absent::Pathed),
        Maybe::Absent(_) => Maybe::Absent(unaliased::Absent::Unqualified),
    };
    let mut signature = Vec::new();
    let mut translation = Maybe::Absent(direct::Absent::Unwritten);
    if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
        let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(out_of_place(&cursor));
        };
        signature.push(head);
        while let Maybe::Present(_) = cursor.tile(TileName::DOT) {
            match cursor.tile(TileName::TYPE_IDENTIFIER) {
                Maybe::Present(segment) => signature.push(segment),
                Maybe::Absent(_) => match cursor.tile(TileName::IDENTIFIER) {
                    Maybe::Present(segment) => signature.push(segment),
                    Maybe::Absent(_) => return Err(out_of_place(&cursor)),
                },
            }
        }
        match read_translation(&mut cursor) {
            Maybe::Present(written) => translation = Maybe::Present(written),
            Maybe::Absent(written_translation::Absent::Unwritten) => {},
            Maybe::Absent(written_translation::Absent::Misplaced) => {
                return Err(out_of_place(&cursor));
            },
        }
    }
    let mut listed = Vec::new();
    if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
        loop {
            match cursor.tile(TileName::IDENTIFIER) {
                Maybe::Present(name) => listed.push(name),
                Maybe::Absent(_) => match cursor.tile(TileName::TYPE_IDENTIFIER) {
                    Maybe::Present(name) => listed.push(name),
                    Maybe::Absent(_) => break,
                },
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                break;
            }
        }
        if listed.is_empty() {
            return Err(out_of_place(&cursor));
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
            return Err(out_of_place(&cursor));
        }
    }
    if let Maybe::Absent(_) = cursor.tile(TileName::SEMICOLON) {
        return Err(out_of_place(&cursor));
    }
    if let Maybe::Present(_) = cursor.peek() {
        return Err(out_of_place(&cursor));
    }

    Ok(WrittenImport {
        uri,
        alias,
        listed,
        signature,
        translation,
        span: import.span,
        addressed,
        address,
    })
}

quenchant_shape::reason_enum! {
    /// Why a cursor reads no translation.
    pub mod written_translation {
        /// The reason none is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Neither `via` nor `renaming` stands at the cursor.
            Unwritten,
            /// A translation's keyword stands at the cursor, and a tile after
            /// it is out of place.
            Misplaced,
        }
    }
}

/// The translation the tiles at `cursor` spell, `via f` or `renaming { a as
/// b (, a as b)* ,? }`, the cursor past it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`WrittenTranslation::Via`] with the flow's name tile after
///   `via`; [`WrittenTranslation::Renaming`] with each pair's two name tiles,
///   of either case, in written order, after `renaming`;
///   [`written_translation::Absent::Unwritten`], the cursor unmoved, where
///   neither keyword stands; [`written_translation::Absent::Misplaced`], the
///   cursor at the first tile out of place, otherwise.
/// - provides: the reading an import's signature and a site's offer share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an import read via a flow, an import read through a
///   renaming and an offer read through each are read whole.
/// - witness: `gandr-surface-lowering::tests::namespace::an_import_via_a_flow_reads_its_source_through_it_3378`
/// - witness: `gandr-surface-lowering::tests::namespace::an_import_renaming_reads_its_source_s_member_under_the_signature_s_name_3461`
/// - witness: `gandr-surface-lowering::lower::world::tests::an_offer_names_the_translation_it_answers_a_label_through_3461`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(WrittenTranslation::Renaming(ref pairs)) => !pairs.is_empty(),
    | Maybe::Present(WrittenTranslation::Via(_)) | Maybe::Absent(_) => true,
})]
#[inline]
pub fn read_translation(
    cursor: &mut Cursor<'_>
) -> Maybe<WrittenTranslation, written_translation::Absent>
{
    let misplaced = Maybe::Absent(written_translation::Absent::Misplaced);
    if let Maybe::Present(_) = cursor.tile(TileName::VIA) {
        return match cursor.tile(TileName::IDENTIFIER) {
            Maybe::Present(flow) => Maybe::Present(WrittenTranslation::Via(flow)),
            Maybe::Absent(_) => misplaced,
        };
    }
    if let Maybe::Absent(_) = cursor.tile(TileName::RENAMING) {
        return Maybe::Absent(written_translation::Absent::Unwritten);
    }
    if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
        return misplaced;
    }
    let name = |cursor: &mut Cursor<'_>| match cursor.tile(TileName::IDENTIFIER) {
        Maybe::Present(name) => Maybe::Present(name),
        Maybe::Absent(_) => cursor.tile(TileName::TYPE_IDENTIFIER),
    };
    let mut pairs = Vec::new();
    while let Maybe::Present(read) = name(cursor) {
        let (Maybe::Present(_), Maybe::Present(named)) = (cursor.tile(TileName::AS), name(cursor))
        else {
            return misplaced;
        };
        pairs.push((read, named));
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            break;
        }
    }
    if pairs.is_empty() {
        return misplaced;
    }
    match cursor.tile(TileName::BRACE_CLOSE) {
        Maybe::Present(_) => Maybe::Present(WrittenTranslation::Renaming(pairs)),
        Maybe::Absent(_) => misplaced,
    }
}

quenchant_shape::reason_enum! {
    /// Why a cursor reads no quoted string.
    pub mod quoted_text {
        /// The reason none is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No quote stands at the cursor.
            Unopened,
            /// A quote opens a string no quote closes.
            Unclosed,
        }
    }
}

/// The string the quoted tiles at `cursor` spell, `"…"`, its escapes decoded,
/// beside the bytes between its quotes, the cursor past the closing quote.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fragments and escapes between the quotes, in order, decoded
///   as [`decode_escapes`] decodes them, with the bytes the two quotes bound;
///   [`quoted_text::Absent::Unopened`], the cursor unmoved, where no quote
///   stands; [`quoted_text::Absent::Unclosed`] where no quote follows the
///   string's last fragment.
/// - provides: the string reading an import's address and an extern block's
///   language and library share.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an escaped address reads decoded, and an extern block's
///   language and library read as written.
/// - witness: `gandr-surface-lowering::tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `gandr-surface-lowering::lower::capability::tests::an_extern_block_declares_an_interface_its_callers_perform_2901`
/// - witness: `written_import::tests::escape_decoding_covers_continuations_unknowns_and_unicode`
#[spec(ensures: |ref ret| match *ret {
    | Maybe::Present((_, between)) => between.end() <= cursor.here().start(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn quoted(
    tree: &SyntaxTree<'_>,
    cursor: &mut Cursor<'_>,
) -> Maybe<(String, ByteSpan), quoted_text::Absent>
{
    let Maybe::Present(opened) = cursor.tile(TileName::QUOTE)
    else {
        return Maybe::Absent(quoted_text::Absent::Unopened);
    };
    let mut written = String::new();
    loop {
        let piece = match cursor.tile(TileName::STRING_FRAGMENT) {
            Maybe::Present(fragment) => fragment,
            Maybe::Absent(_) => match cursor.tile(TileName::ESCAPE_SEQUENCE) {
                Maybe::Present(escape) => escape,
                Maybe::Absent(_) => break,
            },
        };
        if let Some(text) = tree.fragment(piece.node) {
            written.push_str(text.as_ref());
        }
    }
    let Maybe::Present(closed) = cursor.tile(TileName::QUOTE)
    else {
        return Maybe::Absent(quoted_text::Absent::Unclosed);
    };
    let Ok(between) = ByteSpan::new(opened.span.end(), closed.span.start())
    else {
        return Maybe::Absent(quoted_text::Absent::Unclosed);
    };

    Maybe::Present((
        decode_escapes(SourceFragment::from(written.as_str())),
        between,
    ))
}

/// The file the module path `path` names, relative to the directory of the
/// package's root module: its names joined by `/`, then `.gandr`, so
/// `text.greet` is `text/greet.gandr`.
///
/// # Specification
/// - requires: `path` is names joined by dots, with layout beside a dot.
/// - ensures: each name of `path`, its layout trimmed, in order, joined by `/`
///   and followed by `.gandr`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a one-name and a two-name path, the second written with
///   layout beside its dot, each name their file.
/// - witness: `written_import::tests::a_module_path_names_its_file_2687`
#[spec(ensures: |ret| ret.as_ref().strip_suffix(".gandr").is_some() && ret.as_ref().matches('/').count() == path.as_ref().matches('.').count())]
fn module_file(path: SourceFragment<'_>) -> ImportUri
{
    let mut file = String::new();
    for (index, name) in path.as_ref().split('.').enumerate() {
        if index > 0 {
            file.push('/');
        }
        file.push_str(name.trim());
    }
    file.push_str(".gandr");
    ImportUri::from(file)
}

/// Every import `tree`'s root writes, in source order, read as the collection
/// reads it.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`.
/// - ensures: one entry per import form at the root, in source order; every
///   other root child is passed over.
/// - provides: what a caller reads to lay out a [`Unit`] before lowering it:
///   the sources an import names, without collecting a declaration.
/// - fails: [`LoweringRefusal::MalformedForm`] for a repaired root or an import
///   out of shape, and [`LoweringRefusal::UnknownMold`] for a mold the grammar
///   does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] and [`LoweringRefusal::UnknownMold`].
///
/// # Adequacy
/// - hypothesis: L3 — a source with an unqualified and an aliased import
///   between two declarations lists exactly the two imports.
/// - witness: `gandr-surface-lowering::tests::namespace::an_unqualified_import_binds_no_alias`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.windows(2).all(|pair| match *pair {
    [ref first, ref second] => first.span.start() < second.span.start(),
    _ => false,
})))]
#[inline]
pub fn written_imports<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Result<Vec<WrittenImport>, LoweringRefusal<'source>>
{
    let mut root = Pieces::new();
    read_pieces(pbg, tree, tree.root(), &mut root)?;
    if let Maybe::Present(repaired) = root.repair {
        return Err(repaired.refusal(FormName::ROOT));
    }
    let mut found = Vec::new();
    let mut pieces = Pieces::new();
    for piece in root.pieces {
        let child = piece.placed();
        let Some(node) = tree.node(child.node)
        else {
            continue;
        };
        if let Shape::Form {
            former: Former::Import,
            name,
            ..
        } = shape_of(pbg, node)?
        {
            read_pieces(pbg, tree, child.node, &mut pieces)?;
            found.push(read_import(tree, child, name, &pieces)?);
        }
    }

    Ok(found)
}

/// The sources each source under `roots` imports unqualified, as `unit` lays
/// its path imports out.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`, and `unit` lays out its text.
/// - ensures: for each source written under `roots`, the targets of its
///   unaliased quoted path imports with no list that `unit` resolves to a
///   source; an import that does not read, a scheme address, an unresolved
///   path, a module path and a list add nothing, the collection refusing or
///   binding them as it does. Every source of the unit but its prelude also
///   imports the prelude, which no source writes.
/// - provides: the sources whose `theory` blocks an `include` may name.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source importing one sibling unqualified and another
///   under an alias sees the first alone; a source writing no import sees the
///   prelude's theories.
/// - witness: `gandr-surface-lowering::tests::namespace::an_include_reads_the_theories_its_source_imports_1224`
/// - witness: `gandr-surface-lowering::tests::namespace::the_prelude_answers_a_name_nothing_written_binds_2302`
#[spec(ensures: |ret| ret.values().all(|targets| !targets.is_empty()))]
#[inline]
#[must_use]
pub fn unqualified_imports(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    roots: &[NodeIndex],
    unit: &Unit,
) -> BTreeMap<SourceIndex, BTreeSet<SourceIndex>>
{
    let mut seen: BTreeMap<SourceIndex, BTreeSet<SourceIndex>> = BTreeMap::new();
    let mut ordinals: BTreeMap<SourceIndex, PathImportOrdinal> = BTreeMap::new();
    let mut root = Pieces::new();
    let mut pieces = Pieces::new();
    for &position in roots {
        if read_pieces(pbg, tree, position, &mut root).is_err() {
            continue;
        }
        for piece in &root.pieces {
            let child = piece.placed();
            let Some(node) = tree.node(child.node)
            else {
                continue;
            };
            let Ok(Shape::Form {
                former: Former::Import,
                name,
                ..
            }) = shape_of(pbg, node)
            else {
                continue;
            };
            if read_pieces(pbg, tree, child.node, &mut pieces).is_err() {
                continue;
            }
            let Ok(written) = read_import(tree, child, name, &pieces)
            else {
                continue;
            };
            if written.address == Address::Scheme {
                continue;
            }
            let source = unit.source_at(child.span.start());
            let ordinal = ordinals.entry(source).or_default();
            let target = unit.target(source, *ordinal);
            *ordinal = ordinal.next();
            if let (
                Maybe::Absent(unaliased::Absent::Unqualified),
                ImportTarget::Source(target),
                true,
            ) = (written.alias, target, written.listed.is_empty())
            {
                let _fresh = seen.entry(source).or_default().insert(target);
            }
        }
    }
    if let Some(prelude) = unit.prelude() {
        for source in (0 .. unit.sources().len()).map(SourceIndex::from) {
            if source != prelude {
                let _fresh = seen.entry(source).or_default().insert(prelude);
            }
        }
    }

    seen
}

/// Decode the escapes of a string literal's or an import address's content.
///
/// # Specification
/// - requires: the input is UTF-8 content without its surrounding quote tiles.
/// - ensures: n, t, r and 0 escapes decode to their control characters; escaped
///   LF and CRLF or CR are removed; every other escaped character loses only
///   its backslash.
/// - provides: decoded literal or import-address content, preserving unescaped
///   Unicode.
/// - fails: a trailing backslash contributes no character; unknown escapes are
///   not rejected.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the named escape classes, CR/LF continuations, unknown
///   escapes, Unicode and a trailing backslash have exact decoded values.
/// - witness: `written_import::tests::escape_decoding_covers_continuations_unknowns_and_unicode`
#[spec(
    ensures: |ret| {
        let content: &str = content.as_ref();
        let actual: &str = ret.as_str();
        let mut escaped = false;
        let mut after_cr = false;
        actual.chars().eq(content.chars().filter_map(|character| {
            if after_cr {
                after_cr = false;
                if character == '\n' {
                    return None;
                }
            }
            if escaped {
                escaped = false;
                match character {
                    | 'n' => Some('\n'),
                    | 't' => Some('\t'),
                    | 'r' => Some('\r'),
                    | '0' => Some('\0'),
                    | '\r' => {
                        after_cr = true;
                        None
                    },
                    | '\n' => None,
                    | other => Some(other),
                }
            }
            else if character == '\\' {
                escaped = true;
                None
            }
            else {
                Some(character)
            }
        }))
    },
)]
#[inline]
#[must_use]
pub fn decode_escapes(content: SourceFragment<'_>) -> String
{
    let spelled: &str = content.as_ref();
    let mut decoded = String::with_capacity(spelled.len());
    let mut chars = spelled.chars().peekable();
    while let Some(character) = chars.next() {
        if character != '\\' {
            decoded.push(character);
            continue;
        }
        match chars.next() {
            Some('n') => decoded.push('\n'),
            Some('t') => decoded.push('\t'),
            Some('r') => decoded.push('\r'),
            Some('0') => decoded.push('\0'),
            Some('\r') => {
                if chars.peek() == Some(&'\n') {
                    let _break = chars.next();
                }
            },
            Some('\n') | None => {},
            Some(other) => decoded.push(other),
        }
    }

    decoded
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_surface_syntax::SourceFragment;

    use super::Address;
    use super::ImportUri;
    use super::decode_escapes;
    use super::module_file;

    #[test]
    fn an_address_names_a_scheme_a_coordinate_or_a_path()
    {
        let of = |uri: &str| Address::of(&ImportUri::from(String::from(uri)));
        assert_eq!(
            of("file:///far.gandr"),
            Address::Scheme,
            "a URL names its scheme"
        );
        assert_eq!(of("./circle-base.gandr"), Address::Path, "a relative path");
        assert_eq!(
            of("./a:b.gandr"),
            Address::Path,
            "a colon after a slash opens no scheme"
        );
        assert_eq!(
            of("1file:far.gandr"),
            Address::Path,
            "a scheme opens with a letter"
        );
        assert_eq!(
            of("git+ssh:repo"),
            Address::Scheme,
            "a scheme continues with letters, digits, `+`, `-` and `.`"
        );
        assert_eq!(
            of("path:../hello"),
            Address::Coordinate,
            "the `path` scheme names a package's coordinate"
        );
        assert_eq!(
            of("gh:acme-org/rope"),
            Address::Coordinate,
            "the `gh` scheme names a package's coordinate"
        );
        assert_eq!(
            of("paths:../hello"),
            Address::Scheme,
            "a longer scheme is no coordinate"
        );
    }

    /// #2687: a module path names its file by its names joined by `/`, the
    /// layout beside a dot dropped, then `.gandr`.
    #[test]
    fn a_module_path_names_its_file_2687()
    {
        let file = |path: &str| String::from(module_file(SourceFragment::from(path)).as_ref());
        assert_eq!(file("greet"), "greet.gandr", "one name is its file");
        assert_eq!(
            file("text . greet"),
            "text/greet.gandr",
            "two names are a directory and its file"
        );
    }

    /// Escape classes and continuations preserve their specified characters.
    #[test]
    fn escape_decoding_covers_continuations_unknowns_and_unicode()
    {
        for (written, expected) in [
            ("plain λ", "plain λ"),
            ("\\n\\t\\r\\0", "\n\t\r\0"),
            ("a\\\nb", "ab"),
            ("a\\\r\nb", "ab"),
            ("a\\\rb", "ab"),
            ("a\\q\\λ", "aqλ"),
            ("a\\", "a"),
            ("a\r\nb", "a\r\nb"),
            ("\\\\", "\\"),
            ("\\\r\\n", "\n"),
        ] {
            assert_eq!(decode_escapes(SourceFragment::from(written)), expected);
        }
    }
}
