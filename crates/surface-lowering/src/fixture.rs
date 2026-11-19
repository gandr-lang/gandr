//! Test fixtures: the units the lowering's own tests lower, over the base
//! crate's fixtures.
//!
//! The base crate's `fixture` module holds the parsed and hand-built trees,
//! the synthetic positions, origins and spans, and the attribute registry's
//! entries. This module names them for the tests here, and adds the units a
//! source lowers in: a stand-in for the `std` modules it lists, and one for
//! the host modules it imports.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_surface_grammar::Pbg;
pub use gandr_surface_lowering_base::fixture::Handmade;
pub use gandr_surface_lowering_base::fixture::Rule;
pub use gandr_surface_lowering_base::fixture::Spelled;
pub use gandr_surface_lowering_base::fixture::grammar;
pub use gandr_surface_lowering_base::fixture::node;
pub use gandr_surface_lowering_base::fixture::parsed;
pub use gandr_surface_lowering_base::fixture::registered;
pub use gandr_surface_lowering_base::fixture::repaired;
pub use gandr_surface_lowering_base::fixture::span;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::budget::LoweringBudget;
use crate::coincide::Decisions;
use crate::lower::lower_unit;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitSource;

/// The line a source writes to list `List` from its home (#4520).
pub const LISTING: &str = "import std.list (List) ;\n";

/// `source` after [`LISTING`] and a newline that stands in for `std.list`,
/// which declares nothing: the text [`listed`] lowers.
///
/// # Specification
/// trivial.
pub fn listing<Source>(source: Source) -> String
where
    Source: core::fmt::Display,
{
    format!("\n{LISTING}{source}")
}

/// The line a source writes to list the session formers from their home
/// (#4521).
pub const SESSION_LISTING: &str = "import std.session (Run, Prefix, Dialogue) ;\n";

/// `source` after [`SESSION_LISTING`] and a newline that stands in for
/// `std.session`, which declares nothing: the text [`listed`] lowers.
///
/// # Specification
/// trivial.
pub fn session_listing<Source>(source: Source) -> String
where
    Source: core::fmt::Display,
{
    format!("\n{SESSION_LISTING}{source}")
}

/// `text`, which [`listing`] or [`session_listing`] made, lowered as a unit
/// of two sources: the stand-in for the `std` modules and the source listing
/// their formers.
///
/// # Specification
/// - requires: `text` is what [`listing`] or [`session_listing`] made and
///   parses cleanly.
/// - ensures: the second source's path imports, at most two, resolve to the
///   first.
/// - provides: a source that names a homed former lowered where it resolves.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the unit.
///
/// # Adequacy
/// - hypothesis: L3 — every witness naming `List` or a session former reads its
///   module through here, and a source that does not list it refuses the type
///   head.
/// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
/// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
#[spec(requires: text.as_ref().starts_with('\n'))]
pub fn listed<'source, Text>(
    text: &'source Text,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
where
    Text: AsRef<str> + ?Sized,
{
    let pbg = grammar();
    let tree = parsed(&pbg, SourceText::from(text.as_ref()));
    let stand_in = ImportTarget::Source(SourceIndex::from(0_usize));
    let unit = Unit::new(Vec::from([
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(ByteOffset::from(1_usize), Vec::from([stand_in, stand_in])),
    ]))
    .expect("the listing imports the source before it");
    lower_unit(
        &pbg,
        &tree,
        &unit,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the listed unit lowers")
}

/// The lines a source writes to import the module of every host interface
/// (#4523): it names any of them through these.
pub const HOSTING: &str =
    "import std.env ;\nimport std.fs ;\nimport std.io ;\nimport std.net ;\nimport std.process ;\n";

/// A newline that stands in for the host modules, then `source` and
/// [`HOSTING`] after it: the text [`hosted`] lowers. The imports trail the
/// source, so its spans stand one byte on.
///
/// # Specification
/// trivial.
pub fn hosting<Source>(source: Source) -> String
where
    Source: core::fmt::Display,
{
    format!("\n{source}{HOSTING}")
}

/// `text`, which [`hosting`] made, lowered as a unit of two sources: the
/// stand-in for the host modules and the source importing each of them.
///
/// # Specification
/// - requires: `text` is what [`hosting`] made and parses cleanly.
/// - ensures: as [`imported`] over [`HOSTING`]'s imports.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the unit.
///
/// # Adequacy
/// - hypothesis: L3 — every witness naming a host interface reads its module
///   through here.
/// - witness: `lower::capability::tests::a_host_interface_answers_only_where_its_module_is_imported_4523`
#[spec(requires: text.as_ref().starts_with('\n') && text.as_ref().ends_with(HOSTING))]
pub fn hosted<'source, Text>(
    text: &'source Text,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
where
    Text: AsRef<str> + ?Sized,
{
    imported(text, arena)
}

/// `text` lowered as a unit of two sources: a newline that stands in for
/// every module the second imports, then the second, whose path imports,
/// each a line opening `import `, resolve to the first.
///
/// # Specification
/// - requires: `text` opens with the stand-in's newline, parses cleanly and
///   writes each path import on a line of its own.
/// - ensures: each of the second source's path imports resolves to the first.
/// - provides: a source whose imports resolve, lowered where they do.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the unit.
///
/// # Adequacy
/// - hypothesis: L3 — a source importing the console's module reaches it, and
///   one importing another module does not.
/// - witness: `lower::capability::tests::a_host_interface_answers_only_where_its_module_is_imported_4523`
#[spec(requires: text.as_ref().starts_with('\n'))]
pub fn imported<'source, Text>(
    text: &'source Text,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
where
    Text: AsRef<str> + ?Sized,
{
    let pbg = grammar();
    let tree = parsed(&pbg, SourceText::from(text.as_ref()));
    importing(&pbg, &tree, arena)
}

/// `text`, which [`hosting`] made from a source the parser must repair,
/// lowered as [`hosted`] lowers a clean one.
///
/// # Specification
/// - requires: `text` is what [`hosting`] made, and the parser repairs it.
/// - ensures: as [`hosted`], over the repaired tree.
/// - fails: never on accepted fixtures.
/// - panics: if the parser reads the text without a repair, or if the lowering
///   refuses the unit.
///
/// # Adequacy
/// - hypothesis: L3 — a host scope that a doubled `}` closes early reads its
///   interface through here.
/// - witness: `lower::capability::tests::a_doubled_closer_before_a_scope_s_clauses_is_refused_there_5302`
#[spec(requires: text.as_ref().starts_with('\n') && text.as_ref().ends_with(HOSTING))]
pub fn hosted_repaired<'source, Text>(
    text: &'source Text,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
where
    Text: AsRef<str> + ?Sized,
{
    let pbg = grammar();
    let tree = repaired(&pbg, SourceText::from(text.as_ref()));
    importing(&pbg, &tree, arena)
}

/// `tree` lowered as a unit of two sources, as [`imported`] states.
///
/// # Specification
/// trivial.
fn importing<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
{
    let imports = <&str>::from(tree.source())
        .lines()
        .filter(|line| line.starts_with("import "))
        .count();
    let unit = Unit::new(Vec::from([
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(
            ByteOffset::from(1_usize),
            alloc::vec![ImportTarget::Source(SourceIndex::from(0_usize)); imports],
        ),
    ]))
    .expect("the importing source imports the source before it");
    lower_unit(
        pbg,
        tree,
        &unit,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the imported unit lowers")
}
