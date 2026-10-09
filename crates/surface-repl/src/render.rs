//! The interim type renderer: a type's content table spelled as the surface
//! writes it.
//!
//! The incremental checker hands a checked item's signature and a synthesised
//! item's type back as [`ContentNode`] tables. [`spell`] writes such a table in
//! the fragment's type syntax — `Integer`, `String`, `Unit`, `U C`, `F A`,
//! `A -> C` — and marks the spelling approximate wherever a node has no surface
//! spelling yet, writing `?` for it. The renderer gives way to the layout
//! printer when that lands; until then it is the one spelling every transcript
//! line names a type by.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_incremental::ContentNode;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Sort;
use gandr_kernel_term::BaseType;

/// How many nodes one spelling visits before the renderer stops.
///
/// A content table is acyclic and a type of the fragment is a handful of
/// nodes, so the bound is reached only by a malformed table, whose spelling is
/// then `?` rather than a loop that does not end.
const SPELL_BUDGET: usize = 4_096;

/// Whether a spelling says exactly the type its table holds.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Fidelity
{
    /// Every node was spelled as the surface writes it.
    Faithful,
    /// Some node has no surface spelling yet and was written `?`.
    Approximate,
}

/// A type written in the surface's syntax.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Spelling
{
    /// The written type.
    text: String,
    /// Whether the text says exactly the type.
    fidelity: Fidelity,
}

impl Spelling
{
    /// The spelling of a node the surface cannot write.
    ///
    /// # Specification
    /// trivial.
    fn unknown() -> Self
    {
        Self {
            text: String::from("?"),
            fidelity: Fidelity::Approximate,
        }
    }

    /// Whether the text says exactly the type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fidelity(&self) -> Fidelity
    {
        self.fidelity
    }
}

impl AsRef<str> for Spelling
{
    /// The written type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.text
    }
}

impl fmt::Display for Spelling
{
    /// Writes the type as the surface spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.text)
    }
}

/// The polarity a type position requires.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Polarity
{
    /// A value type: the root of a signature, a thunk's body's opposite.
    Value,
    /// A computation type.
    Computation,
}

/// What a position admits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admits
{
    /// A type of either polarity: the root.
    Either,
    /// A type of this polarity only.
    Only(Polarity),
}

/// How a spelled piece binds, for the parentheses its context needs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// A name or `?`, which never needs parentheses.
    Atom,
    /// A former applied to its argument, `U C` or `F A`.
    Application,
    /// An arrow, `A -> C`.
    Arrow,
}

/// One spelled subterm.
#[derive(Clone, Debug)]
struct Piece
{
    /// Its text.
    text: String,
    /// How it binds.
    binding: Binding,
}

impl Piece
{
    /// An atom spelled `text`.
    ///
    /// # Specification
    /// trivial.
    const fn atom(text: String) -> Self
    {
        Self {
            text,
            binding: Binding::Atom,
        }
    }

    /// The text, parenthesized unless it is an atom: the argument of a former.
    ///
    /// # Specification
    /// trivial.
    fn as_argument(&self) -> String
    {
        match self.binding {
            | Binding::Atom => self.text.clone(),
            | Binding::Application | Binding::Arrow => format!("({})", self.text),
        }
    }

    /// The text, parenthesized when it is an arrow: the domain of an arrow.
    ///
    /// # Specification
    /// trivial.
    fn as_domain(&self) -> String
    {
        match self.binding {
            | Binding::Atom | Binding::Application => self.text.clone(),
            | Binding::Arrow => format!("({})", self.text),
        }
    }
}

/// One unit of the renderer's pending work.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Spell the node at the index, in a position admitting the polarity.
    Spell(NodeIndex, Admits),
    /// Wrap the last piece as `U` of it.
    Thunk,
    /// Wrap the last piece as `F` of it.
    Returner,
    /// Join the last two pieces as an arrow from the first to the second.
    Arrow,
}

/// What a content node is, as far as a type position cares.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A type of this polarity.
    Type(Polarity),
    /// A term, which no type position admits.
    Term,
}

/// What one node of the walk answers.
#[derive(Clone, Debug)]
enum Expanded
{
    /// A piece spelled at once.
    Spelled(Piece),
    /// A node the surface cannot write yet.
    Unknown,
    /// A former whose join waits on its children's spells, now pushed.
    Deferred,
}

/// What `node` is, as far as a type position cares.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the value-type formers answer a value type, the computation-type
///   formers a computation type, an unresolved node the polarity of its sort,
///   and every term former, or an unresolved term, a term.
/// - provides: the check that a former's argument is of the polarity the former
///   takes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a former over an argument of the wrong polarity, and a
///   term at the root, each spell approximately.
/// - witness: `render::tests::ty_dispatches_on_polarity`
const fn kind(node: &ContentNode) -> Kind
{
    match *node {
        | ContentNode::Base(_)
        | ContentNode::UnitType
        | ContentNode::Product(..)
        | ContentNode::Sum(..)
        | ContentNode::ThunkType(_)
        | ContentNode::Universe { .. }
        | ContentNode::TypeLift { .. }
        | ContentNode::Element { .. }
        | ContentNode::Abstract(_)
        | ContentNode::Unresolved(Sort::ValueType) => Kind::Type(Polarity::Value),
        | ContentNode::Returner(_)
        | ContentNode::Arrow { .. }
        | ContentNode::Pi { .. }
        | ContentNode::ComputationElement { .. }
        | ContentNode::Unresolved(Sort::CompType) => Kind::Type(Polarity::Computation),
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Pair(..)
        | ContentNode::Injection(..)
        | ContentNode::Thunk(_)
        | ContentNode::ValueLift { .. }
        | ContentNode::Quote(_)
        | ContentNode::QuoteComputation(_)
        | ContentNode::Lambda(_)
        | ContentNode::Application(..)
        | ContentNode::Return(_)
        | ContentNode::Bind(..)
        | ContentNode::Force(_)
        | ContentNode::Case { .. }
        | ContentNode::Unresolved(Sort::Value | Sort::Computation) => Kind::Term,
    }
}

/// Whether a position admitting `admits` takes a node of `kind`.
///
/// # Specification
/// trivial.
const fn admitted(
    admits: Admits,
    kind: Kind,
) -> Admission
{
    match (admits, kind) {
        | (Admits::Either, Kind::Type(_)) => Admission::Admitted,
        | (Admits::Only(wanted), Kind::Type(found))
            if matches!(
                (wanted, found),
                (Polarity::Value, Polarity::Value) | (Polarity::Computation, Polarity::Computation)
            ) =>
        {
            Admission::Admitted
        },
        | (Admits::Either | Admits::Only(_), Kind::Type(_) | Kind::Term) => Admission::Misplaced,
    }
}

/// Whether a node fits the position it sits in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admission
{
    /// A type of the polarity the position takes.
    Admitted,
    /// A term, or a type of the other polarity.
    Misplaced,
}

/// The type at `root` of `nodes`, written in the surface's syntax.
///
/// # Specification
/// - requires: nothing; any table and index are admissible.
/// - ensures: `Integer`, `String` and `Unit` for the base and unit types; `+U
///   C` and `-F A` for the thunk and returner formers, their argument
///   parenthesized unless it is an atom; `A -> C` for an arrow, right
///   associative, its domain parenthesized only when it is itself an arrow; an
///   abstract type by its name. Every node the surface cannot write yet — the
///   numeric atom, products, sums, universes, lifts, elements, dependent
///   arrows, unresolved nodes, a term, an index past the table, and a former
///   over an argument of the wrong polarity — is written `?`, and the spelling
///   is then [`Fidelity::Approximate`]; otherwise it is [`Fidelity::Faithful`].
///   A table that would take more than a fixed visit budget, which only a
///   malformed one does, spells `?`.
/// - provides: the one spelling a transcript line names a type by; read back as
///   a signature, a faithful spelling lowers to the type it was spelled from.
/// - fails: never.
/// - panics: none.
/// - intension: one walk over an explicit work stack, never recursion; linear
///   in the spelled tree.
///
/// # Adequacy
/// - hypothesis: L3 — every value-type and computation-type former of the
///   fragment, nested, is asserted at its exact spelling; a former over the
///   wrong polarity, an unsupported node, a dangling index and a cycle are each
///   asserted approximate; L2 — the type of every declaration of the strict
///   corpus spells as its source wrote it.
/// - witness: `render::tests::value_ty_covers_every_reachable_former`
/// - witness: `render::tests::comp_ty_covers_every_reachable_former`
/// - witness: `render::tests::ty_dispatches_on_polarity`
/// - witness: `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
/// - witness: `render::tests::types_render_without_debug`
/// - witness: `render::tests::a_malformed_table_spells_unknown`
/// - witness: `loop::tests::corpus_types_spell_as_their_source_writes_them`
#[inline]
#[must_use]
pub fn spell(
    nodes: &[ContentNode],
    root: NodeIndex,
) -> Spelling
{
    let mut fidelity = Fidelity::Faithful;
    let mut tasks = Vec::from([Task::Spell(root, Admits::Either)]);
    let mut pieces: Vec<Piece> = Vec::new();
    let mut visits = 0_usize;
    while let Some(task) = tasks.pop() {
        match task {
            | Task::Spell(index, admits) => {
                visits = visits.saturating_add(1);
                if visits > SPELL_BUDGET {
                    return Spelling::unknown();
                }
                let expanded = match nodes.get(usize::from(index)) {
                    | Some(node) => match admitted(admits, kind(node)) {
                        | Admission::Admitted => expand(node, &mut tasks),
                        | Admission::Misplaced => Expanded::Unknown,
                    },
                    | None => Expanded::Unknown,
                };
                match expanded {
                    | Expanded::Spelled(piece) => pieces.push(piece),
                    | Expanded::Unknown => {
                        fidelity = Fidelity::Approximate;
                        pieces.push(Piece::atom(String::from("?")));
                    },
                    | Expanded::Deferred => {},
                }
            },
            | Task::Thunk | Task::Returner => {
                let Some(argument) = pieces.pop()
                else {
                    return Spelling::unknown();
                };
                let former = if matches!(task, Task::Thunk) {
                    "+U"
                }
                else {
                    "-F"
                };
                pieces.push(Piece {
                    text: format!("{former} {}", argument.as_argument()),
                    binding: Binding::Application,
                });
            },
            | Task::Arrow => {
                let (Some(codomain), Some(domain)) = (pieces.pop(), pieces.pop())
                else {
                    return Spelling::unknown();
                };
                pieces.push(Piece {
                    text: format!("{} -> {}", domain.as_domain(), codomain.text),
                    binding: Binding::Arrow,
                });
            },
        }
    }
    match (pieces.pop(), pieces.is_empty()) {
        | (Some(piece), true) => Spelling {
            text: piece.text,
            fidelity,
        },
        | (Some(_) | None, false) | (None, true) => Spelling::unknown(),
    }
}

/// The piece `node` spells at once, or the work its children need.
///
/// # Specification
/// - requires: `node` is a type, of the polarity its position admits.
/// - ensures: an atom for a base type the surface names, the unit type, and an
///   abstract type with a textual name; [`Expanded::Unknown`] for every other
///   leaf the surface cannot write; for `+U`, `-F` and an arrow, pushes the
///   former's join below its children's spells, each child admitting the
///   polarity its former takes, and answers [`Expanded::Deferred`].
/// - provides: one step of [`spell`]'s walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — through [`spell`]'s witnesses, which assert every arm at
///   its exact spelling.
/// - witness: `render::tests::value_ty_covers_every_reachable_former`
/// - witness: `render::tests::comp_ty_covers_every_reachable_former`
/// - witness: `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`
fn expand(
    node: &ContentNode,
    tasks: &mut Vec<Task>,
) -> Expanded
{
    match *node {
        | ContentNode::Base(BaseType::Integer) => {
            Expanded::Spelled(Piece::atom(String::from("Integer")))
        },
        | ContentNode::Base(BaseType::String) => {
            Expanded::Spelled(Piece::atom(String::from("String")))
        },
        | ContentNode::UnitType => Expanded::Spelled(Piece::atom(String::from("Unit"))),
        | ContentNode::Abstract(Reference::Item { ref key, .. }) => {
            match core::str::from_utf8(key.as_ref()) {
                | Ok(name) => Expanded::Spelled(Piece::atom(String::from(name))),
                | Err(_) => Expanded::Unknown,
            }
        },
        | ContentNode::ThunkType(body) => {
            tasks.push(Task::Thunk);
            tasks.push(Task::Spell(body, Admits::Only(Polarity::Computation)));
            Expanded::Deferred
        },
        | ContentNode::Returner(inner) => {
            tasks.push(Task::Returner);
            tasks.push(Task::Spell(inner, Admits::Only(Polarity::Value)));
            Expanded::Deferred
        },
        | ContentNode::Arrow { domain, codomain } => {
            tasks.push(Task::Arrow);
            tasks.push(Task::Spell(codomain, Admits::Only(Polarity::Computation)));
            tasks.push(Task::Spell(domain, Admits::Only(Polarity::Value)));
            Expanded::Deferred
        },
        | ContentNode::Base(BaseType::Numeric)
        | ContentNode::Abstract(Reference::Unoccupied)
        | ContentNode::Product(..)
        | ContentNode::Sum(..)
        | ContentNode::Universe { .. }
        | ContentNode::TypeLift { .. }
        | ContentNode::Element { .. }
        | ContentNode::Pi { .. }
        | ContentNode::ComputationElement { .. }
        | ContentNode::Unresolved(_)
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Pair(..)
        | ContentNode::Injection(..)
        | ContentNode::Thunk(_)
        | ContentNode::ValueLift { .. }
        | ContentNode::Quote(_)
        | ContentNode::QuoteComputation(_)
        | ContentNode::Lambda(_)
        | ContentNode::Application(..)
        | ContentNode::Return(_)
        | ContentNode::Bind(..)
        | ContentNode::Force(_)
        | ContentNode::Case { .. } => Expanded::Unknown,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::ItemKey;
    use gandr_core_incremental::NodeIndex;
    use gandr_core_incremental::Occurrence;
    use gandr_core_incremental::Reference;
    use gandr_core_incremental::Sort;
    use gandr_kernel_term::BaseType;

    use super::Fidelity;
    use super::spell;

    /// The first eight node indices.
    ///
    /// # Specification
    /// trivial.
    fn indices() -> [NodeIndex; 8]
    {
        [0, 1, 2, 3, 4, 5, 6, 7].map(NodeIndex::from)
    }

    /// The abstract type keyed `key`.
    ///
    /// # Specification
    /// trivial.
    fn named(key: ItemKey) -> ContentNode
    {
        ContentNode::Abstract(Reference::Item {
            key,
            occurrence: Occurrence::from(0),
        })
    }

    /// The text and fidelity of the table's spelling from its first node.
    ///
    /// # Specification
    /// trivial.
    fn spelled(nodes: &[ContentNode]) -> (String, Fidelity)
    {
        let spelling = spell(nodes, NodeIndex::from(0));
        (spelling.to_string(), spelling.fidelity())
    }

    /// The faithful spelling `text`.
    ///
    /// # Specification
    /// trivial.
    fn faithful(text: String) -> (String, Fidelity)
    {
        (text, Fidelity::Faithful)
    }

    /// The approximate spelling `text`.
    ///
    /// # Specification
    /// trivial.
    fn approximate(text: String) -> (String, Fidelity)
    {
        (text, Fidelity::Approximate)
    }

    /// Every value type the fragment writes spells exactly, nested formers
    /// parenthesized.
    #[test]
    fn value_ty_covers_every_reachable_former()
    {
        let [_, n1, n2, n3, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(core::slice::from_ref(&integer)),
            faithful("Integer".into())
        );
        assert_eq!(
            spelled(&[ContentNode::Base(BaseType::String)]),
            faithful("String".into())
        );
        assert_eq!(spelled(&[ContentNode::UnitType]), faithful("Unit".into()));
        assert_eq!(
            spelled(&[named(ItemKey::from("Shape"))]),
            faithful("Shape".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Returner(n2),
                integer.clone(),
            ]),
            faithful("+U (-F Integer)".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Arrow {
                    domain: n2,
                    codomain: n3,
                },
                integer,
                ContentNode::Returner(n2),
            ]),
            faithful("+U (Integer -> -F Integer)".into())
        );
    }

    /// Every computation type the fragment writes spells exactly: the arrow
    /// right associative, a thunk domain bare, a returner's thunk argument
    /// parenthesized.
    #[test]
    fn comp_ty_covers_every_reachable_former()
    {
        let [_, n1, n2, n3, n4, n5, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(&[ContentNode::Returner(n1), integer.clone()]),
            faithful("-F Integer".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Returner(n1),
                ContentNode::ThunkType(n2),
                ContentNode::Returner(n3),
                ContentNode::UnitType,
            ]),
            faithful("-F (+U (-F Unit))".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n2,
                },
                integer.clone(),
                ContentNode::Arrow {
                    domain: n3,
                    codomain: n4,
                },
                ContentNode::Base(BaseType::String),
                ContentNode::Returner(n5),
                ContentNode::UnitType,
            ]),
            faithful("Integer -> String -> -F Unit".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n3,
                },
                ContentNode::ThunkType(n3),
                integer,
                ContentNode::Returner(n2),
            ]),
            faithful("+U (-F Integer) -> -F Integer".into())
        );
    }

    /// A former reads its argument at the polarity it takes: `+U` over a value
    /// type, `-F` over a computation type, an arrow from a computation type,
    /// and a term at the root each spell approximately, at exactly the
    /// misplaced node.
    #[test]
    fn ty_dispatches_on_polarity()
    {
        let [_, n1, n2, ..] = indices();
        let integer = ContentNode::Base(BaseType::Integer);
        assert_eq!(
            spelled(&[ContentNode::ThunkType(n1), integer.clone()]),
            approximate("+U ?".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Returner(n1),
                ContentNode::Returner(n2),
                integer.clone(),
            ]),
            approximate("-F ?".into())
        );
        assert_eq!(
            spelled(&[
                ContentNode::Arrow {
                    domain: n1,
                    codomain: n1,
                },
                ContentNode::Returner(n2),
                integer,
            ]),
            approximate("? -> -F Integer".into())
        );
        assert_eq!(spelled(&[ContentNode::Unit]), approximate("?".into()));
    }

    /// Fidelity follows the nodes the surface cannot write, not the characters
    /// a name happens to hold: a name spelled with `?` stays faithful, while a
    /// product, the numeric atom and an unresolved type are each approximate.
    #[test]
    fn fidelity_tracks_unsupported_nodes_not_user_punctuation()
    {
        let [_, n1, n2, ..] = indices();
        assert_eq!(
            spelled(&[named(ItemKey::from("Maybe?"))]),
            faithful("Maybe?".into())
        );
        let integer = ContentNode::Base(BaseType::Integer);
        for unsupported in [
            ContentNode::Product(n1, n1),
            ContentNode::Base(BaseType::Numeric),
            ContentNode::Unresolved(Sort::ValueType),
        ] {
            assert_eq!(
                spelled(&[unsupported.clone(), integer.clone()]),
                approximate("?".into()),
                "{unsupported:?} has no surface spelling"
            );
        }
        assert_eq!(
            spelled(&[
                ContentNode::ThunkType(n1),
                ContentNode::Returner(n2),
                ContentNode::Base(BaseType::Numeric),
            ]),
            approximate("+U (-F ?)".into())
        );
    }

    /// A spelling displays as the surface text, never as the table's debug
    /// image, and its text view agrees with its display.
    #[test]
    fn types_render_without_debug()
    {
        let [n0, n1, n2, n3, n4, ..] = indices();
        let nodes = [
            ContentNode::ThunkType(n1),
            ContentNode::Arrow {
                domain: n2,
                codomain: n3,
            },
            ContentNode::Base(BaseType::String),
            ContentNode::Returner(n4),
            ContentNode::UnitType,
        ];
        let spelling = spell(&nodes, n0);
        assert_eq!(spelling.to_string(), "+U (String -> -F Unit)");
        assert_eq!(AsRef::<str>::as_ref(&spelling), "+U (String -> -F Unit)");
        let debug = format!("{nodes:?}");
        assert!(
            debug.contains("ThunkType") && !spelling.to_string().contains("ThunkType"),
            "the display is not the debug image: {debug}"
        );
    }

    /// A dangling index, an empty table and a cycle each spell approximately
    /// rather than panicking or looping.
    #[test]
    fn a_malformed_table_spells_unknown()
    {
        let [n0, n1, .., n7] = indices();
        assert_eq!(
            spelled(&[ContentNode::ThunkType(n7)]),
            approximate("+U ?".into())
        );
        assert_eq!(spelled(&[]), approximate("?".into()));
        let cycle: Vec<ContentNode> = Vec::from([ContentNode::ThunkType(n1), ContentNode::Arrow {
            domain: n0,
            codomain: n1,
        }]);
        assert_eq!(spelled(&cycle), approximate("?".into()));
    }
}
