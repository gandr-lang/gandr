//! The type the latest resume gives a declaration, spelled at a page width.
//!
//! # A declaration's type and documentation are read off the latest revision
//!
//! **Choice.** `type_of` spells the type the latest resume gives the last item
//! of a name, the lookup a transcript makes; `type_at` spells the type of the
//! item a `Reference` names, key and occurrence, the lookup a hover makes over
//! one of several declarations of a name. Both read the item's checkpoint: a
//! checked or owed value by its signature, a synthesised value by its produced
//! type, a native declaration by its universe, each laid out through the
//! printer's `ContentSource` at the caller's page width, and an absence names
//! why — no resume, no such item, a refused item, an unsigned one, a refused
//! layout. `Session::documentation` answers the documentation text the latest
//! accepted lowering filed under a declaring form's content identity, which
//! documentation does not reach, so an edit to the documentation alone keeps
//! the key; a revision refused whole keeps the accepted one's, as the import
//! scope does. The session keeps the text owned, so it outlives the revision it
//! was read from.
//!
//! **Alternatives.** The lookup lived in the REPL's encoder, the one face that
//! spelled a checkpoint's type; a second face, the language server's hover,
//! would otherwise copy it and the two could spell one type differently.
//! Documentation could be read again from the face's own parse, at the cost of
//! a second reading of `///` lines and `doc("…")` entries that could disagree
//! with the lowering's.
//!
//! **Reversal.** A face that needs the type of a node inside a body, not a
//! whole item, needs a per-node typing the resume does not keep; documentation
//! that must survive a revision refused at the declaration, not whole, needs
//! the lowering to file it for refused forms too.

use anodized::spec;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::DeclarationRoots;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Resume;
use gandr_core_incremental::Typing;
use gandr_core_incremental::submitted;
use gandr_surface_pretty::ContentSource;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a declaration's type cannot be spelled.
    pub mod spelled {
        /// The reason no type is spelled.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The session holds no resume to read checkpoints from.
            Unresumed,
            /// No checkpoint of the latest resume carries the declaration's
            /// name.
            Uncheckpointed,
            /// The checker refused the item, so it has no type.
            Refused,
            /// The item states no signature and synthesised none.
            Unsigned,
            /// The printer reached a layout ceiling laying the type out.
            Unpresentable,
        }
    }
}

/// The type of the last declaration named `name` in `resume`, laid out at
/// `page`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the last checkpoint whose item key is `name`'s bytes answers, as
///   [`spelled_type`] spells it.
/// - provides: the type a transcript line names a declaration by: the latest of
///   its name, which a later line shadows an earlier one with.
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — no resume, an absent name and a refused checkpoint retain
///   distinct absence reasons, while a stated signature and a synthesised type
///   are each spelled.
/// - witness: `typed::tests::missing_and_refused_types_keep_their_absence_reasons`
/// - witness: `typed::tests::a_synthesised_type_is_spelled`
#[spec(ensures: |ret| match resume {
    Maybe::Absent(_) => matches!(ret, Maybe::Absent(spelled::Absent::Unresumed)),
    Maybe::Present(resume) => resume.checkpoints().items().iter().any(|checkpoint|
        matches!(checkpoint.content().reference(), Reference::Item { key, .. }
            if key.as_ref() == AsRef::<str>::as_ref(&name).as_bytes()))
        != matches!(ret, Maybe::Absent(spelled::Absent::Uncheckpointed)),
})]
#[inline]
pub fn type_of(
    resume: Maybe<&Resume, submitted::Absent>,
    name: SourceFragment<'_>,
    page: PageWidth,
) -> Maybe<Presentation, spelled::Absent>
{
    let Maybe::Present(resume) = resume
    else {
        return Maybe::Absent(spelled::Absent::Unresumed);
    };
    let wanted = AsRef::<str>::as_ref(&name).as_bytes();
    let named = |checkpoint: &&ItemCheckpoint| {
        matches!(
            checkpoint.content().reference(),
            Reference::Item { key, .. } if key.as_ref() == wanted
        )
    };
    resume.checkpoints().items().iter().rfind(named).map_or(
        Maybe::Absent(spelled::Absent::Uncheckpointed),
        |checkpoint| spelled_type(checkpoint, page),
    )
}

/// The type of the item `reference` names in `resume`, laid out at `page`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the checkpoint whose reference is `reference` answers, as
///   [`spelled_type`] spells it.
/// - provides: the type a hover names one declaration by, among several of one
///   name: the occurrence of its key it is.
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two members of one name in two modules are each spelled
///   by their own occurrence, and an occurrence past them is absent.
/// - witness: `typed::tests::each_occurrence_of_a_name_has_its_own_type`
#[spec(ensures: |ret| match resume {
    Maybe::Absent(_) => matches!(ret, Maybe::Absent(spelled::Absent::Unresumed)),
    Maybe::Present(resume) => resume.checkpoints().items().iter()
        .any(|checkpoint| checkpoint.content().reference() == reference)
        != matches!(ret, Maybe::Absent(spelled::Absent::Uncheckpointed)),
})]
#[inline]
pub fn type_at(
    resume: Maybe<&Resume, submitted::Absent>,
    reference: &Reference,
    page: PageWidth,
) -> Maybe<Presentation, spelled::Absent>
{
    let Maybe::Present(resume) = resume
    else {
        return Maybe::Absent(spelled::Absent::Unresumed);
    };
    resume
        .checkpoints()
        .items()
        .iter()
        .find(|checkpoint| checkpoint.content().reference() == reference)
        .map_or(
            Maybe::Absent(spelled::Absent::Uncheckpointed),
            |checkpoint| spelled_type(checkpoint, page),
        )
}

/// The type `checkpoint` gives its item, laid out at `page`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a checked or owed value by its signature, a synthesised value by
///   its produced classifier, and a native declaration by its declared
///   universe, each laid out through [`present_type`] over a [`ContentSource`];
///   a refused item, an unsigned owed or checked one, and a refused layout are
///   each absences naming their reason.
/// - provides: the one spelling both lookups share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refused checkpoint, a stated signature and a
///   synthesised type are each asserted at their exact answer. The predicate
///   checks precedence without printing twice.
/// - witness: `typed::tests::missing_and_refused_types_keep_their_absence_reasons`
/// - witness: `typed::tests::a_synthesised_type_is_spelled`
#[spec(ensures: |ret| match *checkpoint.typing() {
    Typing::Refused(_) => matches!(ret, Maybe::Absent(spelled::Absent::Refused)),
    Typing::Checked { .. } | Typing::Owed
        if matches!(checkpoint.content().declaration(), DeclarationRoots::Value {signature:Maybe::Absent(_),..}) =>
        matches!(ret, Maybe::Absent(spelled::Absent::Unsigned)),
    Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Synthesised { .. } =>
        matches!(ret, Maybe::Present(_) | Maybe::Absent(spelled::Absent::Unpresentable)),
})]
fn spelled_type(
    checkpoint: &ItemCheckpoint,
    page: PageWidth,
) -> Maybe<Presentation, spelled::Absent>
{
    let content = checkpoint.content();
    let laid_out = |nodes: &[ContentNode], root: NodeIndex| {
        present_type(&ContentSource::from(nodes), root, page).map_or(
            Maybe::Absent(spelled::Absent::Unpresentable),
            Maybe::Present,
        )
    };
    match *checkpoint.typing() {
        | Typing::Data => match *(content.declaration()) {
            | DeclarationRoots::Data(ref roots) => laid_out(content.nodes(), roots.kind),
            | DeclarationRoots::Value { .. } => Maybe::Absent(spelled::Absent::Unpresentable),
        },
        | Typing::Checked { .. } | Typing::Owed => match *(content.declaration()) {
            | DeclarationRoots::Value {
                signature: Maybe::Present(ref root),
                ..
            } => laid_out(content.nodes(), *root),
            | DeclarationRoots::Value {
                signature: Maybe::Absent(_),
                ..
            } => Maybe::Absent(spelled::Absent::Unsigned),
            | DeclarationRoots::Data(_) => Maybe::Absent(spelled::Absent::Unpresentable),
        },
        | Typing::Synthesised { ref produced, .. } => {
            laid_out(produced.nodes(), NodeIndex::from(0))
        },
        | Typing::Refused(_) => Maybe::Absent(spelled::Absent::Refused),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::ItemKey;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_core_incremental::Occurrence;
    use gandr_core_incremental::Reference;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_grammar::built_in;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::spelled;
    use super::type_at;
    use super::type_of;
    use crate::Session;

    /// A session over the built-in grammar, in memory.
    ///
    /// # Specification
    /// trivial.
    fn session() -> Session<MemoryCheckpointStore, InMemoryBlockStore>
    {
        Session::new(
            built_in().expect("the grammar builds"),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            BackendArtifact::from(b"type observer".as_slice()),
        )
    }

    /// No resume, an absent name and a refused item have distinct absence
    /// reasons, while an owed signature retains its declared type.
    #[test]
    fn missing_and_refused_types_keep_their_absence_reasons()
    {
        let page = PageWidth::from(100_u32);
        let mut session = session();
        assert!(matches!(
            type_of(session.last(), SourceFragment::from("name"), page),
            Maybe::Absent(spelled::Absent::Unresumed)
        ));
        let _submitted = session
            .submit(SourceText::from("def name : String ;"))
            .expect("the session does not fault");
        assert!(matches!(
            type_of(session.last(), SourceFragment::from("missing"), page),
            Maybe::Absent(spelled::Absent::Uncheckpointed)
        ));
        assert!(
            matches!(type_of(session.last(), SourceFragment::from("name"), page),
            Maybe::Present(ref shown) if shown.as_ref() == "String")
        );
        let _submitted = session
            .submit(SourceText::from("def name : String ;\ndef name = 42 ;"))
            .expect("the mismatch is a refusal, not an engine fault");
        assert!(matches!(
            type_of(session.last(), SourceFragment::from("name"), page),
            Maybe::Absent(spelled::Absent::Refused)
        ));
    }

    /// An unsigned definition is spelled by the type its body synthesised.
    #[test]
    fn a_synthesised_type_is_spelled()
    {
        let mut session = session();
        let _submitted = session
            .submit(SourceText::from("def answer = 42 ;"))
            .expect("the session does not fault");
        assert!(
            matches!(type_of(session.last(), SourceFragment::from("answer"), PageWidth::from(100_u32)),
            Maybe::Present(ref shown) if shown.as_ref() == "Integer")
        );
    }

    /// Two members of one name in two modules are each spelled by their own
    /// occurrence of the key, and an occurrence past them is absent.
    #[test]
    fn each_occurrence_of_a_name_has_its_own_type()
    {
        let page = PageWidth::from(100_u32);
        let mut session = session();
        let _submitted = session
            .submit(SourceText::from(
                "module A {\n  def x = 1 ;\n}\nmodule B {\n  def x = \"one\" ;\n}\n",
            ))
            .expect("the session does not fault");
        let at = |occurrence: usize| {
            type_at(
                session.last(),
                &Reference::Item {
                    key: ItemKey::from("x"),
                    occurrence: Occurrence::from(occurrence),
                },
                page,
            )
        };
        assert!(matches!(at(0), Maybe::Present(ref shown) if shown.as_ref() == "Integer"));
        assert!(matches!(at(1), Maybe::Present(ref shown) if shown.as_ref() == "String"));
        assert!(matches!(
            at(2),
            Maybe::Absent(spelled::Absent::Uncheckpointed)
        ));
    }
}
