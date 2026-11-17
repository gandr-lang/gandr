//! The heads of a text laid after its closure.

use alloc::vec::Vec;

use gandr_surface_lsp_core::signature::Signatures;
use gandr_surface_lsp_core::signature::kept_closure_heads;
use gandr_surface_syntax::SourceText;

use crate::toolkit::grammar;
use crate::toolkit::roles;

/// #1403: an importer's heads, read after its closure's lowering, are the
/// heads read off its whole tree, and a second reading after the same
/// lowering takes the closure's part kept instead of walking its forms.
#[test]
fn a_closure_s_heads_are_read_once_per_lowering_1403()
{
    use alloc::sync::Arc;

    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_lsp_base::quiet::formless;
    use gandr_surface_pretty::Spelling;
    use quenchant_shape::shape::Maybe;

    use crate::protocol::DocumentUri;
    use crate::recheck::open;
    use crate::recheck::recheck;

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/model/identity/circle-elim.gandr");
    let written = std::fs::read_to_string(&path).expect("the corpus importer is read");
    let text = SourceText::from(written.as_str());
    let uri = DocumentUri::from(format!("file://{}", path.display()).as_str());
    let mut session = open(&uri, &Arc::default());
    let rechecked = recheck(
        &uri,
        &mut session,
        text,
        &gandr_surface_dispatcher::Unshadowed,
        Verbosity::User,
        Spelling::Unicode,
        Maybe::Absent(formless::Absent::Uncareted),
    );
    let Maybe::Present(laid) = rechecked.laid
    else {
        panic!("the importer is laid out after its closure");
    };
    let session = session.expect("the grammar builds");
    let grammar = grammar().expect("the grammar builds");
    let roles = roles().expect("the roles build");
    let mut read = None;
    let _table = session.type_held_unit(
        SourceText::from(laid.text.as_str()),
        (&laid.unit, laid.base),
        |tree, closure| {
            let key = closure.expect("the process holds the closure's lowering");
            let after =
                Signatures::after(grammar, roles, (tree, &laid.unit, laid.base), Some(&key));
            let whole = Signatures::of(grammar, roles, tree, &laid.unit);
            let again = kept_closure_heads(&key, || {
                panic!("a closure whose heads are kept is not walked again")
            });
            read = Some((after, whole, again));
        },
    );
    let (after, whole, again) = read.expect("the laid revision parses");
    assert!(
        !after.closure().is_empty() && !after.own().is_empty(),
        "the closure and the importer each declare heads"
    );
    assert_eq!(
        after
            .closure()
            .iter()
            .chain(after.own())
            .cloned()
            .collect::<Vec<_>>(),
        whole.own(),
        "the closure's heads then the importer's are the whole tree's"
    );
    assert!(
        Arc::ptr_eq(after.closure(), &again),
        "the second reading takes the heads the first kept"
    );
}
