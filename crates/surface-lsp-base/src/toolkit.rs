//! The process's one toolkit: the built-in grammar, the role table read off
//! it and the forms an inline completion offers under it.
//!
//! Every recheck, every highlight, the outline and the inline completion read
//! one grammar. The first call builds it, and each later call reads the same
//! value at the same address.

use std::sync::OnceLock;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::built_in;

use crate::inline::Forms;

/// The built-in grammar, the role table read off it and the forms an inline
/// completion offers under it.
#[derive(Debug)]
struct Toolkit
{
    /// The grammar every document is parsed and composed under.
    grammar: Pbg,
    /// The roles its molds highlight as.
    roles: RoleTable,
    /// The forms a hole of each sort can open.
    forms: Forms,
}

/// The process's one toolkit, or the fault that kept it from building.
static TOOLKIT: OnceLock<Result<Toolkit, PbgError>> = OnceLock::new();

/// The process's one toolkit, built on first use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same toolkit, at the same address, on every call; the
///   grammar, its role table and its forms are built by the first call alone.
/// - provides: the grammar every recheck and every highlight reads.
/// - fails: the [`PbgError`] the first build met, on every call, since the
///   built-in grammar is the same on every call.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — two calls are asserted to answer one address.
/// - witness: `toolkit::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| TOOLKIT.get().is_some_and(|stored|
    match (stored.as_ref(), ret) {
        (Ok(expected), Ok(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
        (Err(expected), Err(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
        _ => false,
    }))]
fn toolkit() -> Result<&'static Toolkit, &'static PbgError>
{
    TOOLKIT
        .get_or_init(|| {
            let grammar = built_in()?;
            let roles = RoleTable::build(&grammar)?;
            let forms = Forms::new(&grammar);
            Ok(Toolkit {
                grammar,
                roles,
                forms,
            })
        })
        .as_ref()
}

/// The process's one grammar, built on first use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the grammar of [`toolkit`], at the same address on every call.
/// - provides: the grammar an inline completion and the outline mold under.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the grammar is asserted at the toolkit's address;
///   building a grammar of its own changes that address.
/// - witness: `toolkit::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
#[inline]
pub fn grammar() -> Result<&'static Pbg, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.grammar)
}

/// The forms of the process's one grammar, read off it with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the forms of [`toolkit`], at the same address on every call.
/// - provides: the forms an inline completion offers to fill a slot.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the forms are asserted at the toolkit's address; forms
///   read off a grammar of their own change that address.
/// - witness: `toolkit::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
#[inline]
pub fn forms() -> Result<&'static Forms, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.forms)
}

/// The role table of the process's one grammar, built with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the role table of [`toolkit`], at the same address on every call.
/// - provides: the roles the outline reads a declaration's name by.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the role table is asserted at the toolkit's address; a
///   table built over a grammar of its own changes that address.
/// - witness: `toolkit::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
#[inline]
pub fn roles() -> Result<&'static RoleTable, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.roles)
}

#[cfg(test)]
mod tests
{
    use super::forms;
    use super::grammar;
    use super::roles;
    use super::toolkit;

    #[test]
    fn the_grammar_is_built_once_per_process()
    {
        let first = toolkit().expect("the built-in grammar builds");
        let second = toolkit().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(first), core::ptr::from_ref(second)),
            "each recheck reads one shared grammar rather than building its own"
        );
        let grammar = grammar().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(grammar), &raw const first.grammar),
            "an inline completion molds under the toolkit's grammar"
        );
        let forms = forms().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(forms), &raw const first.forms),
            "an inline completion offers the toolkit's forms"
        );
        let roles = roles().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(roles), &raw const first.roles),
            "the outline names each declaration by the toolkit's roles"
        );
    }
}
