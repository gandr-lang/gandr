//! The crossing between the composition and the run stage.
//!
//! Settlement runs each declaration that states what it runs to, so the
//! composition runs a program before a source has a verdict. The data of a
//! program, its construction and its reads stay in this crate
//! ([`Program`]). The runs stand in their own crate above this one
//! (`gandr-surface-evaluate`), and the composition reaches them through
//! [`Engine`], which that crate implements. The composition, the walk, the
//! type table and the run verb take the engine as a generic parameter, and
//! the crate that names the engine monomorphises them.

use alloc::string::String;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_net::Net;
use gandr_surface_corpus::Runner;

use crate::entry::console::Console;
use crate::entry::entered::Entered;
use crate::entry::entered::Entry;
use crate::entry::entered::RealsProfile;
use crate::entry::evaluation::Evaluation;
use crate::entry::evaluation::Terminal;
use crate::entry::worlds::Hosted;
use crate::entry::worlds::MigrationCount;
use crate::entry::worlds::Worlds;
use crate::pool::Pool;
use crate::program::Program;

/// The run stage, as the composition, the walk, the type table and the run
/// verb read it: each run of a program.
///
/// # Specification
/// - executable: none — a trait; each implementation states its contracts on
///   its own items.
pub trait Engine
{
    /// The runs of `program`, each sequential: what settles a composition.
    ///
    /// # Specification
    /// - requires: `program` is the program that the composition builds for the
    ///   module it settles.
    /// - ensures: a runner whose each run is a sequential run of `program`.
    /// - provides: the runs that a sequential settlement compares.
    /// - fails: never; a run that cannot be carried out is an outcome.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure judged once and each document after it
    ///   settle their runs as a whole judgement does.
    /// - witness: `tests::compose::a_closure_judged_once_judges_each_document_alike_776`
    fn runs<'run>(program: &'run mut Program<'_>) -> impl Runner + 'run;

    /// The runs of `program`, each independent writer started on `pool`: what
    /// settles a composition scheduled concurrently.
    ///
    /// # Specification
    /// - requires: as [`Self::runs`].
    /// - ensures: a runner whose runs give what [`Self::runs`] gives, each
    ///   independent writer a job of `pool`.
    /// - provides: the runs that a concurrent settlement compares.
    /// - fails: never; a run that cannot be carried out is an outcome.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source settles on the concurrent
    ///   schedule as on the sequential one.
    /// - witness: `tests::corpus::sweeps::the_concurrent_schedule_settles_the_corpus_alike_2954`
    fn scheduled<'run>(
        program: &'run mut Program<'_>,
        pool: &'run Pool,
    ) -> impl Runner + 'run;

    /// Run the declaration of `program` at `constant`.
    ///
    /// # Specification
    /// - requires: `constant` is an admission position of `program`; a position
    ///   that it does not hold is an outcome of its own.
    /// - ensures: what the run of that declaration came to.
    /// - fails: never; a run that cannot be carried out is an outcome.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a workspace reads each field of its model by a run,
    ///   and a value runs to its spelling.
    /// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
    /// - witness: `gandr-surface-evaluate::evaluate::tests::a_value_runs_to_its_spelling`
    fn evaluate<'source>(
        program: &mut Program<'source>,
        constant: ConstantIndex,
    ) -> Evaluation<'source>;

    /// Run the function of `program` at `constant` on `arguments` under
    /// `host`.
    ///
    /// # Errors
    /// What `host` aborts the run with.
    ///
    /// # Specification
    /// - requires: `constant` is the admission position of a function of
    ///   `program`, and `arguments` are values of `into`.
    /// - ensures: the terminal of the call, read back into `into`.
    /// - fails: with what `host` aborts the run with.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a site reads its secret by a call of the model that
    ///   the run names.
    /// - witness: `tests::manifold::a_site_reads_its_secret_from_the_model_given_3375`
    fn call<'source, Host>(
        program: &mut Program<'source>,
        constant: ConstantIndex,
        arguments: &[ValueId],
        into: &mut CoreArena,
        host: &mut Host,
    ) -> Result<Terminal<'source>, Host::Abort>
    where
        Host: HostHandler;

    /// Run `entry` of `program` with `arguments`.
    ///
    /// # Specification
    /// - requires: `entry` is the entry of `program`.
    /// - ensures: how the entry ended, with each line it printed on `console`,
    ///   each migration it shipped on the net of `hosting`.
    /// - fails: never; an entry that cannot run is an outcome.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source that declares `main` runs its entry.
    /// - witness: `tests::script::a_source_declaring_main_runs_its_entry_1881`
    fn enter<'source>(
        program: &mut Program<'source>,
        entry: Entry,
        arguments: &[String],
        console: &mut dyn Console,
        hosting: (Option<&mut Net>, Option<Worlds<'_>>, RealsProfile),
    ) -> Entered<'source>;

    /// Host the worlds of `program` on `net` for `migrations`.
    ///
    /// # Specification
    /// - requires: `worlds` binds each world that a migration of `program`
    ///   names.
    /// - ensures: each migration hosted, up to `migrations`, with what each
    ///   printed on `console`.
    /// - fails: never; a migration that cannot run is an outcome.
    /// - panics: none.
    /// - executable: none — a required trait method has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two hosts in turn each host two migrations.
    /// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    fn host(
        program: &mut Program<'_>,
        worlds: Worlds<'_>,
        net: &mut Net,
        migrations: MigrationCount,
        console: &mut dyn Console,
    ) -> Hosted;
}
