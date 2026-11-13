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
    fn runs<'run, 'source>(program: &'run mut Program<'source>) -> impl Runner + 'run;

    /// The runs of `program`, each independent writer started on `pool`: what
    /// settles a composition scheduled concurrently.
    fn scheduled<'run, 'source>(
        program: &'run mut Program<'source>,
        pool: &'run Pool,
    ) -> impl Runner + 'run;

    /// Run the declaration of `program` at `constant`.
    fn evaluate<'source>(
        program: &mut Program<'source>,
        constant: ConstantIndex,
    ) -> Evaluation<'source>;

    /// Run the function of `program` at `constant` on `arguments` under
    /// `host`.
    ///
    /// # Errors
    /// What `host` aborts the run with.
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
    fn enter<'source>(
        program: &mut Program<'source>,
        entry: Entry,
        arguments: &[String],
        console: &mut dyn Console,
        hosting: (Option<&mut Net>, Option<Worlds<'_>>, RealsProfile),
    ) -> Entered<'source>;

    /// Host the worlds of `program` on `net` for `migrations`.
    fn host(
        program: &mut Program<'_>,
        worlds: Worlds<'_>,
        net: &mut Net,
        migrations: MigrationCount,
        console: &mut dyn Console,
    ) -> Hosted;
}
