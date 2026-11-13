//! **Host tools**: the tools of `mise.toml` that publish no binary for the
//! target of a host of ours, built once for each version on a host of
//! another target.
//!
//! mise installs a tool from its release's binary. A release can publish no
//! binary for a target, and the riscv64 host meets that for ten tools of the
//! tree and for mise itself. There mise holds the binary of another
//! architecture, or no binary, and a job builds the tool from source on the
//! slowest host. This crate builds each such tool on a fast host instead.
//!
//! - [`names`] wraps each name a build reads and writes: a tool's key, a
//!   version, a target, an install name, a program, a placeholder, a repository
//!   and a template of a version.
//! - [`input`] reads a file whole and parses its TOML, with the file's path for
//!   a refusal.
//! - [`recipe`] reads the tree's table of the tools to build and how each one
//!   builds: a crate of crates.io, a cargo package of a git tag, or a Go
//!   package of a git tag.
//! - [`lock`] reads the version that `mise.lock` locks for each tool.
//! - [`host`] reads the builder's configuration: the linker and the C tools of
//!   each target, and the programs a build needs.
//! - [`jobs`] gives one job for each tool of a target, with its version and the
//!   name of its directory in mise's install directory.
//! - [`steps`] gives the commands that build a job.
//! - [`mod@build`] runs a job into its key, the directory `<target>/<install
//!   name>/<version>`, under a lock for the key.
//!
//! # Boundaries
//!
//! A key stands whole or not at all. A build writes into a partial directory
//! and renames it into the key at its end, so a build that stops leaves no
//! key, and the next run builds the tool again. The build keeps a key that
//! stands and never builds it again. The tree names no host: the builder's
//! linker, C tools and programs are its configuration.
//!
//! # References
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-host-tools/README.md).

pub mod build;
pub mod error;
pub mod host;
pub mod input;
pub mod jobs;
pub mod lock;
pub mod names;
pub mod recipe;
pub mod steps;

pub use crate::build::Built;
pub use crate::build::Processes;
pub use crate::build::Runner;
pub use crate::build::build;
pub use crate::error::HostToolsError;
pub use crate::host::Host;
pub use crate::input::Input;
pub use crate::jobs::Job;
pub use crate::jobs::plan;
pub use crate::lock::Lock;
pub use crate::names::Target;
pub use crate::names::ToolKey;
pub use crate::names::Version;
pub use crate::recipe::Builds;
pub use crate::recipe::Recipe;
pub use crate::recipe::Tool;
pub use crate::steps::Step;
