//! The reader of a Rust crate: a compiler driver on rustc's own libraries
//! that writes the record of the requested functions.
//!
//! The reader takes the build's command line for the crate, word for word,
//! and stops after the analysis. Cargo adds its own `-C metadata` value to
//! each crate, and that value enters each symbol. So a command line that the
//! reader built again would give other symbols. A Dylint driver adds its own
//! value too, so the reader is a driver of its own. Each output of the run
//! goes beside the entry, and no output of the build changes.
//!
//! The reader takes the paths of the functions in
//! `GANDR_RUST_RECORD_FUNCTIONS`, one on each line, and writes one entry of
//! the record to the file that `GANDR_RUST_RECORD_ENTRY` names. The entry
//! holds the digest of each source file that the compiler read, taken from
//! the bytes that it read.
//!
//! The reader exits with rustc's status. A crate that does not compile
//! writes no entry.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;

mod read;

use std::env;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;

use gandr_runtime_rust_record::Digest;
use gandr_runtime_rust_record::ENTRY;
use gandr_runtime_rust_record::Encoded;
use gandr_runtime_rust_record::Entry;
use gandr_runtime_rust_record::FUNCTIONS;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::Identity;
use gandr_runtime_rust_record::Record;
use gandr_runtime_rust_record::SourceFile;
use gandr_runtime_rust_record::SourcePath;
use gandr_runtime_rust_record::Target;
use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_interface::interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::FileLoader;

/// The source files that the compiler read, each with the digest of the
/// bytes that it read.
type Sources = Arc<Mutex<Vec<SourceFile>>>;

/// A file loader that reads as rustc's own does, and keeps the digest of
/// each file that it reads.
struct Loader
{
    /// The files read so far.
    sources: Sources,
}

impl Loader
{
    /// Keeps the digest of `bytes`, read from `path`.
    fn keep(
        &self,
        path: &Path,
        bytes: &[u8],
    ) -> io::Result<()>
    {
        let text = path.to_str().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "the reader keeps UTF-8 paths alone",
            )
        })?;
        let file = SourceFile {
            path: SourcePath::from(text),
            digest: Digest::of(Encoded(bytes)),
        };
        self.sources
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(file);
        Ok(())
    }
}

impl FileLoader for Loader
{
    fn file_exists(
        &self,
        path: &Path,
    ) -> bool
    {
        path.exists()
    }

    fn read_file(
        &self,
        path: &Path,
    ) -> io::Result<String>
    {
        let bytes = fs::read(path)?;
        self.keep(path, &bytes)?;
        String::from_utf8(bytes).map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
    }

    fn read_binary_file(
        &self,
        path: &Path,
    ) -> io::Result<Arc<[u8]>>
    {
        let bytes = fs::read(path)?;
        self.keep(path, &bytes)?;
        Ok(bytes.into())
    }

    fn current_directory(&self) -> io::Result<PathBuf>
    {
        env::current_dir()
    }
}

/// The driver's state: the request, and what the run wrote.
struct Reader
{
    /// The paths of the requested functions.
    functions: Vec<FunctionPath>,
    /// The file that the entry goes to.
    entry: PathBuf,
    /// The source files that the compiler read.
    sources: Sources,
    /// Whether the analysis ran and the entry was written.
    written: Option<io::Result<()>>,
}

impl rustc_driver::Callbacks for Reader
{
    /// Reads each source through the loader that keeps its digest, and puts
    /// each output of the run beside the entry. The build's command line
    /// stays word for word, and no output of the build changes.
    fn config(
        &mut self,
        config: &mut Config,
    )
    {
        config.file_loader = Some(Box::new(Loader {
            sources: Arc::clone(&self.sources),
        }));
        config.output_dir = self.entry.parent().map(Path::to_path_buf);
        config.output_file = None;
    }

    fn after_analysis(
        &mut self,
        _compiler: &Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation
    {
        let outcome = read::outcome(tcx, &self.functions);
        let identity = Identity {
            commit: Identity::of_build().commit,
            target: Target::from(tcx.sess.opts.target_triple.tuple()),
        };
        let sources =
            std::mem::take(&mut *self.sources.lock().unwrap_or_else(PoisonError::into_inner));
        let entry = Entry {
            sources,
            record: Record { identity, outcome },
        };
        self.written = Some(fs::write(&self.entry, entry.encode().as_encoded().0));
        Compilation::Stop
    }
}

fn main() -> ExitCode
{
    let (Ok(functions), Some(entry)) = (env::var(FUNCTIONS), env::var_os(ENTRY))
    else {
        return ExitCode::from(2);
    };
    let mut reader = Reader {
        functions: functions.lines().map(FunctionPath::from).collect(),
        entry: PathBuf::from(entry),
        sources: Arc::default(),
        written: None,
    };
    let arguments: Vec<String> = env::args().collect();
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&arguments, &mut reader));
    match reader.written {
        Some(Err(_)) => ExitCode::from(3),
        None if status == ExitCode::SUCCESS => ExitCode::from(4),
        Some(Ok(())) | None => status,
    }
}
