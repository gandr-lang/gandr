//! The register: the one writer of a store's roots, and the namers that hand
//! their namings to it.
//!
//! [`Store::open`](crate::Store::open) gives a store and its register. The
//! register names a root through `&mut self`, so one owner holds it and no
//! two writers of the roots stand in one process. A thread that shares the
//! store hands its naming to the owner through a [`Namer`], a sender on a
//! channel: the send takes `&self`, no lock and no system call. The owner
//! drains the channel at its next naming and at [`Register::drain`]. It first
//! syncs each segment of the two planes that a batch wrote to since the last
//! naming, so a root never names an object a crash can lose. It then holds
//! the roots lock alone once for each drain, appends each naming to the roots
//! journal in order, and then publishes one snapshot of the roots. A reader
//! loads that snapshot through [`Store::roots`](crate::Store::roots) with no
//! lock. A process whose run never ends, as a language server, gives the
//! register to a thread of its own, which waits for each naming in
//! [`Register::serve`].
//!
//! The snapshot sits in an `arc_swap::ArcSwap`, the atomically swappable
//! `Arc` of the ecosystem. A load is a few atomic operations and waits for no
//! writer. A `std::sync::RwLock<Arc<Roots>>` is the lock that this store
//! takes out. `left-right` keeps two copies, and its writer waits at each
//! publication for every reader of the old copy. A high advisory against
//! `arc-swap`, its end of maintenance, or an atomic `Arc` in `std` reverses
//! the choice.
//!
//! # Boundaries
//!
//! The roots journal stays the hand-off between processes: a second store
//! over the directory reads what this register appended. A naming that is in
//! the channel at a crash is lost, and the next process computes it again. A
//! reader in the process sees a naming after the owner's next drain.
//!
//! # References
//!
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — lineage: the store's single
//!   writer plan, whose register is the one owner of the roots, and whose
//!   readers load a snapshot through `arc-swap`.
//! - `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: the performance
//!   programme (§ performance-picture) — the writer syncs the marked segments
//!   before it names a root, so no root names an object a crash can lose.

use alloc::sync::Arc;
use std::path::PathBuf;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;

use arc_swap::ArcSwap;
use gandr_storage_values::ContentPtr;

use crate::crash;
use crate::crash::Point;
use crate::plane::ChunkDirectory;
use crate::plane::NodeDirectory;
use crate::roots::Kept;
use crate::roots::Naming;
use crate::roots::RootName;
use crate::roots::Roots;
use crate::store::Hold;
use crate::store::StoreError;
use crate::store::locked;

/// A handle that hands namings to a register's owner. It is `Clone` and
/// `Sync`, and its naming takes `&self`, so threads share it with no lock.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Namer(Sender<Naming>);

impl Namer
{
    /// Hand the naming of `pointer` by `name` to the register's owner.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the owner's next drain names `pointer` by `name`,
    ///   after every naming this namer handed over before.
    /// - provides: the naming of a root from a thread that does not own the
    ///   register.
    /// - fails: [`StoreError::Unowned`] when the register is gone.
    /// - panics: none.
    /// - executable: none — the naming waits in the channel.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the namings of sixteen threads stand after one drain,
    ///   and a store opened later reads each.
    /// - witness: `tests::store::the_namings_of_sixteen_threads_stand_after_one_drain_6899`
    #[inline]
    pub fn name(
        &self,
        name: RootName,
        pointer: ContentPtr,
    ) -> Result<(), StoreError>
    {
        self.0
            .send(Naming::new(name, pointer))
            .map_err(|_unowned| StoreError::Unowned)
    }
}

/// The one writer of a store's roots. It is neither `Clone` nor `Sync`, and
/// its namings take `&mut self`, so one owner names the roots.
#[derive(Debug)]
pub struct Register
{
    /// What writes the roots.
    writer: Writer,
    /// The namings the namers handed over.
    namings: Receiver<Naming>,
    /// The sender each namer clones.
    namer: Sender<Naming>,
}

impl Register
{
    /// The register of the store at `root`: its value plane `chunks`, its
    /// record plane `nodes`, its roots `kept`, and the snapshot `published`
    /// that its readers load.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn new(
        root: PathBuf,
        (chunks, nodes): (Arc<ChunkDirectory>, Arc<NodeDirectory>),
        kept: Kept,
        published: Arc<ArcSwap<Roots>>,
    ) -> Self
    {
        let (namer, namings) = std::sync::mpsc::channel();
        Self {
            writer: Writer {
                root,
                chunks,
                nodes,
                kept,
                published,
            },
            namings,
            namer,
        }
    }

    /// A namer that hands its namings to this register.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn namer(&self) -> Namer
    {
        Namer(self.namer.clone())
    }

    /// Name `pointer` by `name`, whatever `name` named before, after each
    /// naming the namers handed over.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Register::drain`], with this naming the last.
    /// - provides: the owner's own naming of a root.
    /// - fails: as [`Register::drain`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening, a second
    ///   setting of one name replaces it, two stores over one directory keep
    ///   each other's roots, and namings one at a time leave far fewer nodes
    ///   than namings.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    /// - witness: `tests::store::naming_roots_one_at_a_time_writes_no_tree_per_naming_4081`
    #[inline]
    pub fn name(
        &mut self,
        name: RootName,
        pointer: ContentPtr,
    ) -> Result<(), StoreError>
    {
        self.writer.write(
            self.namings
                .try_iter()
                .chain(core::iter::once(Naming::new(name, pointer))),
        )
    }

    /// Name each naming that the namers handed over since the last drain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with no naming handed over, nothing is read or written.
    ///   Otherwise, on success, the roots read again under the roots lock
    ///   alone, with each naming's name naming its pointer in the order the
    ///   channel gives them, stand on disk. The store's readers then load them
    ///   as one snapshot, so every root that another store over the directory
    ///   set stands too. On failure the namings taken are lost, and the readers
    ///   load the snapshot before.
    /// - provides: the owner's write of every naming of the process.
    /// - fails: [`StoreError::Io`] when the lock or a file cannot be used, and
    ///   the faults of reading and writing the roots.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one lock, one reading of what other stores journaled, one
    ///   write of the entries between two folds, and one snapshot for each
    ///   drain.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the namings of sixteen threads stand after one drain,
    ///   for the store's readers and for a store opened later.
    /// - witness: `tests::store::the_namings_of_sixteen_threads_stand_after_one_drain_6899`
    #[inline]
    pub fn drain(&mut self) -> Result<(), StoreError>
    {
        self.writer.write(self.namings.try_iter())
    }

    /// Wait for each naming, and name it with each other naming handed over by
    /// then, until every namer is gone: the owner of a register whose namers
    /// live as long as the process, as a language server's do.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every naming a namer handed over stands, as
    ///   [`Register::drain`] leaves it, once every namer is gone. Each wait
    ///   ends at the next naming, and the drain after it holds the lock once.
    /// - provides: the owner thread of a process that never ends its run.
    /// - fails: as [`Register::drain`], at the first drain that fails.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a serving register names each naming that namers on
    ///   other threads hand it, and returns once they are gone.
    /// - witness: `tests::store::a_serving_register_names_each_naming_until_its_namers_go_6899`
    #[inline]
    pub fn serve(self) -> Result<(), StoreError>
    {
        let Self {
            mut writer,
            namings,
            namer,
        } = self;
        drop(namer);
        for first in &namings {
            writer.write(core::iter::once(first).chain(namings.try_iter()))?;
        }
        Ok(())
    }
}

/// What writes a store's roots: the store's directory, its two planes, the
/// roots as last read or written, and the snapshot its readers load.
#[derive(Debug)]
struct Writer
{
    /// The directory the store is rooted at.
    root: PathBuf,
    /// The store's value plane, whose marked segments a naming syncs first.
    chunks: Arc<ChunkDirectory>,
    /// The store's record plane, which holds the roots tree.
    nodes: Arc<NodeDirectory>,
    /// The roots, as last read or written, and where the reading stands.
    kept: Kept,
    /// The snapshot the store's readers load.
    published: Arc<ArcSwap<Roots>>,
}

impl Writer
{
    /// Name each of `namings` in order under one lock, and publish one
    /// snapshot.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Register::drain`], with the namings of `namings`.
    /// - provides: the body of [`Register::name`], [`Register::drain`] and
    ///   [`Register::serve`].
    /// - fails: as [`Register::drain`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Register::drain`].
    /// - witness: `tests::store::the_namings_of_sixteen_threads_stand_after_one_drain_6899`
    fn write(
        &mut self,
        namings: impl Iterator<Item = Naming>,
    ) -> Result<(), StoreError>
    {
        let mut namings = namings.peekable();
        if namings.peek().is_none() {
            return Ok(());
        }
        // Every object a naming names stands durable before the naming.
        crash::passed(Point::ObjectsBefore);
        self.chunks.sync()?;
        self.nodes.sync()?;
        crash::passed(Point::ObjectsAfter);
        let lock = locked(&self.root, Hold::Alone)?;
        self.kept.name(&self.root, &self.nodes, namings)?;
        drop(lock);
        self.published.store(Arc::new(self.kept.roots().clone()));
        Ok(())
    }
}
