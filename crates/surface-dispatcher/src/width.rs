//! How many threads a walk lowers its sources on.
//!
//! # The default width is the host's physical performance cores
//!
//! A walk forks by source, and a source's parse is a single-threaded fold over
//! its tokens that wins nothing from a second hardware thread or a slower core
//! once every performance core holds one. The default width is therefore the
//! host's physical performance cores: efficiency cores and the second hardware
//! thread of a core are left idle. The host is asked only when a walk has two
//! sources or more to fork.

#[cfg(any(target_os = "linux", test))]
use alloc::collections::BTreeSet;
use core::num::NonZeroUsize;
#[cfg(any(target_os = "linux", test))]
use std::path::Path;

use anodized::spec;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why the host gave no performance-core count.
    mod topology {
        /// The reason no count is known.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The host's operating system has no topology query here.
            #[cfg_attr(
                any(target_os = "macos", target_os = "linux"),
                expect(dead_code, reason = "only a host without a topology query answers this")
            )]
            Unsupported,
            /// The query exists but could not be read or parsed.
            Unreadable,
        }
    }
}

/// A number of threads, at least one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Threads(NonZeroUsize);

impl Threads
{
    /// One thread.
    pub const ONE: Self = Self(NonZeroUsize::MIN);
}

impl From<NonZeroUsize> for Threads
{
    /// `threads` threads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(threads: NonZeroUsize) -> Self
    {
        Self(threads)
    }
}

impl From<Threads> for NonZeroUsize
{
    /// The number of threads `threads` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(threads: Threads) -> Self
    {
        threads.0
    }
}

/// How many threads a walk lowers its sources on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Width
{
    /// The host's physical performance cores, never more than the threads the
    /// process may run on.
    PerformanceCores,
    /// Exactly this many threads; one is the serial walk.
    Threads(Threads),
}

impl Width
{
    /// The serial walk: one thread, one source at a time.
    pub const SERIAL: Self = Self::Threads(Threads::ONE);

    /// The threads this width runs on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::Threads`] answers its count unchanged;
    ///   [`Self::PerformanceCores`] answers the host's physical performance
    ///   cores, capped by the parallelism the process may use, and that
    ///   parallelism alone when the host reports no topology.
    /// - provides: the pool size a walk forks on, before the walk caps it at
    ///   its source count.
    /// - fails: never; a host that answers nothing is one thread.
    /// - panics: none.
    /// - intension: asks the host once per call, and only for
    ///   [`Self::PerformanceCores`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an explicit count is returned exactly, and the host's
    ///   answer never exceeds the process's available parallelism. Whether that
    ///   answer is the performance-core count is the host's report, read on the
    ///   measured hosts, not a test oracle.
    /// - witness: `width::tests::an_explicit_width_is_exact`
    /// - witness: `width::tests::the_host_width_fits_the_process`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match self {
        Self::Threads(threads) => ret == threads,
        Self::PerformanceCores => std::thread::available_parallelism()
            .map_or(ret == Threads::ONE, |available| ret <= Threads(available)),
    })]
    pub fn threads(self) -> Threads
    {
        match self {
            | Self::Threads(threads) => threads,
            | Self::PerformanceCores => {
                let available =
                    Threads(std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN));
                match physical_performance_cores() {
                    | Maybe::Present(cores) => cores.min(available),
                    | Maybe::Absent(
                        topology::Absent::Unsupported | topology::Absent::Unreadable,
                    ) => available,
                }
            },
        }
    }
}

/// The host's physical performance cores, as the kernel reports them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on macOS, `hw.perflevel0.physicalcpu`, the physical cores of the
///   highest performance level, or `hw.physicalcpu` on a host with one level.
/// - fails: [`topology::Absent::Unreadable`] when neither name reads as a
///   positive count.
/// - panics: none.
/// - executable: none — the answer is the kernel's, read once; no local
///   predicate restates it.
///
/// # Adequacy
/// - hypothesis: L3 — the query's answer is bounded by the caller's witness;
///   the exact count is read on the measured hosts.
/// - witness: `width::tests::the_host_width_fits_the_process`
#[cfg(target_os = "macos")]
fn physical_performance_cores() -> Maybe<Threads, topology::Absent>
{
    use sysctl::Sysctl as _;

    for name in ["hw.perflevel0.physicalcpu", "hw.physicalcpu"] {
        let Ok(control) = sysctl::Ctl::new(name)
        else {
            continue;
        };
        let Ok(value) = control.value_string()
        else {
            continue;
        };
        if let Ok(cores) = value.trim().parse::<NonZeroUsize>() {
            return Maybe::Present(Threads(cores));
        }
    }
    Maybe::Absent(topology::Absent::Unreadable)
}

/// The host's physical performance cores, as the kernel reports them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`physical_cores_under`] over `/sys/devices`.
/// - fails: as [`physical_cores_under`].
/// - panics: none.
/// - executable: none — the answer is the kernel's, read once; no local
///   predicate restates it.
///
/// # Adequacy
/// - hypothesis: L3 — the reading is witnessed over scratch device trees; the
///   live tree's count is read on the measured hosts.
/// - witness: `width::tests::the_host_width_fits_the_process`
#[cfg(target_os = "linux")]
fn physical_performance_cores() -> Maybe<Threads, topology::Absent>
{
    physical_cores_under(Path::new("/sys/devices"))
}

/// The host's physical performance cores: no query on this operating system.
///
/// # Specification
/// trivial.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn physical_performance_cores() -> Maybe<Threads, topology::Absent>
{
    Maybe::Absent(topology::Absent::Unsupported)
}

/// The most logical CPUs a CPU list may name before it is read as malformed.
#[cfg(any(target_os = "linux", test))]
const MOST_CPUS: usize = 1 << 16;

/// One logical CPU, by the kernel's number.
#[cfg(any(target_os = "linux", test))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cpu(usize);

/// The physical cores of the performance CPUs in the Linux device tree at
/// `devices`.
///
/// # Specification
/// - requires: `devices` is a Linux `/sys/devices` tree, or a copy of the parts
///   read here.
/// - ensures: the performance CPUs are those `cpu_core/cpus` lists — the
///   performance half of a hybrid processor — or, where that file is absent,
///   those `system/cpu/online` lists. Two CPUs share a physical core exactly
///   when their `topology/core_cpus_list`, or `topology/thread_siblings_list`
///   on a kernel without it, read the same; the answer is the number of
///   distinct lists.
/// - fails: [`topology::Absent::Unreadable`] when a list is missing or
///   malformed, or names no CPU.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — scratch trees separate second hardware threads, a hybrid
///   processor's efficiency CPUs, the older sibling file, and missing or
///   malformed lists. Every kernel's file layout is outside these fixtures.
/// - witness: `width::tests::second_hardware_threads_share_a_core`
/// - witness: `width::tests::a_hybrid_processor_counts_its_performance_cores`
/// - witness: `width::tests::a_malformed_tree_reports_nothing`
#[cfg(any(target_os = "linux", test))]
#[spec(ensures: |ret| match ret {
    Maybe::Present(_) => true,
    Maybe::Absent(absent) => absent == topology::Absent::Unreadable,
})]
fn physical_cores_under(devices: &Path) -> Maybe<Threads, topology::Absent>
{
    let hybrid = devices.join("cpu_core/cpus");
    let performance = if hybrid.exists() {
        hybrid
    }
    else {
        devices.join("system/cpu/online")
    };
    let Maybe::Present(performance) = cpus(&performance)
    else {
        return Maybe::Absent(topology::Absent::Unreadable);
    };
    let mut cores = BTreeSet::new();
    for Cpu(cpu) in performance {
        let topology = devices.join(format!("system/cpu/cpu{cpu}/topology"));
        let siblings = std::fs::read_to_string(topology.join("core_cpus_list"))
            .or_else(|_error| std::fs::read_to_string(topology.join("thread_siblings_list")));
        let Ok(siblings) = siblings
        else {
            return Maybe::Absent(topology::Absent::Unreadable);
        };
        cores.insert(siblings.trim().to_owned());
    }
    NonZeroUsize::new(cores.len()).map_or(Maybe::Absent(topology::Absent::Unreadable), |cores| {
        Maybe::Present(Threads(cores))
    })
}

/// The CPUs the kernel CPU list at `path` names: comma-separated numbers and
/// inclusive ranges, such as `0-3,8`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each number, and each number of each range, appears once, in
///   ascending order.
/// - fails: [`topology::Absent::Unreadable`] when the file cannot be read,
///   holds anything but such a list, names a range backwards, or names more
///   than [`MOST_CPUS`] CPUs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — single numbers, ranges, a mixed list, a backwards range,
///   a stray word, an empty file and an oversized range have exact answers
///   through the device-tree witnesses.
/// - witness: `width::tests::second_hardware_threads_share_a_core`
/// - witness: `width::tests::a_hybrid_processor_counts_its_performance_cores`
/// - witness: `width::tests::a_malformed_tree_reports_nothing`
#[cfg(any(target_os = "linux", test))]
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref listed) => listed.windows(2).all(|pair| match *pair {
        [left, right] => left < right,
        _ => false,
    }) && listed.len() <= MOST_CPUS,
    Maybe::Absent(absent) => absent == topology::Absent::Unreadable,
})]
fn cpus(path: &Path) -> Maybe<Vec<Cpu>, topology::Absent>
{
    let Ok(list) = std::fs::read_to_string(path)
    else {
        return Maybe::Absent(topology::Absent::Unreadable);
    };
    let mut listed = BTreeSet::new();
    for item in list.trim().split(',') {
        let (first, last) = item.split_once('-').unwrap_or((item, item));
        let (Ok(first), Ok(last)) = (first.parse::<usize>(), last.parse::<usize>())
        else {
            return Maybe::Absent(topology::Absent::Unreadable);
        };
        if first > last || last.saturating_sub(first) >= MOST_CPUS {
            return Maybe::Absent(topology::Absent::Unreadable);
        }
        listed.extend((first ..= last).map(Cpu));
        if listed.len() > MOST_CPUS {
            return Maybe::Absent(topology::Absent::Unreadable);
        }
    }
    Maybe::Present(listed.into_iter().collect())
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use std::ffi::OsStr;
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use quenchant_shape::shape::Maybe;

    use super::Cpu;
    use super::Threads;
    use super::Width;
    use super::physical_cores_under;
    use super::topology;

    /// A scratch device tree, removed when dropped.
    #[repr(transparent)]
    struct Devices(PathBuf);

    impl Devices
    {
        /// An empty device tree named for `test` and this process.
        ///
        /// # Specification
        /// - requires: the derived temporary path is exclusively owned by this
        ///   fixture.
        /// - ensures: returns an empty directory at that path.
        /// - fails: never.
        /// - panics: if a stale directory cannot be removed or a new one
        ///   created.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — each witness writes its own files and reads an
        ///   exact count back; hostile permissions are outside these fixtures.
        /// - witness: `width::tests::second_hardware_threads_share_a_core`
        #[spec(ensures: |ref ret|
            std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()))]
        fn new(test: &Path) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-width-{}-{}",
                test.display(),
                std::process::id()
            ));
            if root.exists() {
                std::fs::remove_dir_all(&root).expect("a stale tree is removed");
            }
            std::fs::create_dir_all(&root).expect("the tree is created");
            Self(root)
        }

        /// Write `text` at `relative`, creating its directories.
        ///
        /// # Specification
        /// - requires: `relative` names a file below the tree.
        /// - ensures: the file holds `text`.
        /// - fails: never.
        /// - panics: if a directory or the file cannot be written.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the counts read back depend on every file
        ///   written; a lost write changes them.
        /// - witness: `width::tests::second_hardware_threads_share_a_core`
        #[spec(
            requires: relative.is_relative() && relative.file_name().is_some(),
            ensures: std::fs::read(self.0.join(relative))
                .is_ok_and(|written| written == text.as_encoded_bytes()),
        )]
        fn file(
            &self,
            relative: &Path,
            text: &OsStr,
        )
        {
            let path = self.0.join(relative);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("the directories are created");
            std::fs::write(path, text.as_encoded_bytes()).expect("the file is written");
        }

        /// Give `cpu` the sibling list `siblings` in its topology file `name`.
        ///
        /// # Specification
        /// trivial.
        fn siblings(
            &self,
            Cpu(cpu): Cpu,
            name: &Path,
            siblings: &OsStr,
        )
        {
            self.file(
                &Path::new("system/cpu")
                    .join(format!("cpu{cpu}"))
                    .join("topology")
                    .join(name),
                siblings,
            );
        }
    }

    impl Drop for Devices
    {
        /// Remove the tree.
        ///
        /// # Specification
        /// - requires: the fixture exclusively owns its directory.
        /// - ensures: the directory no longer exists.
        /// - fails: never.
        /// - panics: if removal fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — removal on normal exit; unwinding is outside it.
        /// - witness: `width::tests::second_hardware_threads_share_a_core`
        #[spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the tree is removed");
        }
    }

    #[test]
    fn an_explicit_width_is_exact()
    {
        let three = Threads(NonZeroUsize::new(3).expect("three is not zero"));
        assert_eq!(Width::Threads(three).threads(), three);
        assert_eq!(Width::SERIAL.threads(), Threads::ONE);
    }

    #[test]
    fn the_host_width_fits_the_process()
    {
        let available = std::thread::available_parallelism().expect("the host reports parallelism");
        assert!(Width::PerformanceCores.threads() <= Threads(available));
    }

    #[test]
    fn second_hardware_threads_share_a_core()
    {
        let two = Maybe::Present(Threads(NonZeroUsize::new(2).expect("two is not zero")));
        let core_cpus = Path::new("core_cpus_list");
        let devices = Devices::new(Path::new("smt"));
        devices.file(Path::new("system/cpu/online"), OsStr::new("0-3\n"));
        for (cpu, siblings) in [(0, "0,2"), (1, "1,3"), (2, "0,2"), (3, "1,3")] {
            devices.siblings(Cpu(cpu), core_cpus, OsStr::new(siblings));
        }
        assert_eq!(
            physical_cores_under(&devices.0),
            two,
            "four hardware threads on two cores"
        );
        let older = Devices::new(Path::new("smt-older"));
        older.file(Path::new("system/cpu/online"), OsStr::new("0-1,4\n"));
        for (cpu, siblings) in [(0, "0-1"), (1, "0-1"), (4, "4")] {
            older.siblings(
                Cpu(cpu),
                Path::new("thread_siblings_list"),
                OsStr::new(siblings),
            );
        }
        assert_eq!(
            physical_cores_under(&older.0),
            two,
            "a kernel without core_cpus_list is read through thread_siblings_list"
        );
    }

    #[test]
    fn a_hybrid_processor_counts_its_performance_cores()
    {
        let devices = Devices::new(Path::new("hybrid"));
        devices.file(Path::new("system/cpu/online"), OsStr::new("0-7\n"));
        devices.file(Path::new("cpu_core/cpus"), OsStr::new("0-3\n"));
        for (cpu, siblings) in [
            (0, "0-1"),
            (1, "0-1"),
            (2, "2-3"),
            (3, "2-3"),
            (4, "4"),
            (5, "5"),
            (6, "6"),
            (7, "7"),
        ] {
            devices.siblings(Cpu(cpu), Path::new("core_cpus_list"), OsStr::new(siblings));
        }
        assert_eq!(
            physical_cores_under(&devices.0),
            Maybe::Present(Threads(NonZeroUsize::new(2).expect("two is not zero"))),
            "the efficiency CPUs 4 to 7 are not counted"
        );
    }

    #[test]
    fn a_malformed_tree_reports_nothing()
    {
        let unreadable = Maybe::Absent(topology::Absent::Unreadable);
        let core_cpus = Path::new("core_cpus_list");
        let empty = Devices::new(Path::new("empty"));
        assert_eq!(physical_cores_under(&empty.0), unreadable, "no online list");
        for (name, online) in [
            ("backwards", "3-0\n"),
            ("word", "0-1,many\n"),
            ("blank", "\n"),
            ("huge", "0-4294967295\n"),
        ] {
            let devices = Devices::new(Path::new(name));
            devices.file(Path::new("system/cpu/online"), OsStr::new(online));
            devices.siblings(Cpu(0), core_cpus, OsStr::new("0"));
            assert_eq!(
                physical_cores_under(&devices.0),
                unreadable,
                "the online list {online:?}"
            );
        }
        let orphan = Devices::new(Path::new("orphan"));
        orphan.file(Path::new("system/cpu/online"), OsStr::new("0-1\n"));
        orphan.siblings(Cpu(0), core_cpus, OsStr::new("0"));
        assert_eq!(
            physical_cores_under(&orphan.0),
            unreadable,
            "an online CPU without a topology"
        );
    }
}
