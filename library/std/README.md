# std

The standard library: the package every gandr program can read, built and checked by the same verbs as any package (`gandr check library/std`). Its first module is `std.package`, the theories a project's manifest is read from. The rest of this page is the map the later modules land from, one unit each (#628).

## Host access is by capability

`std` reaches the host on `cap-std`'s design: no ambient authority. A handle is the authority to act under it, and no path or address escapes the handle it was opened under. In gandr a handle is a capability of a host effect's operations (`Cap { read, write }` of `Fs`): a parameter, attenuable, scoped by its handler. Authority enters a program in one place, as `main`'s parameter, and never through a global. That is what `cap_std::ambient_authority()` marks in Rust.

## The module map

| module | holds | absorbs | seam | status |
| ------ | ----- | ------- | ---- | ------ |
| `std.package` | `Versioned`, `Gandr.Package`, `Gandr.Workspace`, and `Gandr.Module` and `Gandr.Dependency` with no model yet (#533 p2, p3) | the prelude's manifest theories; `corpus/model/projects/` imports it | none: no host access | landed |
| `std.nix` | `Nix.Derivation`, `Nix.Attribute` | none | none: a type provider (#2763) | reserved |
| `std.authority` | the ambient authority, `main`'s parameter, from which each host module's root capability is opened | none | `cap_std::ambient_authority`, `AmbientAuthority` | reserved |
| `std.fs` | `Fs` under a directory capability: open, read, write, create and remove beneath it; temporary directories removed with their scope | `corpus/model/builtins/host-modules.gandr`, `corpus/model/control/capability-attenuate.gandr` | `cap_std::fs::Dir`, `cap_tempfile::TempDir`, `cap_primitives::fs::open_dir` (resolution beneath its start); rustix `fs` | reserved |
| `std.net` | a pool capability of the addresses a program may bind or connect to; streams and datagrams opened within it | none | `cap_std::net::Pool`, `cap_net_ext::PoolExt`; rustix `net` | reserved |
| `std.time` | a system clock and a monotonic clock, each a capability; instants and durations | `corpus/model/effects/domhringr.gandr` § `Clock` | `cap_std::time::SystemClock`, `MonotonicClock`; `cap_time_ext::MonotonicClockExt` | reserved |
| `std.rand` | a randomness capability; distributions and draws | `corpus/model/effects/domhringr.gandr` § `Random` | `cap_rand::thread_rng`, `cap_rand::rngs::CapRng` | reserved |
| `std.process` | `Proc`: exit and the process's arguments, under the capability `main` is given | `corpus/model/control/capability-region.gandr`, `corpus/model/control/program-exit.gandr` | rustix `process`; `cap-std` has no process type | reserved |
| `std.env` | the environment's variables, read under `main`'s authority | none | none: `cap-std` leaves the environment ambient, so the capability is gandr's own | reserved |
| `std.console` | `Console`: the standard streams | `corpus/model/effects/hello.gandr` | the standard streams' descriptors, borrowed as `BorrowedFd` (I/O safety) | reserved |
| `std.nat`, `std.list`, `std.string` | the native data, their eliminators and everyday functions, each law beside it as a derived cell | `corpus/model/basics/`, `corpus/model/builtins/lists.gandr`, `corpus/model/builtins/strings.gandr` | none: no host access | reserved |
| `math` | identity, equivalences, h-levels, the circle | the HoTT exemplars (#628) | none | declined here: a library of its own, which builds on `std` |

A module's interface is what its `pub` declarations state; a declaration is private by default. Every definition with a law ships the law beside it as a derived cell, proved by its completion certificate (#628). No theory of `std.package` has a law: its operations are fields the manifest records.

## Importing it

A project imports `std.package` by the relative path to its source, `library/std/src/package.gandr`, until a package imports another by name (#533 p3). A source under any root may import one under the strict root, so the corpus's fixtures read `std` as a package does, and `std`'s declarations settle as strictly as they do alone.
