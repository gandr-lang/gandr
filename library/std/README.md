# std

The standard library: the package every gandr program can read, built and checked by the same verbs as any package (`gandr check library/std`). Its first modules are `std.build`, the theories a project's manifest is read from, `std.layout` and `std.boundary`, Rust's default layout and the foreign boundary's function rows, `std.grade`, the grade algebras, `std.cost`, decalf's cost effect, `std.manifold`, the theories a deployment's files are read from, `std.authority`, the ambient authority `main` is handed, `std.io`, the standard streams opened from it, `std.secret`, a secret no run can ship, print or compare, `std.string`, strings joined and the laws of joining, and `std.math.path` and `std.math.cylinder`, the algebra of paths and its composites. The rest of this page is the map the later modules land from, one unit each (#628).

## Names follow Rust's hierarchy

Packages and modules are lowercase, and types and theories are capitalized: `std.fs`, `std.io.Console`. The hierarchy follows Rust's `std` first, and PureScript's or cubical Agda's where Rust has no analogue. `std.io` holds the standard streams and the ring, and `std.fs`, `std.net`, `std.process`, `std.env`, `std.time` and `std.rand` stand beside it. Theoretical mathematics stands under `std.math`, its algebraic hierarchy with it. A library that is truly separate, as a `hott` library would be, is a package of its own (#4529).

## Host access is by capability

`std` reaches the host on `cap-std`'s design: no ambient authority. A handle is the authority to act under it, and no path or address escapes the handle it was opened under. In gandr a handle is a capability of a host effect's operations (`Cap { read, write }` of `Fs`): a parameter, attenuable, scoped by its handler. Authority enters a program in one place, as `main`'s parameter, and never through a global. That is what `cap_std::ambient_authority()` marks in Rust.

## Where a module states its facts

Each module of `library/std/src/` states its facts in its head comment: what it holds, the corpus sources that use it, and the host seam with the `cap-std` type that it mirrors. A module with no host access states no seam.

`std` reserves five names, and no module of `src/` has them. `std.partial` is the home of `Partial`, the divergence interface, which stays ambient by its bare name (#4496). `std.time` is a system clock and a monotonic clock, each a capability, over `cap_std::time::SystemClock` and `MonotonicClock`; `corpus/model/effects/domhringr.gandr` § `Clock` uses one. `std.nix` is a type provider of `Nix.Derivation` and `Nix.Attribute` (#2763). `std.nat` is the native data with their eliminators, over `corpus/model/basics/`. The rest of `std.math` is the rest of #628: identity's remaining laws, the equivalence formers, the h-level ladder, the circle and its loop space, the directed layer, and the algebraic hierarchy.

A module's interface is what its `pub` declarations state; a declaration is private by default. Every definition with a law ships the law beside it as a derived cell, proved by its completion certificate (#628). No theory of `std.build` has a law: its operations are fields the manifest records. A groupoid law of `std.math` is a definition at its path type, proved by based path induction or by conversion, and the kernel replays it.

## Importing it

A source imports a module of `std` by name from under any root, `import std.string (concat);`. A module path whose head is `std` names the standard library's module when no source or locked dependency of the importer's package takes the name `std`. The standard library is `library/std` of the tree that built the toolchain. A source under any root may import one under the strict root, so the corpus's fixtures read `std` as a package does, and `std`'s declarations settle as strictly as they do alone.
