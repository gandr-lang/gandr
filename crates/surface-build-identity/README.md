# gandr-surface-build-identity

The `gandr` driver passes two build identities to the low crates. Each verdict key binds the identity of the kernel. Each stratum key binds the build of the theory sites.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)

## Synopsis

**What.** Two digests that the build script writes. `kernel` gives the kernel's `BuildIdentity`, and `sites` gives the `SitesBuild` of the theory sites.

**Why.** A stored verdict is recalled only by a kernel that gives the same verdict, so its key binds the build of the kernel. A digest that a low crate compiles in changes that crate, and Cargo compiles each package above it again. The driver alone depends on this crate. So a change that moves a digest compiles this crate and the driver again, and no library between them.

**How.** The build script reads the closure of each library over its normal and build dependencies. For each member of the workspace in the closure it reads the manifest, the build script and each file under `src`. For each other package in the closure it reads the locked name, version and source. It reads no test, bench, example or README, no member that a dev dependency alone reaches, and no other entry of the lock.

## Provided features

- `kernel`: the kernel's build identity, the digest of the closure of `gandr-kernel-core`.
- `sites`: the build of the theory sites, the digest of the closure of `gandr-theory-sites`.

## Expected features

- **A workspace.** The crate sits in the `crates` directory of the workspace, and the script reads the root manifest, each member's manifest and `Cargo.lock` there.
- **One consumer.** Only a crate that makes a binary depends on this crate. A library takes each identity as a value from its caller.

## Examples

```sh
cargo nextest run -p gandr-surface-build-identity
```

## Where the detail lives

The build script ([`build.rs`](build.rs)) writes the digests. The digest module ([`src/digest.rs`](src/digest.rs)) states what each digest reads, and its tests hold it on a small workspace.

## References

- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: the kernel verdict reuse — a verdict key covers the whole input of the kernel.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: the stratum receipt — the key of a stored stratum names the build that certified it.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence. The licence text is at the repository root.
