# gandr-core-publish

The one writer that publishes a file whole: a private temporary, created exclusively, then renamed onto the file's name.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A small crate: `publish` writes a file's contents into a temporary beside the file and renames it onto the file's name. A reader of the directory sees the old bytes or the new ones, never half of either. `Unpublished` names the file, the step the file system refused and what it said.

**Why.** The record stores of `core-incremental` and the planes and roots of `storage-store` each published their files this way. A `core` crate depends on no `storage` crate, so the writer lives in a crate of its own. A consumer at any layer from the core upward reaches it.

**How.** The temporary's name is the file's, then `.tmp-`, the process and a nonce. The write opens it only by creating it, so a name that another writer or a squatter holds is never written through. A guard owns the temporary from its creation, and on every exit but the rename it attempts to remove the file. [`src/lib.rs`](src/lib.rs) states each step's obligations.

## References

- `vault:01a178aa-4bbc-7842-9a60-d11551c41e06` — lineage: the rollback audit (§ The real leak was in the filesystem), where the guard over the temporary and its exclusively created name come from.

## Provided features

- `publish(directory, name, contents)`: the file `name` of `directory` holds `contents`, and no temporary of the publication remains.
- `Unpublished`: the file, the `Step` refused (`Create`, `Write` or `Rename`) and the file system's `io::ErrorKind`. A run of taken temporary names is a `Create` refusal with `AlreadyExists`.

## Expected features

- **An existing directory.** The writer creates no directory. A missing one refuses the creation.
- **One file name.** `name` spells one file name, with no separator.
- **Atomicity, not durability.** No sync precedes or follows the rename, so a crash may lose a file just published.

## Examples

```rust
use gandr_core_publish::Contents;
use gandr_core_publish::publish;

let directory = std::env::temp_dir().join(format!("gandr-core-publish-example-{}", std::process::id()));
std::fs::create_dir_all(&directory).expect("a directory");
publish(&directory, "greeting", Contents(b"hello")).expect("published");
assert_eq!(std::fs::read(directory.join("greeting")).expect("read"), b"hello");
std::fs::remove_dir_all(&directory).expect("removed");
```

The tests run as below, the second line the enforcing twin that checks every specification:

```sh
cargo nextest run -p gandr-core-publish
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-core-publish
```

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
