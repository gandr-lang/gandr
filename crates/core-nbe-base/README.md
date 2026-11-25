# gandr-core-nbe-base

The base of the glued value domain: the per-run arena that owns it, its closures, values and neutrals, the free indices of a core term, the content guards, element identity, the stage terms, and the sharing overlay with its erasure and its measure. The evaluator and the conversion machine compile over this crate. An edit of the evaluator rebuilds neither this crate nor a crate that reads only this crate.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The data of normalization by evaluation. A `DomainArena` holds the glued nodes of one run: each carries what it denotes together with the core term it came from, and a neutral carries its unfolded form beside its neutral form. An `Overlay` holds the shares of a term, and the `erase_*` functions and `SharingMeasure` read it.

**Why.** The domain, its identity and its overlay name no module of the evaluator, and the evaluator names each of them. So the domain compiles first, and an edit of the evaluator does not rebuild it.

**How.** `gandr-core-nbe` imports each module of this crate under its old name and re-exports each path a consumer names today; [`src/lib.rs`](src/lib.rs) lists the modules. The tests of element identity evaluate and read back, so they are tests of `gandr-core-nbe`.

## Provided features

- **The glued domain.** `DomainArena` with its id families and watermark; `DomainValue`, `DomainComp`, `Neutral` and the faces they carry; `ValueClosure`, `CompClosure` and the two-zone `Environment`.
- **Free indices.** `FreeIndices` and `FreeFault`: the free indices of a core term in each zone.
- **The cached word.** `Guard`, `GuardAnswer` and `ContentHash`.
- **Element identity.** `identity::clause`, `identity::fibre` and the motives an identity's transport reads.
- **Sharing.** `Overlay` and `Overlay::validate`; the `erase_*` functions; `SharingMeasure`.
- **Staging.** The terms of the experimental stage universe that `stage::normalize` reads.

## Expected features

- **The core arena outlives the domain arena.** A domain node names core nodes it does not own, so the caller never truncates the core arena below one, as [`arena`](src/arena.rs) states.
- **Shares placed where their legs are read.** Erasure copies a leg's indices to every occurrence unshifted, so a free index in a leg names the binder it reaches from the occurrence.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Term and unfolding faces, neutrals and spines | [`domain`](src/domain.rs) |
| The per-run arena | [`arena`](src/arena.rs) |
| Closure spaces | [`closure`](src/closure.rs) |
| Free indices | [`free`](src/free.rs) |
| The cached word | [`guard`](src/guard.rs) |
| Element identity | [`identity`](src/identity.rs) |
| The sharing overlay, erasure and the measure | [`overlay`](src/overlay.rs), [`measure`](src/measure.rs), [`spec`](src/spec.rs) |
| Strict stage terms | [`stage`](src/stage.rs) |

## References

- `vault:01a183de-4ab1-7660-a88a-04b9e8d318e3` — exemplar: the source page of Beniamino Accattoli. "Back to the Future of Lambda: Refreshing the Lambda-Calculus for the 21st Century." Habilitation, Institut Polytechnique de Paris, 2025. `hal:tel-05454767` — § 3.9's practical values, which the environment's value ids keep.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
