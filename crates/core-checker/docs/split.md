# Products and their split

How `gandr-core-checker` judges a product split and hands it to the kernel. The crate's [README](../README.md) states the rest of the crate; the core vocabulary's [n-ary products section](../../core-term/README.md#n-ary-products-and-sums) states the former.

<!-- toc -->
- [A split only checks](#a-split-only-checks)
- [A split crosses as its projection binds](#a-split-crosses-as-its-projection-binds)
<!-- tocstop -->

## A split only checks

A split's scrutinee synthesises a product of exactly the split's arity, the unit for a split of none, and its body checks against the expected type under one binder per component, component zero outermost, each typed by its component shifted past the binders before it; the expected type is shifted past all of them. A split of another arity or of anything but a product is a `ShapeMismatch` wanting a product, at the scrutinee. A split in synthesis position is `NotSynthesisable`, the checking form `CheckingForm::Split`: its body's type may read the components it binds, and strengthening them out is the bind's rule, not this one. `judgement::tests::a_split_binds_every_component_of_its_product` asserts each arm.

## A split crosses as its projection binds

The kernel has no split. Erasure mints the split's reduct into the core arena and erases it in the split's place: one bind per component, component zero outermost, each of the projection of the scrutinee shifted past the binds before it, ending in the body, so the body reads the components at the indices the split gave them and a split of no components crosses as its body. The kernel then judges the projections and binds by its own rules. `native_formers::native_formers::a_split_crosses_as_its_projection_binds` crosses a split of a variable pair, which a wrong shift would project from its first component, a split of a closed triple and a split of the unit.

The alternatives were a kernel split, which widens the trusted base by a binder former the projection already expresses, and refusing the split at the bridge, which leaves every program that discards a unit uncrossed. A split of a neutral compares in the normaliser by its arity and bodies, and those verdicts are not replayed: the kernel never sees a split, only the binds it judges itself. The choice reverses if the kernel gains a split of its own.
