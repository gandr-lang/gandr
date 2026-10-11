# Recursive data and the structural fixpoint

How `gandr-kernel-core` admits a data declaration that names its own family, types the fixpoint, replays its structural-descent claim and unfolds it during conversion replay. The crate's [README](../README.md) states the rest of the crate.

<!-- toc -->
- [References](#references)
- [Strict positivity and uniformity, by name](#strict-positivity-and-uniformity-by-name)
- [The fixpoint and its evidence](#the-fixpoint-and-its-evidence)
- [The conversion gate](#the-conversion-gate)
- [The decision](#the-decision)
- [Witnesses](#witnesses)
<!-- tocstop -->

## References

- Peter Dybjer. "Inductive families." _Formal Aspects of Computing_ 6 (1994), 440–465. <https://doi.org/10.1007/BF01211308> — strictly positive, generalised induction and the formation criteria the occurrence walk enforces.
- Thierry Coquand and Christine Paulin. "Inductively defined types." _COLOG-88_, LNCS 417, Springer (1990), 50–66. <https://doi.org/10.1007/3-540-52335-9_47> — strict positivity with uniform parameters.
- Eduardo Giménez. "Structural recursive definitions in type theory." _ICALP 1998_, LNCS 1443, Springer (1998). <https://doi.org/10.1007/BFb0055070> — the guarded fixpoint whose recursive calls stand at subterms of the scrutinised constructor.
- Ambrus Kaposi and András Kovács. "Signatures and Induction Principles for Higher Inductive-Inductive Types." _Logical Methods in Computer Science_ 16(1) (2020). <https://doi.org/10.23638/LMCS-16(1:10)2020> — signatures as a description theory, the route not taken inside the kernel.

## Strict positivity and uniformity, by name

A data declaration may name its own family in a constructor field. Before formation, an occurrence walk reads every parameter and field. The family may stand only as a whole field or as the result of a function field, `U (Π ȳ. F (T p̄))`, applied to exactly its parameter variables in telescope order. The walk refuses by name, at the parameter or field site:

- an occurrence under a function's domain, `NegativeOccurrence`;
- one inside another family's arguments or a field-local positive former, `NestedOccurrence`;
- one inside a term a type reads, or in the parameter telescope, `IndexOccurrence`;
- the family applied to any other arguments, `NonUniformOccurrence`;
- a field naming a position after its own block, `CrossBlockReference`.

Formation then reads the self occurrence through the block's own signature. Every other reference still sees only the admitted prefix.

## The fixpoint and its evidence

`fix x. M` checks at every computation type `C`: its body checks at `C` with `x : U C` bound innermost. Recursion goes through that binder, so a body never names its own admission position and the admitted prefix stays the only visible signature table.

The evidence is `Partial`, no claim, or `StructuralDescent`. A structural-descent claim says the body is a lambda whose body is a case on that lambda's variable, that each branch opens exactly its constructor's fields, and that every self occurrence is the head of a call whose argument is a field of the scrutinised constructor or a function field's result. Admission replays the claim and refuses a failed one as `DescentNotReplayed` carrying its `DescentRefusal`. A partial fixpoint is admitted at any computation type, including a loop at `F 1`.

## The conversion gate

Conversion replay unfolds a structural-descent fixpoint only where it is applied to a constructor, `(fix x. M) (c v̄) ⇝ M[thunk (fix x. M)/x] (c v̄)`. A partial fixpoint at that gate declines as `ReplayDecline::PartialFixpoint`, so a trace that needs a partial unfolding is never certified. Two stuck fixpoints compare by their bodies under one self variable, whatever their evidence.

## The decision

**Choice.** Strict positivity and parameter uniformity, checked on the native declaration, and one guarded fixpoint whose descent claim the kernel replays, rather than a primitive recursor per declaration. The trusted base gains one former and one replay check; every eliminator is an ordinary derived declaration that the kernel re-checks.

**Alternatives.** A primitive recursor per declaration adds a generated rule per signature to the trusted base. A description universe decoded at admission gives up native nominal identity inside the kernel. A size-based termination checker needs sized types the kernel does not have.

**Reversal.** Mutual blocks, indexed families, nested occurrences, or descent through a non-field such as a measure each need their own formation or replay rule. A measured recursion arrives as new evidence, not as a widened structural check.

## Witnesses

`recursive_data::recursive_data::recursive_blocks_are_admitted`, `recursive_data::recursive_data::occurrences_are_refused_by_name`, `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`, `recursive_data::recursive_data::derived_eliminators_are_admitted`, `recursive_data::recursive_data::a_fixpoint_computes_at_a_constructor_and_replays` and `recursive_data::recursive_data::a_partial_fixpoint_declines_at_its_gate`.
