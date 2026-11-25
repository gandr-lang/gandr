# gandr-core-unify

Contextual metavariables over the core, and the unifier that solves them where an equation forces a most general solution and postpones every other equation in one store.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [License](#license)

## Synopsis

**What.** A metavariable is a value hole a metacontext declares, with the binders its context holds. `solve` takes equations between core values, value types and computation types, each posed under some binders, binds a metavariable only where an equation forces it, and postpones what it cannot answer most generally.

**Why.** An implicit argument left out of a call is found by the equations its parameters' types pose against its explicit arguments. A binding the equations do not force is a guess, and a guess surfaces later somewhere else. An equation that cannot be answered yet may be answerable once another equation is solved, so it waits rather than stopping the run, and whatever still waits when the declaration ends is refused there by name.

**How.** Rigid sides sharing a head decompose. Two introduction forms or two type formers with different heads refute, as does a metavariable occurring strongly rigidly in its candidate solution; nothing else does, since a neutral, a binder read off a carried support and a flexible occurrence can each be closed by a later instantiation or a singleton type. A metavariable against a value is bound to it, and the decode of one against a type to the type's quote. A solution naming no binder outside its context is lowered into the context by a root relocation. Every other equation goes into the metacontext's store with its reason and the unsolved metavariables that block it, and is posed again when one of them is bound, so the run's answer does not depend on the order of its equations.

The crate root's rustdoc carries the worked example and the boundaries.

## References

- Dale Miller, "A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification", _Journal of Logic and Computation_ 1(4), 1991, [doi:10.1093/logcom/1.4.497](https://doi.org/10.1093/logcom/1.4.497): the pattern fragment whose forced solutions are most general.
- Andreas Abel and Brigitte Pientka, "Higher-Order Dynamic Pattern Unification for Dependent Types and Records", _TLCA 2011_, LNCS 6690, [doi:10.1007/978-3-642-21691-6_5](https://doi.org/10.1007/978-3-642-21691-6_5): contextual metavariables, pruning and the occurs check read through solutions.
- Conor McBride, "Everybody's Got To Be Somewhere", _MSFP 2018_, EPTCS 275, [doi:10.4204/EPTCS.275.6](https://doi.org/10.4204/EPTCS.275.6): the support carried on every node that scopes a solution.
- Jesper Cockx and Dominique Devriese, "Proof-Relevant Unification: Dependent Pattern Matching with Only the Axioms of Your Type Theory", _Journal of Functional Programming_ 28, 2018, [doi:10.1017/S095679681800014X](https://doi.org/10.1017/S095679681800014X): the conflict and cycle rules, the only refutations.
- Andrew Slattery and Jonathan Sterling, "Bidirectional Elaborators à la Carte", 2026, [arXiv:2607.09564](https://arxiv.org/abs/2607.09564): postponement as partiality over one dominance, whose constraint actions commute.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: a composite is a former whose cells and fold the solver reads as its children.

## Provided features

- `Metas`, `MetaId`, `MetaCount`, `declaration`, `meta_lookup`: the metacontext — a hole declared once with its context's binders, its solution once bound, and the store of equations that wait.
- `solve`, `Equation`, `Side`, `Verdict`: equations decided in order, values, value types and computation types alike, under the binders each is posed at; a dependent pair's second factor, a dependent function's codomain and a static lambda's body one binder deeper.
- `Refutation`: a clash of introduction forms or type formers, a strongly rigid occurrence of a metavariable in its own solution.
- `Postponed`, `Reason`: an equation that waits, why, and the metavariables whose solution poses it again — a definition, a gradual side, an applied metavariable, an undecomposed former, a neutral against a rigid side, decodes at two levels, a metavariable of a wider context, a binder outside the context, a flexible occurrence, a linear variable.

## Expected features

- Pattern inversion: a metavariable applied to distinct variables, solved by abstracting over them.
- Pruning: a solution's metavariable of a wider context narrowed rather than postponed.
- The elaborator's spine pass: an omitted implicit argument becomes a metavariable at a fully applied head, the call is checked with its solutions written, and what still waits at the declaration's end is refused by name.

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
