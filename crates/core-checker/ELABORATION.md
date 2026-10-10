# Elaboration suspends on owed code constants

`elaboration::Session` is the term-producing path for variables, application, lambda, both conversion bridges, thunk, force, return, non-dependent bind and decodes of code constants. Its equational specification is Andrew Slattery and Jonathan Sterling, _Bidirectional Elaborators à la Carte_, arXiv:2607.09564v2, §§3–6. The Rust path reuses the iterative judgement and conversion rules; the kernel independently certifies emitted terms.

## Output and suspension

| Outcome | Payload and meaning |
| ------- | ------------------- |
| `Checked(Output)` | Formed value type and emitted core `ValueId`; computations cross as thunks. Runtime constructors remain unchanged. Universe transport is explicit quoted lifted syntax, recorded per occurrence so shared code can inhabit different universes at different uses. Unchanged subterms retain their ids. |
| `Owed` | The declaration itself lacks its body; its formed signature supplies a rigid constant and a kernel axiom. |
| `Suspended` | Source declaration, sorted unique residual equations, their owed-hole blocker set at creation, and earlier suspended declaration dependencies. No conditional body is exported or installed as a definition. |
| `Refused` | An ordinary checker refusal, including a refused subterm or dependency; never a certificate that a unification sieve is empty. |

Only a bare owed code constant opposite a constructor-headed type becomes a residual equation, in either orientation and beneath matching type constructors. Spined holes and flex–flex equations retain the ordinary checker result. A residual records what a fill must settle; it neither solves a hole nor certifies a clash. Unifier-produced solutions and certified emptiness are separate work. The ordinary checking entry points retain rigid-hole conversion.

## Substitution and resumption

`fill` checks a proposed body against the owed declaration's original signature and admission prefix. Only a checked filling is installed. Other entries remain unchanged, including checked terms whose types mention the hole. The session's exclusive arena borrow prevents external truncation or body edits from posing as substitutions.

A filling can depend on an earlier declaration still awaiting resumption. Its suspension retains that prerequisite and its recorded equations, but the hole blocker set includes only heads still owed when the new record is created. An empty hole blocker set with suspended prerequisites requests their resumption; it does not publish conditional output.

`resume` schedules a suspended target and its suspended prerequisites in admission order, rebuilding each prefix by adopting cached answers. It rejudges suspended declarations, not completed dependents. The continuation granularity is one declaration. `Entry::judgements` counts actual declaration judgements, excluding adoption and independent kernel replay. `readmit` exports only settled emitted terms, owed axioms and refusal marks; it uses no implicit-lift side table.

| Route property | Calculus law | Witness in `elaboration::tests` |
| -------------- | ------------ | ------------------------------- |
| Kernel readmission | Typed combinators, Construction 4.3 | `every_fixture_the_checker_accepts_is_readmitted` |
| Equal expected types give equal output | `conv`, Construction 4.3; judgemental invariance, §4.5 | `judgemental_equality_leaves_output_unchanged` |
| Owed conversion suspends | Exegesis 6.6, suspension versus failure | `owed_conversion_suspends` |
| Resume agrees with a filled batch | Theorem 5.1, multilinearity and substitution naturality | `incremental_equals_from_scratch` |
| Resumption order is irrelevant | Lemma 3.19, commutative partiality | `resumptions_commute` |
| Success survives filling without rejudgement | Exegesis 6.6, success closed under substitution | `checked_success_is_stable_without_rejudgement` |
| A refused subterm refuses its declaration | Corollary 5.2, multistrictness | `refused_subterms_refuse_the_declaration` |

The readmission witness extends the checker's generated fixture families to emitted terms. Directed witnesses cover both bridges, bind under a binder, dependent suspension scheduling, nested and shared universe transports, invalid fills, and the bare-flex boundary. These are executable witnesses over the named fragment, not a formal dominance construction or a universal proof. Output identity and artifact equality witness the relational laws separately from kernel typing; the stable-success witness also observes the judgement count.

The alternatives are a second elaboration checker, which duplicates the rule semantics; interpreting the shallow combinator embedding directly, which needs an extensional metalanguage with equality reflection; and treating every stuck comparison as failure, which violates the suspension law. A private residual collector plus occurrence-specific term emission keeps one rule machine and a separate certification boundary. Declaration continuations give way to saved machine frames when measured resumption workloads justify retaining partial within-declaration work. General unification replaces the bare-flex boundary when it supplies solutions, postponement reasons and replayable clash evidence.
