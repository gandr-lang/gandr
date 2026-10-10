# The strict stage producer

The one-subject page for the `stage` module of `gandr-core-nbe`: the strict meta-level producer over the kernel's auxiliary stage language, what it reduces and what it leaves residual, and the witnesses that measure it. The crate's [README](../README.md) states the rest of the normalizer.

<!-- toc -->

- [Experimental stage normalization](#experimental-stage-normalization)

<!-- tocstop -->

## Experimental stage normalization

`stage::normalize` evaluates the meta level of the auxiliary [stage language](../../kernel-core/docs/staging.md#experimental-stage-universe) and leaves the object program as written. Typing determines the stage through the universe index. Every meta contraction and congruence equation is independently replayed by the kernel before the residual is admitted as object code.

The producer uses a postorder worklist and capture-avoiding substitution. It reduces meta beta, outer natural iteration, outer identity elimination and both quote/splice round trips, including beneath object binders. Object beta, iteration, elimination and multiplication remain residual. In particular, `(λx. x * x) e` retains its application and sharing instead of duplicating `e`.

**Decision.** Strict two-level staging preserves the source program's object computation and cost model. Full conversion normalization is the alternative: it also contracts object redexes, changing sharing and when work occurs. Revisit this choice for a staged program whose cost the user cannot predict from the source under the strict rule. The stage discipline follows András Kovács, _Staged Compilation with Two-Level Type Theory_, ICFP 2022, §2, [doi:10.1145/3547641](https://doi.org/10.1145/3547641); kernel replay additionally checks the proposed staging equations.

`stage::power` builds `λn. λx. iter n <1> (λp.<~x * ~p>)`, of type `Nat_outer → Lift Nat_inner → Lift Nat_inner`. It threads quoted input at the meta level and carries quoted naturals through iteration. Specialization `<λx. ~(pow n <x>)>` yields `λx. x * (x * (… * 1))` without creating object redexes. Witnesses compare exponents zero through eight at inputs zero through five with checked integer exponentiation and independently execute the ordinarily admitted CBPV body. The function-valued-accumulator encoding `λn. iter n <λx.1> (λp.<λx. x * (~p) x>)` witnesses the complementary case: its object applications survive.

The equation census for those exponents uses fresh arenas and includes every replayed equation, including congruence:

| Exponent `n` | Replayed equations | Distinct shapes | Largest family |
| ------------ | -----------------: | --------------: | -------------: |
| 0 | 9 | 9 | 1 |
| 1 | 18 | 13 | 3 |
| 2–8 | `8n + 10` | 14 | `2n + 1` |

Shapes retain the rule and classifier. Beta uses capture-avoiding substitution; congruence retains parent constructors and non-child payloads, replacing immediate children by holes shared according to structural equality across both endpoints. Arena sharing does not affect that equality. Splice-of-quote is the largest family for positive exponents. These are observations over the stated range, not serialized sizes, a compression result or a performance bound.

The existing glued domain does not interpret this auxiliary vocabulary. Explicit per-step replay keeps the producer outside the trusted boundary without introducing a second semantic domain; native formers are the condition for reusing the glued evaluator. Residual extraction supports closed first-order natural functions, rather than general closure conversion.
