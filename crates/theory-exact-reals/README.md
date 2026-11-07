# gandr-theory-exact-reals

Canonical dyadics, explicitly oriented intervals and the scoped plan DAG: the finite arithmetic and the plan language that exact real computation reads.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Intervals](#intervals)
- [Plans and their bytes](#plans-and-their-bytes)
- [Certificates](#certificates)
- [Measurement](#measurement)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `Dyadic` holds a number `m · 2^e` in one canonical form. `NumericInterval` holds two bounds, each a dyadic or an infinity with a closure, and an explicit orientation. Every dyadic operation rounds to a requested precision toward the floor or the ceiling and reports whether it lost bits. Every interval operation rounds outward. `Plan` holds a computation over the reals as a finite DAG of real, open and domain nodes, and it has one canonical byte form. `approximate` encloses each real node of a validated plan, and it gives each open node a positive and a negative approximant. `check` replays a `Certificate` of a judgement with no search. `Dovetail` runs the refinement machine, and a `Cache` keeps the certificates that it writes. The crate is `no_std`.

**Why.** An exact real is an infinite object, and a program holds only finite approximations of it. Floating point rounds each result without a record, so an enclosure built from it is not sound. A dyadic is exact, a sum or a product of dyadics is a dyadic, and directed rounding keeps an enclosure sound while it bounds the bits. An interval alone is never evidence of truth. Truth needs a certificate that a checker replays with exact comparisons alone. The crate does not depend on the kernel, and no real number enters kernel conversion.

**How.** A nonzero mantissa is odd, and zero has the exponent zero, so the derived equality agrees with the exact order. A mantissa that fits an `i64` is inline, and the arithmetic on two inline values runs in `i128` with no allocation. A wider mantissa is a `num_bigint::BigInt`. The work of a sum is bounded by the operand widths and the precision, never by the gap between the exponents. The `dyadic` module documentation states the bound.

## References

- `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals design. Its domain is canonical dyadics with an inline path and oriented intervals as runtime approximants. Its plan language is a scoped DAG that keeps sharing as edges, and its firewall keeps all of it out of the kernel.
- `Taylor-2010-lambda_calculus_real_analysis` — exemplar: Taylor, _JLA_ 2:5, 2010, `doi:10.4115/jla.2010.2.5` — a real as a located cut.
- `Bauer-efficient_computation_dedekind_reals` — exemplar: Bauer, _CCA_, 2008 — the approximants of a formula.
- `Bauer-2009-dedekind_reals_abstract_stone_duality` — exemplar: Bauer and Taylor, _MSCS_ 19:4, 2009, `doi:10.1017/S0960129509007695` — Moore's arithmetic.
- `Escardó-2004-synthetic_topology_data_types_classical_spaces` — exemplar: Escardó, _ENTCS_ 87, 2004, `doi:10.1016/j.entcs.2004.09.017` — an open as a semidecidable property.
- `Bakke-2026-synthetic_sierpinski_cone` — newest: Bakke, Sterling, Williams and Ye, 2026, `arXiv:2605.00773` — the outcomes of a run as a cone.
- `Tarau-2008-functional_hitchhikers_guide_hereditarily_finite_sets_ackermann_encodings_pairing_functions` — exemplar: Tarau, 2008, `arXiv:0808.0754` — Ackermann's code and its successor.
- `Tarau-2008-ranking_catamorphisms_unranking_anamorphisms_hereditarily_finite_datatypes` — exemplar: Tarau, 2008, `arXiv:0808.0753` — the ranking fold and the unranking unfold.
- `vault:01a1b278-5641-7c20-95d3-093641459620` — exemplar: Cantone and Policriti, 2018, `arXiv:1806.09329` — the real code `R` and its successor.
- `Doré-2023-computing_spaces_type_theory` — exemplar: Doré, 2023 — graph matchings.
- `vault:01a1b278-54ca-7062-94f4-4c94748c971e` — exemplar: Paige and Tarjan, 1987, `doi:10.1137/0216062` — partition refinement.
- `vault:01a1b278-4fbc-7c31-a4f3-2a171b335796` — anchor: the fixed-point ledger.

## Provided features

- `Dyadic`: `new`, `From<i64>`, `ZERO` and `ONE`; `mantissa`, `exponent`, `width` and `sign`; `round`, `add`, `sub`, `mul` and `div` to a `Precision` toward a `Rounding`; the exact order through `Ord`; negation through `Neg`.
- `Rounded`: the rounded value and its `Exactness`, `Exact` or `Inexact`.
- `Precision`: the significant bits a result keeps, from one bit to the per-operation quota of 2^24 bits.
- `Exponent`, `BitWidth` and `Sign`: the nominal parts of a dyadic.
- `DyadicError`: an exponent outside the `i32` range, a precision outside its range, or a zero divisor.
- `NumericInterval`: `new`, `point`, `whole`, `lower`, `upper`, `orientation`, `dual`, `contains`, and the outward-rounded `add`, `sub`, `mul` and `div`.
- `Bound`, `Endpoint`, `Closure`, `Orientation` and `Containment`: the parts of an interval and the answer of a membership query.
- `IntervalError`: each malformed interval by name, a dual operand, a divisor that holds zero, and a failed endpoint operation.
- `Plan`: the canonical DAG; `root`, `node_count`, `node` and `nodes`; `encode` to `PlanBytes` and `decode` from `EncodedPlan`.
- `PlanBuilder`: `new`, `with_capacity`, `real`, `open`, `domain`, `sort_of`, `node_count`, and `finish` to the canonical plan of a `Root`.
- `Real`, `Open` and `Domain`: the node kinds of the three sorts, with `Cut` and `Quantifier`; `Node`, `Sort`, `Edge` and `Edges`.
- `NodeId`, `RealId`, `OpenId`, `DomainId`, `DeBruijn`, `Power`, `Evidence`, `EvidenceSlot` and `NodeCount`: the nominal parts of a plan.
- `PlanError` and `DecodeError`: each refused node, root and byte string by name.
- `validate` and `admit`: the total validation pass from bytes or from a plan, with its `Quotas`, its `EvidenceTable` of `Judgement`s, and a `ValidatedPlan` or a `Refusal` that names its `Site` and its `Check`.
- `Scope`, `Height` and `ByteLength`: whether an edge enters a binder, and the nominal parts of the quotas.
- `approximate`: the dual approximation of a validated plan at one precision, an `Approximation` that answers `enclosure` and `approximants` by node, each pair of approximants a `BilateralApprox` of a `PositiveApprox` and a `NegativeApprox`.
- `Certificate`, `Step`, `Side`, `StepId` and `FormatVersion`: a versioned certificate; `encode` to `CertificateBytes` and `decode` from `EncodedCertificate`.
- `check`: the replay within `CheckerQuotas`, a `Checked` `Conclusion` or a `CertificateRefusal` that names its `StepSite` and its `CertificateCheck`.
- `square_root`, `square_root_of_two`, `radicand` and `refine`: the registered cut schema, its recognition, and its refinement to a power of two with a certificate.
- `Obligation`, `Outcome` and `Dovetail`: the refinement machine's obligations, their five outcomes, and the scheduler that runs them in bounded quanta within a budget. `Dovetail::resume` reads its checkpoint back. The `semidecision`, `dovetail` and `bisection` module documentation states each.
- `Cache`, `CacheBound`, `Lookup`, `CacheRefusal` and `CacheTally`: the checked-result cache that `Dovetail::consult` reads and `Dovetail::record` fills. The `cache` module documentation states its key.
- `eliminate`, `Elimination`: cut elimination. The `elimination` module tables the rewrite.
- `Sets`, `SetId`, `Ackermann`, `Rank`, `code` and `CodeError`: a table of hereditarily finite sets with Tarau's fold, unfold and successor of Ackermann's code, and the real code of a set of rank at most 3 as a plan. The `ackermann` module documentation states which operations carry over to the real code.
- `PlanGraph`, `GraphBuilder`: a plan or a recursive system as a graph, its `Core`, its `MinimalForm` and `PlanKey`.

## Expected features

- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Round a sum on a grid of four bits, then enclose a product of two intervals.

```rust
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Exactness;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Rounding;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let four = Precision::try_from(4_u32)?;
    let sum = Dyadic::from(17_i64).add(&Dyadic::from(2_i64), four, Rounding::Ceiling)?;
    assert_eq!(sum.value(), &Dyadic::from(20_i64));
    assert_eq!(sum.exactness(), Exactness::Inexact);

    let unit = NumericInterval::new(Bound::closed(Dyadic::from(-1_i64)), Bound::closed(Dyadic::ONE), Orientation::Proper)?;
    let square = unit.mul(&unit, four)?;
    assert_eq!(square, unit);
    Ok(())
}
```

Run the tests, the enforcing twin, and the measurement:

```sh
cargo nextest run -p gandr-theory-exact-reals
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-exact-reals
cargo bench -p gandr-theory-exact-reals
```

## Intervals

A proper interval has its lower endpoint at or below its upper endpoint. A dual interval, the improper interval of Kaucher arithmetic, has them in the other order, and the orientation is a tag that nothing reorders. An infinite endpoint is open. Two equal endpoints make a point, and a point has two closed bounds. `NumericInterval::new` refuses every other form by name: `ClosedInfinity`, then `Reversed`, then `Empty`.

The arithmetic takes proper operands and refuses a dual one as `DualOperand`. A sum adds the lower bounds and the upper bounds, and a difference crosses them. A product chooses two or four endpoint products by the signs of its operands. The `interval` module documentation states when a product closes an endpoint and how zero meets an infinity.

## Plans and their bytes

A plan is a finite DAG of real, open and domain nodes. A cut and the two quantifiers each bind one real variable, and a bound variable names its binder by a de Bruijn index. A `PlanBuilder` holds a DAG by construction. `finish` brings the nodes that the root reaches to one canonical form, which holds each distinct subterm once in an order that depends on its structure alone. `Plan::encode` writes the canonical bytes, and `Plan::decode` accepts exactly those bytes and refuses every other input by name. The `plan` module documentation states the node kinds and the canonical walk, and the `codec` module documentation tables the byte layout.

## Certificates

A `Certificate` is a list of steps, each a primitive rule over the nodes of a plan and over earlier steps. The checker reads a certificate against a validated plan. It uses exact dyadic arithmetic and comparisons alone, and it never calls the interval code. It returns the last step's conclusion, or it refuses the first step that fails and names the check. The checker knows one cut schema, the square root of a positive dyadic, and it refuses a cut of any other shape as forged. `refine` narrows such a cut from its hull to a requested power of two with one step for each halving. The `certificate` and `schema` module documentation tables the rules and states the schema. A `Cache` keeps each certificate under the canonical bytes of the plan that its node roots. The checker replays each hit before the machine uses it.

## Measurement

`cargo bench -p gandr-theory-exact-reals` runs one bench for each stage. Each prints the median, the 99th percentile and the allocations per operation, and its module documentation lists its rows.

Stage C is the first release: a gandr program reaches the crate through `std.reals.Eff`. `cargo bench -p gandr-surface-dispatcher --bench reals` times that host against the bare crate. At the median, the host adds under 0.8 µs to `enclose` and under 0.2 µs to `decide`. To `admit` it adds 0.4 µs to 2.2 µs over the crate's own decode of the bytes.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
