# gandr-theory-exact-reals

Canonical dyadics, explicitly oriented intervals and the scoped plan DAG: the finite arithmetic and the plan language that exact real computation reads.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Rounding and its bound](#rounding-and-its-bound)
- [Intervals](#intervals)
- [Plans and their bytes](#plans-and-their-bytes)
- [Validation](#validation)
- [Dual approximation](#dual-approximation)
- [Certificates](#certificates)
- [Measurement](#measurement)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `Dyadic` holds a number `m · 2^e` in one canonical form. `NumericInterval` holds two bounds, each a dyadic or an infinity with a closure, and an explicit orientation. Every dyadic operation rounds to a requested precision toward the floor or the ceiling and reports whether it lost bits. Every interval operation rounds outward. `Plan` holds a computation over the reals as a finite DAG of real, open and domain nodes, and it has one canonical byte form. `approximate` encloses each real node of a validated plan, and it gives each open node a positive and a negative approximant. `check` replays a `Certificate` of a judgement with no search. `Dovetail` runs the refinement machine, and a `Cache` keeps the certificates that it writes. The crate is `no_std` and depends on `num-bigint`, `hashbrown`, `foldhash` and the specification facade.

**Why.** An exact real is an infinite object, and a program holds only finite approximations of it. Floating point rounds each result without a record, so an enclosure built from it is not sound. A dyadic is exact, a sum or a product of dyadics is a dyadic, and directed rounding keeps an enclosure sound while it bounds the bits. An interval alone is never evidence of truth. Truth needs a certificate that a checker replays with exact comparisons alone. The crate does not depend on the kernel, and no real number enters kernel conversion.

**How.** A nonzero mantissa is odd, and zero has the exponent zero, so the derived equality agrees with the exact order. A mantissa that fits an `i64` is inline, and the arithmetic on two inline values runs in `i128` with no allocation. A wider mantissa is a `num_bigint::BigInt`. The work of a sum is bounded by the operand widths and the precision, never by the gap between the exponents (see [Rounding and its bound](#rounding-and-its-bound)).

## References

- `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals design. Its domain is canonical dyadics with an inline path and oriented intervals as runtime approximants. Its plan language is a scoped DAG that keeps sharing as edges, and its firewall keeps all of it out of the kernel.

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

## Rounding and its bound

A result keeps at most `p` significant bits. Let `2^(k - 1) <= |r| < 2^k` for the exact result `r`. The floor is `floor(r / 2^(k - p)) · 2^(k - p)`, and the ceiling is the next point of that grid at or above `r`. A result that already fits is exact.

A sum aligns its operands on the lower exponent. When one operand lies far below the other, that alignment would cost the whole exponent gap. Let `big` be the operand with the higher top bit, and let `g` be the lower of its exponent and `top(big) - 1 - p`. The sum replaces an operand below `2^(g - 1)` by its sign times `2^(g - 2)`. Both sums then lie in one open cell of the result's grid, so the rounded result is the same. The aligned width stays below the operand widths plus `p + 3` bits.

A product forms the exact product of the two mantissas and rounds it once. Its work is one multiplication of the operand widths.

## Intervals

A proper interval has its lower endpoint at or below its upper endpoint. A dual interval, the improper interval of Kaucher arithmetic, has them in the other order, and the orientation is a tag that nothing reorders. An infinite endpoint is open. Two equal endpoints make a point, and a point has two closed bounds. `NumericInterval::new` refuses every other form by name: `ClosedInfinity`, then `Reversed`, then `Empty`.

The arithmetic takes proper operands and refuses a dual one as `DualOperand`. A sum adds the lower bounds and the upper bounds, and a difference crosses them. A product chooses its endpoint products by the signs of its operands: two products, or four when both operands straddle zero. The result closes an endpoint exactly when some pair of elements attains it and the rounding loses no bits. The product attains zero exactly when an operand contains zero, and zero times an infinity is zero at an endpoint, because every element of an interval is finite.

## Plans and their bytes

A plan is a finite DAG of real, open and domain nodes. A cut and the two quantifiers each bind one real variable, and a bound variable names its binder by a de Bruijn index. A `PlanBuilder` holds a DAG by construction. `finish` brings the nodes that the root reaches to one canonical form, which holds each distinct subterm once in an order that depends on its structure alone. `Plan::encode` writes the canonical bytes, and `Plan::decode` accepts exactly those bytes and refuses every other input by name. The `plan` module documentation states the node kinds and the canonical walk, and the `codec` module documentation tables the byte layout.

## Validation

A plan is untrusted input, so only a `ValidatedPlan` reaches the later stages. `validate` reads the bytes, and `admit` takes a plan in memory. A `Refusal` names the node that fails, or the input as a whole, and the `Check` that fails there. The pass is linear in the nodes and edges, and it never panics. The `validate` module documentation tables each check and states the two walks.

## Dual approximation

`approximate` gives each node of a validated plan an approximation at one precision. A real node gets an enclosure that holds its value, rounded outward. An open node gets a positive and a negative approximant, and each one is sound on its own. When neither proves its side, the proposition stays undecided at that precision, and the crate never reports it as false. The `approx` module documentation tables the approximation of each node kind and states the bounds of the pass.

## Certificates

A `Certificate` is a list of steps, each a primitive rule over the nodes of a plan and over earlier steps. The checker reads a certificate against a validated plan. It uses exact dyadic arithmetic and comparisons alone, and it never calls the interval code. It returns the last step's conclusion, or it refuses the first step that fails and names the check. The checker knows one cut schema, the square root of a positive dyadic, and it refuses a cut of any other shape as forged. `refine` narrows such a cut from its hull to a requested power of two with one step for each halving. The square root of two at a width of `2^-256` takes 257 steps. The `certificate` module documentation tables the rules, and the `schema` module documentation states the schema. A `Cache` keeps each certificate under the canonical bytes of the plan that its node roots. The checker replays each hit before the machine uses it.

## Measurement

`cargo bench -p gandr-theory-exact-reals` runs one bench for each stage of the crate: the arithmetic, the plan, the certificate, the scheduler, the quantifiers and the cache. Each bench prints the median, the 99th percentile and the allocations per operation, and its module documentation lists its rows.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
