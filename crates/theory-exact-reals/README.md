# gandr-theory-exact-reals

Canonical dyadics and explicitly oriented intervals: the finite arithmetic that exact real computation reads.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Rounding and its bound](#rounding-and-its-bound)
- [Intervals](#intervals)
- [Measurement](#measurement)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `Dyadic` holds a number `m · 2^e` in one canonical form. `NumericInterval` holds two bounds, each a dyadic or an infinity with a closure, and an explicit orientation. Every dyadic operation rounds to a requested precision toward the floor or the ceiling and reports whether it lost bits. Every interval operation rounds outward. The crate is `no_std` and depends only on the `num-bigint` carrier and the specification facade.

**Why.** An exact real is an infinite object, and a program holds only finite approximations of it. Floating point rounds each result without a record, so an enclosure built from it is not sound. A dyadic is exact, a sum or a product of dyadics is a dyadic, and directed rounding keeps an enclosure sound while it bounds the bits. The refinement machine of the exact-reals design computes with these values and emits certificates that a checker replays. An interval is an approximant and never evidence of truth. The crate does not depend on the kernel, and no real number enters kernel conversion.

**How.** A nonzero mantissa is odd, and zero has the exponent zero, so the derived equality agrees with the exact order. A mantissa that fits an `i64` is inline, and the arithmetic on two inline values runs in `i128` with no allocation. A wider mantissa is a `num_bigint::BigInt`. The work of a sum is bounded by the operand widths and the precision, never by the gap between the exponents (see [Rounding and its bound](#rounding-and-its-bound)).

## References

- `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals design. Its domain is canonical dyadics with an inline path and oriented intervals as runtime approximants, and its firewall keeps all of it out of the kernel.

## Provided features

- `Dyadic`: `new`, `From<i64>`, `ZERO` and `ONE`; `mantissa`, `exponent`, `width` and `sign`; `round`, `add`, `sub` and `mul` to a `Precision` toward a `Rounding`; the exact order through `Ord`; negation through `Neg`.
- `Rounded`: the rounded value and its `Exactness`, `Exact` or `Inexact`.
- `Precision`: the significant bits a result keeps, from one bit to the per-operation quota of 2^24 bits.
- `Exponent`, `BitWidth` and `Sign`: the nominal parts of a dyadic.
- `DyadicError`: an exponent outside the `i32` range, or a precision outside its range.
- `NumericInterval`: `new`, `point`, `lower`, `upper`, `orientation`, `dual`, `contains`, and the outward-rounded `add`, `sub` and `mul`.
- `Bound`, `Endpoint`, `Closure`, `Orientation` and `Containment`: the parts of an interval and the answer of a membership query.
- `IntervalError`: each malformed interval by name, a dual operand, and a failed endpoint operation.

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

## Measurement

`cargo bench -p gandr-theory-exact-reals` times each operation at operand widths of 63, 64, 256 and 4096 bits, and prints the median, the 99th percentile and the allocations per operation. The bench's module documentation lists the rows.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
