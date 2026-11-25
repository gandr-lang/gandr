# The hotpath verdict's report (#1468): the head's completed hotpath checks,
# `[{name, conclusion, summary}]`, read as the deltas `quenchant-gates
# obligations --hotpath` takes, `[{benchmark, before, after, regressed}]`,
# one per benchmark in name order.
#
# A failed check regressed. Its before and after are the first `a → b` span
# of its first site over threshold, falling back to the wall-time line. A
# passing check moved nothing past its policy: both read `within its policy`,
# so a verdict accepting growth on it reads unmoved.

def moved:
  [splits("\n")]
  | ((map(select(startswith("⚠️ ") and endswith(" · fails the check"))) | first)
      // (map(select(startswith("Wall time"))) | first)
      // "")
  | [match("`([^`]+?) → ([^`]+)`").captures[].string]
  | if length == 2 then {before: .[0], after: .[1]}
    else {before: "unreported", after: "unreported"} end;

unique_by(.name)
| map({benchmark: (.name | ltrimstr("hotpath / "))}
      + if .conclusion == "failure" then (.summary | moved) + {regressed: true}
        else {before: "within its policy", after: "within its policy", regressed: false} end)
