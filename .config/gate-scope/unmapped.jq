# What keeps `table.json` true to the checks that it scopes. A check that
# builds or runs the toolchain sits in a group, so a workflow change never
# runs it. Each check that a group, the `landing` list or the `gate` list
# names exists.
# - see: #4911
#
# A heavy check runs `cargo` beyond `cargo metadata` in its script. The gate
# binary `quenchant-gates` makes a check heavy too. So do the extension's
# `aube` and `node`, and a dependency on a grouped check. The table's `light`
# list names a heavy check that runs on every change anyway.
#
# A check that builds `GATE_SCOPE` under `--cfg anodized_panic`, through
# `.config/mise/enforcing`, unifies the features over the whole workspace. A
# scope that keeps no member using `anodized` otherwise builds
# `quenchant-anodized` without its feature under the cfg, and its build stops.
#
# Input:
#   tasks  each `check:*` task as `mise tasks ls --json` lists it: name, run,
#          depends and env
#   table  the table to read; absent, `table.json`
#
# Output: one finding per line, nothing when the table holds.

import "table" as $table;

(.table // $table::table[0]) as $table
| ([$table.groups[][]] | unique) as $grouped
| ([.tasks[].name]) as $names
| (.tasks[]
    | select(.name | IN($grouped[]) or IN(($table.light // [])[]) | not)
    | select((.run | tostring | test("cargo (?!metadata)|quenchant-gates|\\baube |\\bnode "))
        or any(.depends[]?; IN($grouped[])))
    | "\(.name): it builds or runs the toolchain and sits in no group of .config/gate-scope/table.json"),
  ($table.groups | to_entries[] | .key as $group | .value[]
    | select(IN($names[]) | not)
    | "\($group): it names \(.), which is no check task"),
  (($table.landing // [])[]
    | select(IN($names[]) | not)
    | "landing: it names \(.), which is no check task"),
  (($table.gate // [])[]
    | select(IN($names[]) | not)
    | "gate: it names \(.), which is no check task"),
  (.tasks[]
    | select(.run | tostring | test("\\.config/mise/enforcing\\b"))
    | select(.run | tostring | test("GATE_SCOPE"))
    | select((.run | tostring | test("resolver\\.feature-unification=\\\\?\"workspace\\\\?\""))
        and any(.env[]?; . == "CARGO_UNSTABLE_FEATURE_UNIFICATION=true") | not)
    | "\(.name): it builds GATE_SCOPE under --cfg anodized_panic without the workspace feature unification: set CARGO_UNSTABLE_FEATURE_UNIFICATION=true and pass --config 'resolver.feature-unification=\"workspace\"'")
