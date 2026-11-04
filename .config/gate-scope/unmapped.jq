# What keeps `table.json` true to the checks it scopes (#4911): a check that
# builds or runs the toolchain sits in a group, so a workflow change never runs
# it, and every check a group names exists. A heavy check is one whose script
# runs `cargo` beyond `cargo metadata`, the gate binary `quenchant-gates`, or
# the extension's `aube` or `node`, or one that depends on a grouped check. The
# table's `light` list names a heavy check that runs on every change anyway.
#
# A check that builds `GATE_SCOPE` under `--cfg anodized_panic` unifies the
# features over the whole workspace. A scope that keeps no member using
# `anodized` otherwise builds `quenchant-anodized` without its feature under
# the cfg, and its build stops.
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
  (.tasks[]
    | select(any(.env[]?; test("^RUSTFLAGS=.*--cfg anodized_panic")))
    | select(.run | tostring | test("GATE_SCOPE"))
    | select((.run | tostring | test("resolver\\.feature-unification=\\\\?\"workspace\\\\?\""))
        and any(.env[]?; . == "CARGO_UNSTABLE_FEATURE_UNIFICATION=true") | not)
    | "\(.name): it builds GATE_SCOPE under --cfg anodized_panic without the workspace feature unification: set CARGO_UNSTABLE_FEATURE_UNIFICATION=true and pass --config 'resolver.feature-unification=\"workspace\"'")
