# The witnesses `quenchant-gates` leaves unresolved, read against their
# tests' `cfg` (#4441). The listing holds the tests this host builds, so a
# witness gated off this host is absent from it.
#
# Input: {lines, tests, here, hosts}. `lines` is the gate's standard output,
# one diagnostic a line; `tests` is `tests.bash`'s array; `here` is this
# host's platform atoms and `hosts` each gate host's (`cfg.jq`, `hosts.json`).
#
# An `unresolved-witness` line names a site under `crates/<crate>/` and a
# path whose last segment is the test's name. The tests of that crate and
# name, each `cfg` read:
#   - one false here and true on a gate host resolves the witness as that
#     host's to run, a line in `resolved`;
#   - one false here and on every gate host refuses it, its line in
#     `refused` saying so;
#   - none, or one true here, leaves the line as the gate printed it.
# Every other line stays in `refused` as printed.
# Output: {resolved, refused}, each an array of lines.
include "cfg";

. as $input
| def built($host): all(.cfg[]; predicate | holds($host));
  def hosting($tests): [$input.hosts | to_entries[] | .key as $triple | .value as $atoms
      | select(any($tests[]; built($atoms))) | $triple];
  [.lines[] | select(length > 0)
   | . as $line
   | (capture("^(?<site>[^ ]*crates/(?<crate>[^/]+)/[^ ]*:[0-9]+): unresolved-witness \\[[^]]*\\] `(?<path>[^`]+)`") // null) as $witness
   | if $witness == null then {refused: $line}
     else
       ($witness.path | sub(".*::"; "")) as $name
       | [$input.tests[] | select(.crate == $witness.crate and .name == $name)] as $named
       | if ($named | length) == 0 or any($named[]; built($input.here)) then {refused: $line}
         else
           ($named | map(.cfg | map("#[cfg(\(.))]") | join(" ")) | unique | join(", ")) as $gates
           | hosting($named) as $hosts
           | if ($hosts | length) > 0 then
               {resolved: "\($witness.site): the witness `\($witness.path)` is left to \($hosts | join(" and ")) to run: \($gates) builds it there, not here"}
             else
               {refused: "\($witness.site): unresolved-witness `\($witness.path)`: \($gates) builds it on no host the gate runs on (\($input.hosts | keys_unsorted | join(", ")))"}
             end
         end
     end]
  | {resolved: map(.resolved // empty), refused: map(.refused // empty)}
