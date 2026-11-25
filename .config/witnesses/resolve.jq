# The witnesses `quenchant-gates` leaves unresolved, read against their
# tests' `cfg` (#4441) and against the packages that depend on their owner
# (#7039). The listing holds the tests this host builds, so a witness gated
# off this host is absent from it.
#
# Input: {lines, tests, here, hosts, depends, listed}. `lines` is the gate's
# standard output, one diagnostic a line; `tests` is `tests.bash`'s array;
# `here` is this host's platform atoms and `hosts` each gate host's (`cfg.jq`,
# `hosts.json`). `depends` maps each workspace package to the workspace
# packages it depends on, by a normal, a dev or a build dependency. `listed`
# maps each listed package to its aliases, each with the count of the package's
# targets that list it; an alias is spelled as a witness spells it.
#
# An `unresolved-witness` line names a site under `crates/<crate>/`, its owner
# package in brackets, and a path whose last segment is the test's name.
#
# A path whose first segment is a workspace package P other than the owner
# names a test of P (#7039). It resolves, a line in `resolved`, when P depends
# on the owner and exactly one target of P lists the rest of the path.
# Otherwise its line in `refused` says which of these fails.
#
# Any other path is read against the tests of the site's crate and name, each
# `cfg` read:
#   - one false here and true on a gate host resolves the witness as that
#     host's to run, a line in `resolved`;
#   - one false here and on every gate host refuses it, its line in
#     `refused` saying so;
#   - none, or one true here, leaves the line as the gate printed it.
# Every other line stays in `refused` as printed.
# Output: {resolved, refused}, each an array of lines.
include "cfg";

. as $input
| ($input.depends // {}) as $depends
| ($input.listed // {}) as $listed
| def built($host): all(.cfg[]; predicate | holds($host));
  def hosting($tests): [$input.hosts | to_entries[] | .key as $triple | .value as $atoms
      | select(any($tests[]; built($atoms))) | $triple];
  def package_witness($witness):
    ($witness.path | split("::")) as $segments
    | $segments[0] as $package
    | ($segments[1:] | join("::")) as $rest
    | ($listed[$package][$rest] // 0) as $targets
    | if ($depends[$package] | index($witness.owner)) == null then
        {refused: "\($witness.site): unresolved-witness `\($witness.path)`: \($package) does not depend on \($witness.owner), so no test of it witnesses an item of \($witness.owner)"}
      elif ($listed | has($package)) | not then
        {refused: "\($witness.site): unresolved-witness `\($witness.path)`: the listings hold no test of \($package); list \($package) beside \($witness.owner)"}
      elif $targets == 1 then
        {resolved: "\($witness.site): the witness `\($witness.path)` runs in \($package), which depends on \($witness.owner)"}
      elif $targets == 0 then
        {refused: "\($witness.site): unresolved-witness `\($witness.path)`: no target of \($package) runs `\($rest)`"}
      else
        {refused: "\($witness.site): ambiguous-witness `\($witness.path)`: \($targets) targets of \($package) run `\($rest)`; name the one a reviewer should watch fail"}
      end;
  [.lines[] | select(length > 0)
   | . as $line
   | (capture("^(?<site>[^ ]*crates/(?<crate>[^/]+)/[^ ]*:[0-9]+): unresolved-witness \\[(?<owner>[^]]*)\\] `(?<path>[^`]+)`") // null) as $witness
   | if $witness == null then {refused: $line}
     elif ($witness.path | split("::")[0]) as $package | $depends | has($package) and $package != $witness.owner then
       package_witness($witness)
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
