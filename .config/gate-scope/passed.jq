# Whether a gate passed on a head (#5076). On 2026-11-04 a pull request
# opened on a head that no gate passed, and CI found four prose findings
# that `mise run check` finds. So `pr:open` and `pr:land` read the records
# that `passed.bash` writes when a gate passes, and gate a head without one.
#
# A record is keyed by the tree, not by the commit. A rebase that changes
# nothing, or a reworded message, keeps the tree, so its record still counts.
# A record counts only for the checks its gate ran: when the head's change
# selects a check that no gate on its tree ran, the head is refused. The
# checks of all the records on a tree count together, as each passed there.
#
# Input:
#   tree      the head's tree
#   selected  the checks the head's change selects (`select.jq`)
#   records   the records of passed gates, each {tree, commit, gate, checks, tasks}
#
# Output: {accepted, missing}. `missing` lists the selected checks that no
# gate on the tree ran.

.tree as $tree
| [.records[] | select(.tree == $tree)] as $passed
| ([$passed[].checks[]] | unique) as $ran
| [.selected[] | select(IN($ran[]) | not)] as $missing
| {accepted: (($passed | length) > 0 and ($missing | length) == 0), missing: $missing}
