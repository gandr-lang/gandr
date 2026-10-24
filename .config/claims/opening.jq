# Whether `pr:open` opens a body (#2462): the refusal to print, or nothing.
#
# Input:
#   branch   the branch being opened, `<lane>-<n>-<slug>` when it works an
#            issue
#   body     the body file's text
#
# A merge takes the claim off what the body works (`decide.jq`), so the body
# must name it: a branch that carries an issue number needs `Advances #n` or
# a closing keyword for that issue, and a branch with none needs one such
# line for some issue, the issue the change advances.

include "targets";

(.body | targets(working)) as $worked
| (.branch | capture("^[a-z]+-(?<n>[0-9]+)(-|$)").n // null | if . == null then null else tonumber end) as $n
| if $n != null then
    if ($worked | index($n)) then empty
    else "the body names no `Advances` or `Closes` line for #\($n), the issue `\(.branch)` names: add `Advances #\($n)` for a slice, or `Closes #\($n)` if it finishes the issue, then run `pr:open` again"
    end
  elif ($worked | length) > 0 then empty
  else "the body names no issue it works: add `Advances #n` for the issue the change advances, or `Closes #n` for one it finishes, then run `pr:open` again"
  end
