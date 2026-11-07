# Which remote branches the landing watcher deletes (#6185). GitHub deletes
# the head branch of a merged pull request, but not while another open pull
# request has that branch as its base: a stack member below the top stays.
# A branch a seat pushed with no pull request stays too, after its commits
# land through another branch. The watcher deletes such a branch once each of
# its commits stands on the trunk, read by subject as `wt:sweep` reads a
# branch (`own_commits`, #4227). `branches.jq` lists every branch no unit
# accounts for, landed or not, for a seat to delete by hand (#2539).
#
# Input: an object with
#   kept    the branches that outlive every unit (`kept_branches` of
#           `.config/pr-stack/trunk.bash`);
#   used    the head and base of each open pull request, held ones included;
#   heads   the remote heads, each `{name, oid, commits, ahead}`: `commits`
#           the `+` lines `git cherry origin/<trunk> <oid>` lists, each
#           `{subject, on_trunk}`, or null when the head's commits could not
#           be read; `ahead` the count of `git rev-list origin/<trunk>..<oid>`.
#
# Output: an array of `{name, oid, action, reason}`, one per head, `action`
# `delete` or `keep`. A merge queue branch (`gh-readonly-queue/`) stays:
# GitHub makes and deletes it, and the queue reads it while it lives.
.kept as $kept
| .used as $used
| [
    .heads[]
    | .name as $name
    | {name, oid} + (
      if any($kept[]; . == $name) then {action: "keep", reason: "a branch that outlives every unit"}
      elif ($name | startswith("gh-readonly-queue/")) then {action: "keep", reason: "a merge queue branch, which GitHub deletes"}
      elif any($used[]; . == $name) then {action: "keep", reason: "the head or base of an open pull request"}
      elif .commits == null then {action: "keep", reason: "its commits could not be read"}
      elif (.commits | length) > 0 and all(.commits[]; .on_trunk) then {action: "delete", reason: "its commits stand on the trunk"}
      elif (.commits | length) > 0 then {action: "keep", reason: "a commit is not on the trunk"}
      elif (.ahead // 0) > 0 then {action: "delete", reason: "each commit's patch stands on the trunk"}
      else {action: "delete", reason: "it holds no commit off the trunk"}
      end
    )
  ]
