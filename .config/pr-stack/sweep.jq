# What `wt:sweep` does with each worktree of the clone: a worktree is
# removed when its branch has landed, mechanically, never because a seat
# remembered to, and released when it stands idle for a day (#6183). The
# sweep makes no safety check of its own: `wt remove` and `git worktree
# remove` refuse a dirty or otherwise unsafe tree, and the sweep reports the
# refusal and keeps the tree. The predicates it keeps are the landing itself
# and a live `pr:watch` inside the tree, which runs its merge steps there
# after the landing (#3798).
#
# Input: an array of worktrees, each an object with
#   path      the worktree's path;
#   branch    its branch, or null when detached;
#   primary   the clone's primary worktree;
#   cwd       the caller's own worktree;
#   merged    Worktrunk reads the branch integrated into the default branch
#             and the head it read beside that reason is off origin/main's
#             first-parent line: a landed branch, never one cut from main and
#             not yet committed to. Both come from one `wt list` snapshot;
#   moved     the worktree's head is no longer the one Worktrunk judged: a
#             commit landed after the snapshot, so the judgement is stale
#             (#2299);
#   scratch   null, or a scratch worktree under a temporary directory:
#             `{holder, alive, young}`, `holder` the pid named in a
#             `gandr-scratch-<pid>.` directory (null for an unnamed one),
#             `alive` whether that process runs, `young` whether its index
#             changed within 4 hours;
#   watched   null, or the pid of a live `pr:watch` whose mark
#             (`gandr-watch-<pid>`) the worktree's git directory holds;
#   commits   null, or for a branch Worktrunk does not read merged, the
#             `+` lines `git cherry origin/<trunk>` lists, each `{subject,
#             on_trunk}`. `on_trunk` is true when the trunk
#             (`.config/pr-stack/trunk.bash`) holds a commit of that
#             subject. A queue merge's ` (#n)` suffix is dropped;
#   ahead     null, or the count of `git rev-list origin/<trunk>..<head>`
#             for that branch, or for a stale detached head. For a branch, a
#             count above zero and no `+` line means each commit's patch
#             stands on the trunk (#5030). Absent reads as zero;
#   pulls     null, or the merged pull requests whose head is the branch,
#             each `{number, subjects}`, read only when some commit is not
#             on the trunk;
#   idle      no `incremental` directory under its `target/` changed within
#             the 4-hour claim window (#4221); absent reads as not idle;
#   stale     no commit at its head, no change to its index or its `HEAD`,
#             no build under its `target/` for 24 hours, and no live process
#             working in it (#6183). Read only for a tree that is not the
#             primary, the caller's, a watched or a scratch one; absent reads
#             as not stale;
#   dirty     for a stale tree, `git status` lists a change; otherwise null.
#
# The queue lands a branch rebased onto a moved trunk. A rebase that
# resolves a conflict changes the patch. Worktrunk misses that branch
# (#4227). The branch has landed when each listed commit stands on the trunk
# by subject. It has also landed when one merged pull request holds each
# subject that the trunk lacks. A fast-forward can carry an equal patch of
# each commit under a new hash (#5030). `git cherry` then lists no `+` line.
# The branch has landed when `ahead` is above zero. A branch with `ahead` at
# zero lists no commit of its own. That branch stays with Worktrunk's
# reading. It may be a branch cut from the trunk and not yet committed to.
#
# A stale clean tree that has not landed is released: `git worktree remove`
# takes the tree and its build directory, and the branch stays, so no commit
# goes and `wt switch` makes the tree again (#6183). A stale detached head
# whose commits are not all on the trunk stays as the branch
# `attic/<directory>` first. A stale dirty tree stays: its seat decides.
#
# Output: an array of `{path, branch, action, reason}`, one per worktree:
#   remove   `wt remove --foreground`, the branch deleted as merged;
#   delete   `wt remove -D --foreground`, a branch landed by subject, by
#            a merged pull request, or by an equal patch, which Worktrunk
#            reads unmerged;
#   release  `git worktree remove`, the branch kept; a detached head with
#            commits off the trunk carries `attic`, the branch that keeps it;
#   force    `git worktree remove --force`, a scratch tree nothing holds;
#   keep     left as it is.
# A kept worktree that is idle, and no primary, caller's, watched or scratch
# tree, carries `clear: true`: the sweep deletes its `incremental`
# directories, caches its next build writes again (#4221).

# Why the branch has landed though Worktrunk reads it unmerged, or null.
def landing:
  (.commits // []) as $commits
  | (.ahead // 0) as $ahead
  | if ($commits | length) == 0 then
      if $ahead > 0 then "each commit's patch stands on the trunk"
      else null
      end
    elif all($commits[]; .on_trunk) then "its commits stand on the trunk"
    else
      first(
        (.pulls // [])[] as $pull
        | select(all($commits[]; .on_trunk or (.subject as $subject | $pull.subjects | index([$subject]) != null)))
        | "pull request #\($pull.number) merged"
      ) // null
    end;

# The release of a stale tree, or null: a clean tree that stood a day idle.
def release($what):
  if .stale == true and .dirty == false then
    {action: "release", reason: "\($what), idle for 24 hours; its branch stays"}
  else null
  end;

map(
  . as $tree
  | landing as $landing
  | {path, branch} + (
    if .primary then {action: "keep", reason: "the primary worktree"}
    elif .cwd then {action: "keep", reason: "the caller's own worktree"}
    elif .watched != null then {action: "keep", reason: "held by live pr:watch \(.watched)"}
    elif .scratch != null then
      if .scratch.holder != null then
        if .scratch.alive then {action: "keep", reason: "scratch held by live process \(.scratch.holder)"}
        else {action: "force", reason: "scratch whose process \(.scratch.holder) is gone"}
        end
      elif .scratch.young then {action: "keep", reason: "unnamed scratch changed within 4 hours"}
      else {action: "force", reason: "unnamed scratch unchanged for 4 hours"}
      end
    elif .branch == null then
      if .stale == true and .dirty == false then
        {action: "release", reason: "detached, idle for 24 hours"}
        + if (.ahead // 0) > 0 then {attic: "attic/\(.path | split("/") | last)"} else {} end
      elif .stale == true then {action: "keep", reason: "detached, idle for 24 hours, but dirty: its seat decides"}
      else {action: "keep", reason: "detached, not a scratch"}
      end
    elif (.branch | startswith("wip/")) then
      release("a wip/ branch") // {action: "keep", reason: "a wip/ branch"}
    elif (.merged or $landing != null) and .moved then {action: "keep", reason: "its head moved after it was judged landed"}
    elif .merged then {action: "remove", reason: "landed in origin/main"}
    elif $landing != null then {action: "delete", reason: "landed: \($landing)"}
    elif .stale == true and .dirty == true then {action: "keep", reason: "not landed, idle for 24 hours, but dirty: its seat decides"}
    else release("not landed") // {action: "keep", reason: "not landed"}
    end
  )
  | if .action == "keep" and $tree.idle == true and ($tree.primary | not) and ($tree.cwd | not)
      and $tree.watched == null and $tree.scratch == null
    then . + {clear: true}
    else .
    end
)
