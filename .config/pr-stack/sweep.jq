# What `wt:sweep` does with each worktree of the clone: a worktree is
# removed when its branch has landed, mechanically, never because a seat
# remembered to. The sweep makes no safety check of its own: `wt remove`
# refuses a dirty or otherwise unsafe tree, and the sweep reports the refusal
# and keeps the tree. The predicates it keeps are the landing itself and a
# live `pr:watch` inside the tree, which runs its merge steps there after
# the landing (#3798).
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
#             commits `git cherry origin/main` lists, each `{subject,
#             on_main}`: `on_main` when a commit origin/main holds has the
#             subject, a queue merge's ` (#n)` suffix dropped;
#   pulls     null, or the merged pull requests whose head is the branch,
#             each `{number, subjects}`, read only when some commit is not
#             on main.
#
# The queue lands a branch rebased onto a moved main, and a rebase that
# resolves a conflict changes the patch, so Worktrunk's readings all miss it
# (#4227). Such a branch has landed when each commit it lists stands on main
# by subject, or when one merged pull request of the branch holds each
# commit's subject that main lacks. A branch listing no commit is left to
# Worktrunk's reading: it may be one cut from main and not yet committed to.
#
# Output: an array of `{path, branch, action, reason}`, one per worktree:
#   remove   `wt remove --foreground`, the branch deleted as merged;
#   delete   `wt remove -D --foreground`, a branch landed by subject or by
#            its merged pull request, which Worktrunk reads unmerged;
#   force    `git worktree remove --force`, a scratch tree nothing holds;
#   keep     left as it is.

# Why the branch has landed though Worktrunk reads it unmerged, or null.
def landing:
  (.commits // []) as $commits
  | if ($commits | length) == 0 then null
    elif all($commits[]; .on_main) then "its commits stand on origin/main"
    else
      first(
        (.pulls // [])[] as $pull
        | select(all($commits[]; .on_main or (.subject as $subject | $pull.subjects | index([$subject]) != null)))
        | "pull request #\($pull.number) merged"
      ) // null
    end;

map(
  landing as $landing
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
    elif .branch == null then {action: "keep", reason: "detached, not a scratch"}
    elif (.branch | startswith("wip/")) then {action: "keep", reason: "a wip/ branch"}
    elif (.merged or $landing != null) and .moved then {action: "keep", reason: "its head moved after it was judged landed"}
    elif .merged then {action: "remove", reason: "landed in origin/main"}
    elif $landing != null then {action: "delete", reason: "landed: \($landing)"}
    else {action: "keep", reason: "not landed"}
    end
  )
)
