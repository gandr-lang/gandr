# What the server-side landing watcher does with the open pull requests, read
# once (#2701). `pr:watch` lands a pull request only while its seat's shell
# lives; this reading runs whenever a `CI` run completes, a pull request
# leaves the queue or a draft is taken back (#2984), so a green pull request
# is landed, or its seat told, whether or not anyone is watching it.
#
# A pull request held by a `pr:land` (`landing`) or opened by an app is left
# alone. A stranded one is retargeted to the trunk (`retarget`, with `told`,
# #5776): GitHub could not change its base when the base's pull request
# merged, so it stands on a branch that is gone. That holds in the merge
# queue too, which never merges it there. Any other pull request in the merge
# queue or set to enter it is left alone. Otherwise its state is, in
# this order:
#   dirty      it conflicts with its base;
#   red        a required context failed on its head (`required.jq`);
#   dequeued   the merge queue removed it and its head has not moved since;
#   unrun      its head has no `CI` run (`unrun`, #6164);
#   green      every required context passed;
#   pending    otherwise.
# A seat is told by a comment carrying the mark `<event>:<head>`, once per
# head: a mark already posted for the head posts nothing. A dirty or red pull
# request is always its seat's. The rest depends on `token`, whether the
# watcher holds a token that may queue (`LANDING_TOKEN`, or else the landing
# App's, #3355): the workflow's own token may neither
# queue (the queue refuses its enqueue as not authorized to merge) nor push a
# restack whose checks start (GitHub starts no run for its push).
#   With the token, a green pull request is landed through `land_prefix`,
#   which reads its whole stack bottom up, so one member asks for the stack,
#   and only for a stack with no dequeued member: `land_prefix` reads a
#   dequeued head as green and would queue it again unchanged. A landing
#   that `land_prefix` refuses is told `pr-dequeued`, once per head (`told`,
#   #5695). A dequeued
#   pull request is restacked onto its base, as `pr:watch` heals a stack
#   (#1264), when no member of its stack is red or queued (a push never
#   moves a queued branch or one below it, #2531) and fewer than three
#   restacks of it are marked. The runner rebases it and replays the result
#   through `createCommitOnBranch` (`signed_restack`, #5214), so GitHub signs
#   each commit the trunk's rules require signed; `update-branch`'s rebased
#   commits came out unsigned (#3355). A member above another is restacked
#   the same way once its base moved; one whose restack fails is told
#   instead, once per head (`told` carries whether it was), and one past the
#   cap is told.
#   Without the token, a green stack's lowest green member is told
#   `pr-green`, its seat to land it, and a dequeued pull request is told
#   `pr-dequeued`.
#
# GitHub starts no `CI` run for a push that reaches a pull request while it
# conflicts with its base, and none for a base edit, which it sends as
# `edited` (#6164). Such a head waits on required contexts that never start,
# so nothing lands it, and its stack waits above it. With the token, an unrun
# pull request is closed and reopened, and `reopened` starts `CI`, once per
# head (`pr-rerun`). Without the token, its seat is told `pr-unrun`, once per
# head.
#
# Input: an object with
#   token  whether the watcher holds a token that may queue;
#   prs    the open pull requests, drafts left out, each
#          `{number, oid, queued, held, bot, stack, merge, reading, removed,
#          marks}`: `oid` its head, `stack` its server stack's number or
#          null, `merge` its merge state status, `reading` `required.jq`'s
#          `{failed, pending}` of its head, `removed` whether the last of its
#          queue entries and pushes is a removal from the queue, `removal`
#          that removal's reason in lower case (`failed_checks`, `manual`,
#          …) or "", `stranded` whether the last change of its base is a
#          failed automatic change from the base it still has, `upstream`
#          the subjects described below, `marks` the `<event>:<head>` marks
#          its comments carry, `unrun` whether its head has no `CI` run and
#          is older than the margin `read_prs` allows a new head.
#
#   A removal for `failed_checks` is the entry's own run failing: the
#   enforcing lane runs only in the merge group, so the pull request's own
#   checks read green while the entry is red (#3745). It is never restacked,
#   which would queue the same failure again; its seat is told `pr-dequeued`.
#
#   `upstream` lists, for a dequeued pull request, the commits of its head
#   whose change its base already carries (`upstream_replays`, #4463).
#   The runner's rebase drops each, so they hold no restack back. A seat told
#   `pr-dequeued` without the token, or past the cap, has them named.
#
# Output: the actions, by pull request number, each `{number, act}` with `act`
# one of `land` (with `told`), `restack` (with `told`), `retarget` (with
# `told`), `green`, `dirty`, `red` (with `failed`, the contexts),
# `dequeued` (with `upstream` when it holds such commits), `rerun` or
# `unrun`.

def key: if .stack == null then "#\(.number)" else "stack \(.stack)" end;
def state:
  if .merge == "DIRTY" then "dirty"
  elif (.reading.failed // []) != [] then "red"
  elif .removed then "dequeued"
  elif .unrun then "unrun"
  elif (.reading.pending // ["unread"]) == [] then "green"
  else "pending"
  end;
def marked($event): .oid as $oid | (.marks // []) | any(. == "\($event):\($oid)");
def restacks: [(.marks // [])[] | select(startswith("pr-restacked:"))] | length;

.token as $token
| [.prs[] | . + {state: state}] as $prs
| [$prs[] | select(.stranded and ((.held or .bot) | not)) | {number, act: "retarget", told: marked("pr-dequeued")}] as $stranded
| [$prs[] | select((.queued or .held or .bot or .stranded) | not)]
| map(. as $p
    | [$prs[] | select(key == ($p | key))] as $members
    | if .state == "dirty" then (if marked("pr-dirty") then empty else {number, act: "dirty"} end)
      elif .state == "red" then (if marked("pr-red") then empty else {number, act: "red", failed: .reading.failed} end)
      elif .state == "dequeued" then
        if $token and restacks < 3 and .removal != "failed_checks"
          and all($members[]; ((.reading.failed // []) == []) and (.queued | not))
        then {number, act: "restack", told: marked("pr-dequeued")}
        elif marked("pr-dequeued") then empty
        elif (.upstream // []) != [] then {number, act: "dequeued", upstream}
        else {number, act: "dequeued"}
        end
      elif .state == "unrun" then
        if marked("pr-rerun") or marked("pr-unrun") then empty
        elif $token then {number, act: "rerun"}
        else {number, act: "unrun"}
        end
      elif .state == "green" and all($members[]; .state != "dequeued") then
        if $token then {number, act: "land", key: key, told: marked("pr-dequeued")}
        else {number, act: "green", key: key, told: marked("pr-green")}
        end
      else empty
      end)
| (map(select(.act | IN("land", "green") | not))
   + (map(select(.act | IN("land", "green"))) | group_by([.key, .act]) | map(min_by(.number))))
| map(del(.key) | if .act == "green" then select(.told | not) | del(.told) else . end)
| . + $stranded
| sort_by(.number)
