# What the server-side landing watcher does with the open pull requests, read
# once (#2701). `pr:watch` lands a pull request only while its seat's shell
# lives; this reading runs whenever a `CI` run completes, a pull request
# leaves the queue or a draft is taken back (#2984), so a green pull request
# is landed, or its seat told, whether or not anyone is watching it.
#
# A pull request in the merge queue or set to enter it, held by a `pr:land`
# (`landing`), or opened by an app is left alone. Otherwise its state is, in
# this order:
#   dirty      it conflicts with its base;
#   red        a required context failed on its head (`required.jq`);
#   dequeued   the merge queue removed it and its head has not moved since;
#   green      every required context passed;
#   pending    otherwise.
# A seat is told by a comment carrying the mark `<event>:<head>`, once per
# head: a mark already posted for the head posts nothing. A dirty or red pull
# request is always its seat's. The rest depends on `token`, whether the
# watcher holds the landing App's token: the workflow's own token may neither
# queue (the queue refuses its enqueue as not authorized to merge) nor push a
# restack whose checks start (GitHub starts no run for its push).
#   With the token, a green pull request is landed through `land_prefix`,
#   which reads its whole stack bottom up, so one member asks for the stack,
#   and only for a stack with no dequeued member: `land_prefix` reads a
#   dequeued head as green and would queue it again unchanged. A dequeued
#   pull request is rebased onto its base by GitHub (`update-branch`), as
#   `pr:watch` heals a stack (#1264), when no member of its stack is red or
#   queued (a push never moves a queued branch or one below it, #2531) and
#   fewer than three restacks of it are marked. GitHub signs the rebased
#   commits, which the trunk's rules require and a rebase in the runner could
#   not. A member above another is rebased the same way once its base moved;
#   one the API refuses is told instead, once per head (`told` carries
#   whether it was), and one past the cap is told.
#   Without the token, a green stack's lowest green member is told
#   `pr-green`, its seat to land it, and a dequeued pull request is told
#   `pr-dequeued`.
#
# Input: an object with
#   token  whether the watcher holds the landing App's token;
#   prs    the open pull requests, drafts left out, each
#          `{number, oid, queued, held, bot, stack, merge, reading, removed,
#          marks}`: `oid` its head, `stack` its server stack's number or
#          null, `merge` its merge state status, `reading` `required.jq`'s
#          `{failed, pending}` of its head, `removed` whether the last of its
#          queue entries and pushes is a removal from the queue, `marks` the
#          `<event>:<head>` marks its comments carry.
#
# Output: the actions, by pull request number, each `{number, act}` with `act`
# one of `land`, `restack` (with `told`), `green`, `dirty`, `red` (with
# `failed`, the contexts) or `dequeued`.

def key: if .stack == null then "#\(.number)" else "stack \(.stack)" end;
def state:
  if .merge == "DIRTY" then "dirty"
  elif (.reading.failed // []) != [] then "red"
  elif .removed then "dequeued"
  elif (.reading.pending // ["unread"]) == [] then "green"
  else "pending"
  end;
def marked($event): .oid as $oid | (.marks // []) | any(. == "\($event):\($oid)");
def restacks: [(.marks // [])[] | select(startswith("pr-restacked:"))] | length;

.token as $token
| [.prs[] | . + {state: state}] as $prs
| [$prs[] | select((.queued or .held or .bot) | not)]
| map(. as $p
    | [$prs[] | select(key == ($p | key))] as $members
    | if .state == "dirty" then (if marked("pr-dirty") then empty else {number, act: "dirty"} end)
      elif .state == "red" then (if marked("pr-red") then empty else {number, act: "red", failed: .reading.failed} end)
      elif .state == "dequeued" then
        if $token and restacks < 3
          and all($members[]; ((.reading.failed // []) == []) and (.queued | not))
        then {number, act: "restack", told: marked("pr-dequeued")}
        elif marked("pr-dequeued") then empty
        else {number, act: "dequeued"}
        end
      elif .state == "green" and all($members[]; .state != "dequeued") then
        if $token then {number, act: "land", key: key}
        else {number, act: "green", key: key, told: marked("pr-green")}
        end
      else empty
      end)
| (map(select(.act | IN("land", "green") | not))
   + (map(select(.act | IN("land", "green"))) | group_by([.key, .act]) | map(min_by(.number))))
| map(del(.key) | if .act == "green" then select(.told | not) | del(.told) else . end)
| sort_by(.number)
