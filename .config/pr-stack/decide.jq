# How `pr:land` lands a pull request, decided from the stack on the server.
#
# Input: an object with
#   stack      whether `--stack` was given;
#   refreshed  whether the local gh-stack record was refreshed from the server
#              already in this landing;
#   server     the open pull requests of the pull request's stack, bottom to
#              top, each `{number, head}`: its base chain down to the trunk and
#              the pull requests based on it up to the top;
#   local      `gh stack view --json` for the current branch, or null when
#              the clone records no stack.
#
# Output: one tab-separated line:
#   single              land the one pull request;
#   stack<TAB>N         restack and queue the stack whose top is #N;
#   refresh             refresh the local record from the server, then decide
#                       again with `refreshed` set;
#   refuse<TAB>MESSAGE  stop, naming why.
#
# The server is the authority: a stack linked with `gh stack link` has no local
# record, and a reused branch name can leave a record of an earlier landing.
# The local record only drives the restack, so it must name the server's open
# branches in the server's order.

def chain: [.server[] | "#\(.number)"] | join(" ← ");
def open_local: [(.local.branches // [])[] | select(.isMerged | not) | .name];
def stale_entries:
  . as $in
  | [(.local.branches // [])[]
      | . as $branch
      | ($in.server[] | select(.head == $branch.name)) as $open
      | select($branch.isMerged or (($branch.pr.number // $open.number) != $open.number))
      | "local gh-stack record maps \($branch.name) to \(if $branch.isMerged then "merged " else "" end)#\($branch.pr.number // "?"); the open PR is #\($open.number)"];

if (.server | length) <= 1 then
  "single"
elif (.stack | not) then
  "refuse\tPR #\(.server[0].number) is in a stack of \(.server | length) on the server (\(chain)); land it with `pr:land --stack` from #\(.server[-1].number)'s branch"
elif open_local == [.server[] | .head] then
  "stack\t\(.server[-1].number)"
elif .refreshed then
  "refuse\t\((stale_entries | first) // "the local gh-stack record names \(open_local | join(", ")), not the server stack's open branches") in the server stack \(chain); refresh it with `gh stack unstack --local` and `gh stack checkout \(.server[-1].number)`"
else
  "refresh"
end
