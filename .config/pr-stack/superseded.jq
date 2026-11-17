# Whether a cancelled run's checks are superseded, as `pr:watch`'s
# `red_check` reads them. A run on another head than the pull request's
# reads its checks as no checks of the head: a push moved the head, and the
# concurrency group cancelled the run of the commit before (#7796). On the
# head itself, two `pull_request` events start two runs of a workflow in the
# same second, and the concurrency group cancels one; their ids are not
# ordered by which one survives. So the cancelled run is superseded when any
# other run of its workflow on the same head was not cancelled (queued, in
# progress or completed), whatever its id (#2829).
#
# Input: the workflow's runs on the cancelled run's head, each `{id,
# conclusion}`, the conclusion null while a run is queued or in progress;
# none are read for a run on another head.
# Arguments: `$run`, the cancelled run's id; `$sha`, the head it ran on;
# `$head`, the pull request's head.
# Output: `true` when superseded, so its cancelled checks are not red.

$sha != $head or any(.[]; .id != $run and .conclusion != "cancelled")
