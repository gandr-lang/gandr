# Whether a cancelled run's checks are superseded on its head (#2829), as
# `pr:watch`'s `red_check` reads them. Two `pull_request` events for one head
# start two runs of a workflow in the same second, and the concurrency group
# cancels one; their ids are not ordered by which one survives. So the
# cancelled run is superseded when any other run of its workflow on the same
# head was not cancelled (queued, in progress or completed), whatever its id.
#
# Input: the workflow's runs on the head, each `{id, conclusion}`, the
# conclusion null while a run is queued or in progress.
# Arguments: `$run`, the cancelled run's id.
# Output: `true` when superseded, so its cancelled checks are not red.

any(.[]; .id != $run and .conclusion != "cancelled")
