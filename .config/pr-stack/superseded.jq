# `pr:watch` calls this program for a cancelled run.
#
# A run of another head has no relevant check. A push moves the pull request
# head, then GitHub cancels the old run.
# - see: #7796
#
# Two pull request events can start one workflow on one head in the same
# second. The concurrency group cancels one run. A peer can queue, run or
# complete. It supersedes the cancelled run. Run identifiers give no order.
# - see: #2829
#
# Input is the workflow's runs on the cancelled run's head. Each run has `id`
# and `conclusion`. The conclusion is null for a queued or running run. A
# different head has no input run.
#
# `$run` is a one-item list. The item is the cancelled run's id. `$sha` names
# its head. `$head` names the pull request's head.
#
# The program returns `true` when another run supersedes this run.

$sha != $head or any(.[]; .id != $run[0] and .conclusion != "cancelled")
