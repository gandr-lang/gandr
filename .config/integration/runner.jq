# The runner of the cycle's suite (#5526), read by `ci:cycle` before it
# dispatches ci.yml on `integration`. The input holds the repository's
# self-hosted runners as the REST API lists them, or null when the cycle
# cannot read them: the App's token holds no `Administration: read`, or
# GitHub refuses the read. A runner that is online and carries the label
# `integration` runs the suite, busy or not, since the cycle runs one suite
# at a time. Any other input gives the hosted runner, so no suite waits for
# a runner that is offline.
#
# The output is the value of ci.yml's input `runner`, `integration` or
# `hosted`, and one line. The line counts the runners and names none, since
# a runner's name can name its host.
[.runners // [] | .[] | select(.status == "online" and any(.labels[]; .name == "integration"))] as $online
| if $online != [] then
    {runner: "integration", line: "The suite runs on the self-hosted runner: \($online | length) online with the label integration."}
  elif .runners == null then
    {runner: "hosted", line: "The suite runs on the hosted runner: the cycle cannot read the self-hosted runners."}
  else
    {runner: "hosted", line: "The suite runs on the hosted runner: no runner with the label integration is online."}
  end
