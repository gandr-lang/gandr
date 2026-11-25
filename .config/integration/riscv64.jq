# Whether the riscv64 jobs of a night run. Their host is not online every
# night, and a job that waits for an absent runner stays queued until GitHub
# cancels it. So a job on the riscv64 runners runs only when one of them is
# online, and otherwise the night skips it and says why.
#
# The input holds the repository's self-hosted runners as the REST API lists
# them, or null when the night cannot read them. A runner that is online and
# carries the label `RISCV64` runs the jobs, busy or not. The output is
# `online`, true or false, and one line for the run's summary. The line
# counts the runners and names none, since a runner's name can name its host.
[.runners // [] | .[] | select(.status == "online" and any(.labels[]; .name == "RISCV64"))] as $online
| if $online != [] then
    {online: true, line: "The riscv64 jobs run: \($online | length) runner(s) online with the label RISCV64."}
  elif .runners == null then
    {online: false, line: "The riscv64 jobs skip: the night cannot read the self-hosted runners."}
  else
    {online: false, line: "The riscv64 jobs skip: no runner with the label RISCV64 is online."}
  end
