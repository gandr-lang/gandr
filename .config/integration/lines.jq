# The failing lines of a red check (#6659), which `owner.jq` writes into the
# defect. `check_lines($check)` reads the lines of the gate's log and gives
# the check's own last 30 lines: each line that opens on `[<check>] `, with
# no echo of a command (`$ …`), no `ERROR task failed` of the check itself
# and no `Finished in` line. The lines of another check stay out. A check
# that prints no line of its own gives one line that says so, never an
# empty block.
def check_lines($check):
  "[\($check)] " as $prefix
  | [.[]
      | select(startswith($prefix))
      | select(.[($prefix | length):] | (startswith("$ ") or . == "ERROR task failed" or startswith("Finished in ")) | not)]
  | .[-30:]
  | if length == 0 then ["`\($check)` printed no line of its own"] else . end;
