# The failing lines of a red line (#6659), which `owner.jq` writes into the
# defect. `check_lines($check)` reads the lines of the gate's log and gives
# the line's own last 30 lines. For a check, each line that opens on
# `[<check>] `, with no echo of a command (`$ …`), no `ERROR task failed` of
# the check itself and no `Finished in` line; the lines of another check stay
# out. For one red test, `check:tests-enforcing <binary> <test>` (#6750), the
# suite's lines from the test's first failure up to the next result line:
# its result, its output and its panic. A line that prints nothing of its own
# gives one line that says so, never an empty block.
def check_lines($check):
  ($check | split(" ")) as $words
  | "[\($words[0])] " as $prefix
  | [.[]
      | select(startswith($prefix))
      | select(.[($prefix | length):] | (startswith("$ ") or . == "ERROR task failed" or startswith("Finished in ")) | not)]
  | if ($words | length) == 3 then
      (map((sub(" +$"; "") | endswith(" \($words[1]) \($words[2])")) and test("(FAIL|TIMEOUT|ABORT|SIG[A-Z]+) +\\[")) | index(true)) as $at
      | if $at == null then []
        else .[$at + 1:] as $rest
        | ($rest | map(test("(PASS|FAIL|SLOW|TIMEOUT|ABORT|SKIP|SIG[A-Z]+) +\\[|Summary \\[")) | index(true) // ($rest | length)) as $end
        | .[$at:$at + 1 + $end][:30]
        end
    else .[-30:]
    end
  | if length == 0 then ["`\($check)` printed no line of its own"] else . end;
