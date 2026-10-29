# The `observed` obligation of a defect (#3758): a pull request working a
# `kind:defect` issue observes the defect in the running program. Its witness
# is a transcript `debug:test` or `debug:refusal` writes, committed under a
# crate's `tests/debug-traces/`. A transcript witnesses when its `command:`
# header is a `mise run debug:` task, lldb stopped at a breakpoint and printed
# frame 0, and the body names its `test:`. The block is the `### Observed`
# section `evidence:obligations` writes after `## Re-verification`, its box
# ticked by the witness alone, never by hand.
#
# Input:
#   defect       whether the body works a `kind:defect` issue
#   body         the pull request's body
#   transcripts  the transcripts the change adds or edits: [{path, text}]
#
# Output: the block's lines between its markers, or nothing when the body
# works no defect. An open box is the obligation owed.

def header($name): [capture("(?m)^" + $name + ": (?<value>.+)$").value][0];
def stop: [capture("(?m)^\\s*\\*?\\s*frame #0: .* at (?<at>\\S+:[0-9]+(:[0-9]+)?)\\s*$").at][0];

select(.defect)
| .body as $body
| [.transcripts[]
    | (.text | header("test")) as $test
    | select($test != null and ($body | contains($test)))
    | select(.text | header("command") // "" | startswith("mise run debug:"))
    | select(.text | test("stop reason = breakpoint"))
    | (.text | stop) as $at
    | select($at != null)
    | {path, test: $test, at: $at}]
| "<!-- gandr-observed:start -->",
  "### Observed",
  "",
  (if length == 0 then
     "- [ ] observed — no transcript under a crate's `tests/debug-traces/` stops in a test the body names. Run `mise run debug:refusal <Refusal> <package> <test>` or `mise run debug:test <package> <test>` and commit its transcript."
   else
     .[] | "- [x] observed — `\(.path)` stops `\(.test)` at `\(.at)`."
   end),
  "<!-- gandr-observed:end -->"
