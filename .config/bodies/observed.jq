# The `observed` obligation of a defect (#3758): a pull request working a
# `kind:defect` issue observes the defect in the running program. Its witness
# is a transcript `debug:test` or `debug:refusal` writes, committed under a
# crate's `tests/debug-traces/`. A transcript witnesses when its `command:`
# header is a `mise run debug:` task, lldb stopped at a breakpoint and printed
# frame 0, and the body names its `test:`. A change whose diff touches no Rust
# has no test for lldb to stop in: there the witness is a recorded `.config`
# case the change adds, whose name cites an issue the body closes, failing
# before the change and passing after it (#3784). A defect whose fault is a
# check's refusal on a head is observed in the check, the program that
# refuses: there the witness is the check's own transcript under a crate's
# `tests/debug-traces/`, its `command:` a `mise run check:` task and its
# `issue:` one the body works, then `before:` a head, `exit:` other than 0
# and the refusing lines, then `after:` a head and `exit: 0` (#7643). The
# block is the `### Observed` section `evidence:obligations` writes after
# `## Re-verification`, its box ticked by a witness alone, never by hand.
#
# Input:
#   defect       whether the body works a `kind:defect` issue
#   body         the pull request's body
#   transcripts  the transcripts the change adds or edits: [{path, text}]
#   paths        every path the change touches, less each Rust file whose
#                diff changes only comments (#5498); absent, the change is
#                read as touching Rust
#   cases        the `.config` cases the change adds: [{path, name}]
#
# Output: the block's lines between its markers, or nothing when the body
# works no defect. An open box is the obligation owed.

def header($name): [capture("(?m)^" + $name + ": (?<value>.+)$").value][0];
# The location of frame 0. lldb may end the line with marks such as ` [opt]`,
# for a frame of the optimised standard library (#5341); the location stands
# before them.
def stop: [capture("(?m)^\\s*\\*?\\s*frame #0: .* at (?<at>\\S+:[0-9]+(:[0-9]+)?)(\\s+\\[[a-z]+\\])*\\s*$").at][0];

select(.defect)
| .body as $body
| ([$body | scan("(?i)\\b(?:closes|fixes|resolves) #([0-9]+)")[0]]) as $closed
| ([$body | scan("(?i)\\b(?:closes|fixes|resolves|advances) #([0-9]+)")[0]]) as $worked
| (.paths != null and (.paths | all(endswith(".rs") | not))) as $rustless
| ([.transcripts[]
    | (.text | header("test")) as $test
    | select($test != null and ($body | contains($test)))
    | select(.text | header("command") // "" | startswith("mise run debug:"))
    | select(.text | test("stop reason = breakpoint"))
    | (.text | stop) as $at
    | select($at != null)
    | "- [x] observed — `\(.path)` stops `\($test)` at `\($at)`."]
   + [if $rustless then
        (.cases // [])[]
        | select(any(.name | scan("#([0-9]+)")[0]; IN($closed[])))
        | "- [x] observed — `\(.path)` records `\(.name)`, the change touching no Rust."
      else empty end]
   + [.transcripts[]
      | .path as $path
      | .text
      | capture("(?s)^command: (?<command>mise run check:[^\\n]+)\\nissue: #(?<issue>[0-9]+)\\nbefore: (?<before>[0-9a-f]{7,40})\\nexit: (?<exit>[1-9][0-9]*)\\n.*?\\S.*?\\nafter: (?<after>[0-9a-f]{7,40})\\nexit: 0\\n?$")
      | select(.issue | IN($worked[]))
      | "- [x] observed — `\($path)` records `\(.command)` refusing at `\(.before)` with exit \(.exit), and passing at `\(.after)`."]) as $witnessed
| "<!-- gandr-observed:start -->",
  "### Observed",
  "",
  (if ($witnessed | length) == 0 then
     "- [ ] observed — no transcript under a crate's `tests/debug-traces/` stops in a test the body names. Run `mise run debug:refusal <Refusal> <package> <test>` or `mise run debug:test <package> <test>` and commit its transcript; a change touching no Rust records a `.config` case whose name cites the issue; a refusal of a check commits the check's transcript, its command, issue, head and exit before and after."
   else
     $witnessed[]
   end),
  "<!-- gandr-observed:end -->"
