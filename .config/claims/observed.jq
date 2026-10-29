# The `observed` obligation of a defect (#3758): a pull request working a
# `kind:defect` issue observes the defect in the running program. Its witness
# is a transcript `debug:test` or `debug:refusal` writes, committed under a
# crate's `tests/debug-traces/`. A transcript witnesses when its `command:`
# header is a `mise run debug:` task, lldb stopped at a breakpoint and printed
# frame 0, and the body names its `test:`. A change whose diff touches no Rust
# has no test for lldb to stop in: there the witness is a recorded `.config`
# case the change adds, whose name cites an issue the body closes, failing
# before the change and passing after it (#3784). The block is the
# `### Observed` section `evidence:obligations` writes after
# `## Re-verification`, its box ticked by a witness alone, never by hand.
#
# Input:
#   defect       whether the body works a `kind:defect` issue
#   body         the pull request's body
#   transcripts  the transcripts the change adds or edits: [{path, text}]
#   paths        every path the change touches; absent, the change is read
#                as touching Rust
#   cases        the `.config` cases the change adds: [{path, name}]
#
# Output: the block's lines between its markers, or nothing when the body
# works no defect. An open box is the obligation owed.

def header($name): [capture("(?m)^" + $name + ": (?<value>.+)$").value][0];
def stop: [capture("(?m)^\\s*\\*?\\s*frame #0: .* at (?<at>\\S+:[0-9]+(:[0-9]+)?)\\s*$").at][0];

select(.defect)
| .body as $body
| ([$body | scan("(?i)\\b(?:closes|fixes|resolves) #([0-9]+)")[0]]) as $closed
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
      else empty end]) as $witnessed
| "<!-- gandr-observed:start -->",
  "### Observed",
  "",
  (if ($witnessed | length) == 0 then
     "- [ ] observed — no transcript under a crate's `tests/debug-traces/` stops in a test the body names. Run `mise run debug:refusal <Refusal> <package> <test>` or `mise run debug:test <package> <test>` and commit its transcript; a change touching no Rust records a `.config` case whose name cites the issue."
   else
     $witnessed[]
   end),
  "<!-- gandr-observed:end -->"
