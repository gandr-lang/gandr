# The claim markers an issue body carries (#3915): the lane that claimed it,
# `<!-- claim: lane=<lane> -->`, written by `claim:next`, or the lane that
# last let it go and when, `<!-- released: lane=<lane> at=<time> -->`,
# written by `claim:release` and by the merge that advances it. Writing a
# release removes every marker, so a released body carries that one alone. A
# release under `--forgo` writes neither (#4104). A claim keeps another lane's
# claim standing before its own (`claiming`, #4660): when two runs claim at
# once, the first claim marker is the earlier claim, and it holds the issue.
#
# A marker counts only where a tool writes it, alone on its line (#4839): one
# quoted in prose or a code span, as an issue about the markers writes it, is
# text, never a claim, and no claim or release takes it out. A reader also
# passes over a fenced block.

def claim_marker($lane): "<!-- claim: lane=\($lane) -->";
def released_marker($lane; $at): "<!-- released: lane=\($lane) at=\($at) -->";

# The pattern of `$marker`, a pattern itself, alone on its line: the blank
# text before it and the line's end after it. A writer replaces it with a line
# break and trims the body's end.
def alone($marker): "(?:\\s*\\n|^)[ \\t]*" + $marker + "[ \\t]*(?:\\n|$)";

# The body with each fenced block taken out, so a reader never meets a marker
# quoted in one.
def unfenced: gsub("```[\\s\\S]*?```"; "");

# The body with no claim marker.
def unmarked: gsub(alone("<!-- (claim|released): [^>\\n]*-->"); "\n");

# The body carrying `$marker` alone, after its text.
def marked($marker): (. // "" | unmarked | sub("\\s+$"; "")) + "\n\n" + $marker + "\n";

# The lane a body's first claim marker names, the earlier claim, or null.
def claim_lane: [(. // "") | unfenced | capture(alone("<!-- claim: lane=(?<lane>[^ \\n]+) -->")).lane][0];

# The body carrying `$lane`'s claim marker after any other lane's, its own
# earlier marker and any release removed.
def claiming($lane):
  (. // "" | gsub(alone("<!-- released: [^>\\n]*-->"); "\n") | gsub(alone(claim_marker($lane)); "\n") | sub("\\s+$"; ""))
  + "\n\n" + claim_marker($lane) + "\n";

# The body without `$lane`'s claim marker, or null when it carries none.
def unclaiming($lane):
  if (. // "" | test(alone(claim_marker($lane))))
  then gsub(alone(claim_marker($lane)); "\n") | sub("\\s+$"; "") + "\n"
  else null end;

# A body's release, `{lane, at}` with `at` in seconds, or null.
def release:
  [(. // "") | unfenced | capture(alone("<!-- released: lane=(?<lane>[^ \\n]+) at=(?<at>[^ \\n]+) -->"))
    | {lane, at: (.at | fromdateiso8601)}][0];
