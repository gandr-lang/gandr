# The claim markers an issue body carries (#3915): the lane that claimed it,
# `<!-- claim: lane=<lane> -->`, written by `claim:next`, or the lane that
# last let it go and when, `<!-- released: lane=<lane> at=<time> -->`,
# written by `claim:release` and by the merge that advances it. Writing a
# release removes every marker, so a released body carries that one alone. A
# release under `--forgo` writes neither (#4104). A claim keeps another lane's
# claim standing before its own (`claiming`, #4660): when two runs claim at
# once, the first claim marker is the earlier claim, and it holds the issue.

def claim_marker($lane): "<!-- claim: lane=\($lane) -->";
def released_marker($lane; $at): "<!-- released: lane=\($lane) at=\($at) -->";

# The body with no claim marker.
def unmarked: gsub("\\s*<!-- (claim|released): [^>]*-->"; "");

# The body carrying `$marker` alone, after its text.
def marked($marker): (. // "" | unmarked | sub("\\s+$"; "")) + "\n\n" + $marker + "\n";

# The lane a body's first claim marker names, the earlier claim, or null.
def claim_lane: [(. // "") | capture("<!-- claim: lane=(?<lane>[^ ]+) -->").lane][0];

# The body carrying `$lane`'s claim marker after any other lane's, its own
# earlier marker and any release removed.
def claiming($lane):
  (. // "" | gsub("\\s*<!-- released: [^>]*-->"; "") | gsub("\\s*<!-- claim: lane=\($lane) -->"; "") | sub("\\s+$"; ""))
  + "\n\n" + claim_marker($lane) + "\n";

# The body without `$lane`'s claim marker, or null when it carries none.
def unclaiming($lane):
  if (. // "" | contains(claim_marker($lane)))
  then gsub("\\s*<!-- claim: lane=\($lane) -->"; "") | sub("\\s+$"; "") + "\n"
  else null end;

# A body's release, `{lane, at}` with `at` in seconds, or null.
def release:
  [(. // "") | capture("<!-- released: lane=(?<lane>[^ ]+) at=(?<at>[^ ]+) -->")
    | {lane, at: (.at | fromdateiso8601)}][0];
