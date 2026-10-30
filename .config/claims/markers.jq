# The claim markers an issue body carries (#3915), one at a time: the lane
# that claimed it, `<!-- claim: lane=<lane> -->`, written by `claim:next`, or
# the lane that last let it go and when, `<!-- released: lane=<lane>
# at=<time> -->`, written by `claim:release` and by the merge that advances
# it. Writing one removes the other, so a body carries at most one. A
# release under `--forgo` writes neither (#4104).

def claim_marker($lane): "<!-- claim: lane=\($lane) -->";
def released_marker($lane; $at): "<!-- released: lane=\($lane) at=\($at) -->";

# The body with no claim marker.
def unmarked: gsub("\\s*<!-- (claim|released): [^>]*-->"; "");

# The body carrying `$marker` alone, after its text.
def marked($marker): (. // "" | unmarked | sub("\\s+$"; "")) + "\n\n" + $marker + "\n";

# The lane a body's claim marker names, or null.
def claim_lane: [(. // "") | capture("<!-- claim: lane=(?<lane>[^ ]+) -->").lane][0];

# A body's release, `{lane, at}` with `at` in seconds, or null.
def release:
  [(. // "") | capture("<!-- released: lane=(?<lane>[^ ]+) at=(?<at>[^ ]+) -->")
    | {lane, at: (.at | fromdateiso8601)}][0];
