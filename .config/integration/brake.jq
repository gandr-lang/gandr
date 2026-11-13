# The brake on `landing` (#5442), read by `ci:brake` and `ci:cycle`. The
# brake holds the landings while `main` lags `landing` past one of the two
# limits in `brake.json`. Only a huge backlog takes it. A red cycle files its
# tests, and the landings go on.
#
# The input holds `now` and `oldest`, in seconds since the epoch. `oldest`
# is the committer time of the oldest commit on the first-parent line of
# `landing` that `main` lacks, or null when `main` holds `landing`. The input
# also holds the dispatched runs of landing-checks.yml on `integration`, newest first,
# and the limits. The lag in cycles is the count of verdicts after the
# newest pass. The lag in hours is the age of the oldest commit. A `main`
# that holds `landing` lags by nothing, whatever the verdicts say.
#
# The output is the two lags, whether the brake holds, and one line.
include "verdicts";

. as $in
| if $in.oldest == null then {cycles: 0, hours: 0}
  else {cycles: ($in.runs | verdicts | ((map(.conclusion == "success") | index(true)) // length)),
        hours: ((($in.now - $in.oldest) / 360 | floor) / 10)}
  end
| .on = (.cycles > $in.limits.cycles or .hours > $in.limits.hours)
| .line = "main lags landing: cycles \(.cycles) of at most \($in.limits.cycles), hours \(.hours) of at most \($in.limits.hours). The brake \(if .on then "holds the landings" else "lets the landings go on" end)."
