# Whether the stall detector is alive (#4167): `stall:watch` writes the time
# of each reading into its memory as `read`, and a detector that stopped
# reading leaves it to age. A reading older than two intervals, or none at
# all, is a finding: no page goes out while the detector is down, so its
# absence is the stall `stall:check` names first.
#
# Input: `{now, interval, read}`: the time now and of the last reading, in
# epoch seconds, `read` absent or null when no reading is recorded, and the
# detector's interval in seconds.
# Output: the finding's line, or nothing while the detector is alive.

. as $in
| if $in.read == null then
    "STALL detector-down: no reading recorded; run `mise run stall:watch --install` on the triage lane's host"
  elif $in.now - $in.read > 2 * $in.interval then
    "STALL detector-down \(($in.now - $in.read) / 60 | floor)m: no reading since \($in.read | todate); run `mise run stall:watch --install` on the triage lane's host"
  else
    empty
  end
