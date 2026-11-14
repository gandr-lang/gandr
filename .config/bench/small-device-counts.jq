# One count row of the small-device measure (#7359): a check of gandr's count
# build, its allocations over every thread and the frames that the kernel's
# checks popped, as `gandr check --counts` prints them after the run.
#
# A check that passes pops each frame that it pushes, so its frames are the
# frames that it pushed. The stop is `ends` when the check exits as it must and
# prints its counts. A check past the wall-clock limit reads `past the limit`,
# a check that exits with another status gives the status, and a check that
# prints no count says so.
#
# Input: {path, cores, status, ended, allocations, frames}. `ended` is the
# status that the check exits with when it runs to its end. `allocations` and
# `frames` are the counts of the run, or null when it prints none.
# Output: one Markdown row.

# A count as the table prints it, or `none`.
def count: if . == null then "none" else tostring end;

# Why the check stopped, as the header of this file states.
def stop:
  if .status == 124 then
    "past the limit"
  elif .status != .ended then
    "exits \(.status)"
  elif .allocations == null or .frames == null then
    "ends, and prints no count"
  else
    "ends"
  end;

"| \(.path) | \(.cores) | \(.allocations | count) | \(.frames | count) | \(stop) |"
