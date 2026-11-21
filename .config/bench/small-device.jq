# One row of the small-device measure (#7308): a path of gandr run under a
# bound of cores and of memory, with its wall time, the time to its first line
# of output, its peak resident set, the peak that its scope charged and why it
# stopped.
#
# The resident set counts the pages of the binary and its libraries, which
# another scope can hold in the page cache. The bound reads the charged peak
# alone. So a resident set can pass the bound while the charged peak stays
# under it.
#
# The stop is `ends` when the path exits as it must and the host refuses
# nothing. A path that the memory bound stops reads `stopped at <bound>`: the
# kernel kills it in its scope, or the allocation that fails is named. A path
# past the wall-clock limit reads `past the limit`. A refusal of the host is
# quoted, with the issue that owes its answer when the path names one, and any
# other exit gives its status.
#
# Input: {path, cores, memory, status, ended, oom_kills, out_of_memory,
# allocation, wall, first, peak_kib, charged, refusal, owed}. `memory` is the
# bound as the scope takes it, as `64M` or `1G`. `ended` is the status that the
# path exits with when it runs to its end. `wall` and `first` are in seconds,
# and `first` is null when the path prints nothing. `charged` is in bytes, or
# null where the kernel keeps no peak of a scope. `allocation` is the size that
# the failed allocation names, or null. `refusal` is the host's refusal, or
# null. `owed` is the issue that owes the path's end, as `#7308`, or null.
# Output: one Markdown row.
include "bound";

# The memory bound as the table prints it, as `64 MiB` or `1 GiB`.
def bound_text:
  if test("^[0-9]+G$") then "\(.[:-1]) GiB"
  elif test("^[0-9]+M$") then "\(.[:-1]) MiB"
  else error("the memory bound \(.) is not `<n>M` or `<n>G`")
  end;

# Seconds to the hundredth, as `1.05 s`.
def seconds: (. * 100 | round) as $cents
  | "\($cents / 100 | floor).\($cents % 100 | tostring | if length < 2 then "0" + . else . end) s";

# Kibibytes as mebibytes to the tenth, as `27.3 MiB`.
def mebibytes: (. / 1024 * 10 | round) as $tenths | "\($tenths / 10 | floor).\($tenths % 10) MiB";

# Why the path stopped, as the header of this file states.
def stop:
  if .status == 124 then
    "past the limit"
  elif .oom_kills > 0 or past_bound then
    "stopped at \(.memory | bound_text)"
    + if .allocation != null then ": an allocation of \(.allocation) fails" else ": the kernel kills it" end
  elif .refusal != null then
    "refused" + if .owed != null then ", owed by \(.owed)" else "" end + ": \(.refusal)"
  elif .status == .ended then
    "ends"
  else
    "exits \(.status)"
  end;

"| \(.path) | \(.cores) | \(.memory | bound_text) | \(.wall | seconds) | \(if .first == null then "none" else .first | seconds end) | \(.peak_kib | mebibytes) | \(if .charged == null then "none" else .charged / 1024 | mebibytes end) | \(stop) |"
