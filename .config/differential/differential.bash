# The differential of the scheduled replay against the serial run (#7286,
# #3476). `gandr check --recheck --measure` prints one `measure:` line for each
# declaration that crosses into the kernel, then one `schedule:` line and one
# `speculation:` line for each source, then the summary of the run. The run at
# one job is the serial run, the reference at each width.
#
# The ruling on #7286 sets what each width keeps:
# - the name, the bytes, the shared count and the unshared count of each
#   declaration: exactly;
# - each other line, so each verdict and each refusal with its kind: exactly;
# - the census of each declaration, which is work: an `expanded` count at least
#   that of the serial run, and the `recalled` and `kept` counts free;
# - the exit status: exactly.
# The clock sets each time and the critical chain of each `schedule:` line, and
# the width sets the group of each `speculation:` line. So the differential
# reads none of them.

# Write the lines of the run on standard input that the differential reads:
# each `measure:` line without its time, and each line that is not a
# `schedule:` or `speculation:` line.
differential_lines() {
  awk '
    /^(schedule|speculation): / { next }
    /^measure: / { sub(/, ([0-9]+ ns|untimed|unoffered|admitted in a block)$/, "") }
    { print }
  '
}

# Compare the lines of a run at a width, file `$2`, with the lines of the
# serial run, file `$1`, as `differential_lines` writes both. Print one line
# for each line that departs, `<line>: <why>`, and exit 1 when one departs.
differential_compare() {
  awk '
    function census(line, parts) {
      if (match(line, /, [0-9]+ expanded, [0-9]+ recalled, [0-9]+ kept$/)) {
        parts["fixed"] = substr(line, 1, RSTART - 1)
        split(substr(line, RSTART + 2), words, " ")
        parts["expanded"] = words[1] + 0
        return 1
      }
      return 0
    }
    NR == FNR { serial[FNR] = $0; count = FNR; next }
    {
      wide = FNR
      if (!(FNR in serial)) { printf "%d: the serial run has no line here: %s\n", FNR, $0; departs = 1; next }
      if ($0 == serial[FNR]) next
      delete s; delete w
      if (census(serial[FNR], s) && census($0, w) && s["fixed"] == w["fixed"]) {
        if (w["expanded"] >= s["expanded"]) next
        printf "%d: %d expanded, under the %d of the serial run: %s\n", FNR, w["expanded"], s["expanded"], $0
      } else {
        printf "%d: %s\n%d: the serial run: %s\n", FNR, $0, FNR, serial[FNR]
      }
      departs = 1
    }
    END {
      if (wide < count) { printf "%d: the run ends; the serial run has %d lines\n", wide + 1, count; departs = 1 }
      exit departs
    }
  ' "$1" "$2"
}
