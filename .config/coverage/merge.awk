# One LCOV report from many: each line keeps its highest valid count across
# every input. Each file stays once in first input order. It orders its lines
# from the lowest line number to the highest.
#
# A concurrent counter can read below zero. It can report
# `18446744073709551616`, which is 2^64. A count of 2^63 or more is false.
# The merge omits it.
# - see: #1368
# - see: .config/coverage/cases.json
#
function count_at_least_limit(count, position, limit, digit, boundary) {
  if (length(count) > 19) return 1
  if (length(count) < 19) return 0
  limit = "9223372036854775808"
  for (position = 1; position <= 19; position++) {
    digit = substr(count, position, 1)
    boundary = substr(limit, position, 1)
    if (digit != boundary)
      return index("0123456789", digit) > index("0123456789", boundary)
  }
  return 1
}
function count_is_higher(count, previous, position, digit, other) {
  if (length(count) != length(previous)) return length(count) > length(previous)
  for (position = 1; position <= length(count); position++) {
    digit = substr(count, position, 1)
    other = substr(previous, position, 1)
    if (digit != other)
      return index("0123456789", digit) > index("0123456789", other)
  }
  return 0
}
function count_is_nonzero(count, position) {
  for (position = 1; position <= length(count); position++)
    if (substr(count, position, 1) != "0") return 1
  return 0
}
/^SF:/ {
  file = substr($0, 4)
  if (!(file in seen)) { seen[file] = ++nfiles; files[nfiles] = file }
}
/^DA:/ {
  split(substr($0, 4), parts, ",")
  count = parts[2]
  if (count_at_least_limit(count)) next
  key = file SUBSEP parts[1]
  if (!(key in hits) || count_is_higher(count, hits[key])) hits[key] = count
  if (!(key in listed)) { listed[key] = 1; seq[file] = seq[file] parts[1] "\n" }
}
END {
  for (i = 1; i <= nfiles; i++) {
    file = files[i]
    print "SF:" file
    n = split(seq[file], nums, "\n")
    for (a = 1; a < n; a++)
      for (b = a + 1; b <= n; b++)
        if (nums[a] != "" && nums[b] != "" && nums[b]+0 < nums[a]+0) {
          tmp = nums[a]; nums[a] = nums[b]; nums[b] = tmp
        }
    covered = 0
    total = 0
    for (a = 1; a <= n; a++) {
      if (nums[a] == "") continue
      hit = hits[file SUBSEP nums[a]]
      print "DA:" nums[a] "," hit
      total++
      if (count_is_nonzero(hit)) covered++
    }
    print "LH:" covered
    print "LF:" total
    print "end_of_record"
  }
}
