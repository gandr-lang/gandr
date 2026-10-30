# One LCOV report from many: each line keeps its highest count across every
# input (#1368), each file once, in the order its first input names it, and
# its lines in ascending order. `ci:coverage` merges its per-object exports
# with it, and `ci:coverage-merge` merges the coverage workflow's parts.
/^SF:/ {
  file = substr($0, 4)
  if (!(file in seen)) { seen[file] = ++nfiles; files[nfiles] = file }
}
/^DA:/ {
  split(substr($0, 4), parts, ",")
  key = file SUBSEP parts[1]
  if (!(key in hits) || parts[2]+0 > hits[key]) hits[key] = parts[2]+0
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
      if (hit+0 > 0) covered++
    }
    print "LH:" covered
    print "LF:" total
    print "end_of_record"
  }
}
