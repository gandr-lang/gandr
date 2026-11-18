# The sources a build state was built from, and the dating that keeps a
# build script's inputs fresh across checkouts (#3206).
#
# Cargo reads a crate's sources by checksum (`checksum-freshness`), but a
# build script's `rerun-if-changed` inputs only by mtime. A fresh checkout
# dates every file now, after the restored state's build-script outputs, so
# `runtime-emitter`'s build script reran on every restore, and every crate
# above it rebuilt, even at an exact key.
#
# `sources_record` writes the tracked files' blobs into a state's target
# directory when the state is archived. `sources_restamp`, after a state is
# unpacked, dates every tracked file whose blob every record holds, and every
# directory with no changed file beneath it, to `SOURCES_STAMP`: before any
# build output, so an unchanged input reads as fresh. A file that changed or
# was added, and every directory above a file that changed, was added or was
# removed, is dated now, so a build script watching it reruns. With no record
# every tracked file and its directories are dated now, and every input reads
# as changed. A checkout does not date them: a self-hosted runner's work tree
# outlives its job, its next checkout rewrites no file it already holds, and
# such a file keeps the date an earlier restamp gave it (#5960). Only options
# macOS's `xargs` and `touch` share with GNU's are used (#3244).

# The date unchanged sources take, 2000-01-01T00:00:00Z, as `touch -t` reads
# it in UTC.
SOURCES_STAMP=200001010000.00

# The record's name inside a state's target directory.
SOURCES_RECORD=sources.stage

# sources_record DIR: write the tracked files' modes, blobs and paths, one
# `git ls-files --stage` line each, to DIR/sources.stage. A file the run
# changed in the working tree is left out, so it reads as changed on restore.
sources_record() {
  local dir=$1
  mkdir -p "$dir"
  git ls-files --stage |
    awk -F '\t' 'FILENAME == ARGV[1] { changed[$0] = 1; next } !($2 in changed)' \
      <(git diff --name-only HEAD) - > "$dir/$SOURCES_RECORD"
}

# sources_restamp RECORD...: date each tracked file whose stage line every
# record holds, and each directory with no changed file beneath it, to
# SOURCES_STAMP, and every other tracked file and directory now. A changed
# file marks every directory above it. `touch -c` creates no path, so a
# directory a removal emptied stays absent. The paths go to `touch`
# NUL-separated, and not at all when there are none: macOS's `xargs` has
# neither `-d` nor `-r`, and GNU's runs `touch` once on empty input.
sources_restamp() {
  local paths same fresh
  paths=$(awk -F '\t' -v records="$#" '
    FILENAME == ARGV[1] { current[$0] = $2; next }
    { held[$0]++ }
    END {
      for (line in current) {
        if (records && held[line] == records) same[current[line]] = 1
        else { print "now\t" current[line]; mark(current[line]) }
      }
      for (line in held) if (!(line in current)) { split(line, field, "\t"); mark(field[2]) }
      for (dir in changed) print "now\t" dir
      for (path in same) {
        print "stamp\t" path
        for (dir = parent(path); dir != ""; dir = parent(dir)) {
          if (dir in changed || dir in dated) continue
          dated[dir] = 1
          print "stamp\t" dir
        }
      }
    }
    function mark(path,    dir) { for (dir = parent(path); dir != ""; dir = parent(dir)) changed[dir] = 1 }
    function parent(path,    at) { at = match(path, /\/[^\/]*$/); return at ? substr(path, 1, at - 1) : "" }
  ' <(git ls-files --stage) "$@")
  same=$(awk -F '\t' '$1 == "stamp" { print $2 }' <<< "$paths")
  fresh=$(awk -F '\t' '$1 == "now" { print $2 }' <<< "$paths")
  if [[ -n $same ]]; then
    tr '\n' '\0' <<< "$same" | TZ=UTC0 xargs -0 touch -c -h -t "$SOURCES_STAMP" --
  fi
  if [[ -n $fresh ]]; then
    tr '\n' '\0' <<< "$fresh" | xargs -0 touch -c -h --
  fi
}
