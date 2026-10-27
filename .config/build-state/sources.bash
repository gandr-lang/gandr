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
# directory with no changed file beneath it, to `SOURCES_EPOCH`: before any
# build output, so an unchanged input reads as fresh. A file that changed, was
# added or was removed keeps the checkout's date, and so does every directory
# above it, so a build script watching it reruns. With no record nothing is
# dated, and every input reads as changed, as before.

# The date unchanged sources take: 2000-01-01T00:00:00Z.
SOURCES_EPOCH=946684800

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
# SOURCES_EPOCH. A changed file marks every directory above it.
sources_restamp() {
  (( $# )) || return 0
  awk -F '\t' -v records="$#" '
    FILENAME == ARGV[1] { current[$0] = $2; next }
    { held[$0]++ }
    END {
      for (line in current) {
        if (held[line] == records) same[current[line]] = 1
        else mark(current[line])
      }
      for (line in held) if (!(line in current)) { split(line, field, "\t"); mark(field[2]) }
      for (path in same) {
        print path
        for (dir = parent(path); dir != ""; dir = parent(dir)) {
          if (dir in changed || dir in dated) continue
          dated[dir] = 1
          print dir
        }
      }
    }
    function mark(path,    dir) { for (dir = parent(path); dir != ""; dir = parent(dir)) changed[dir] = 1 }
    function parent(path,    at) { at = match(path, /\/[^\/]*$/); return at ? substr(path, 1, at - 1) : "" }
  ' <(git ls-files --stage) "$@" |
    xargs -r -d '\n' touch -h -d "@$SOURCES_EPOCH" --
}
