#!/usr/bin/env bash
# The cases of `ledger:stamp`, which `check:ledger` runs. Each case builds a
# scratch repository with a small features table: a base commit, and a
# change that edits some rows. The case reads the rows and the commits that
# the script leaves.
# - see: #7978, `stamp.bash`
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
stamp=$here/stamp.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "stamp case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The table: the schema, then the rows `$1`.
table() {
  printf '%s\n' 'PRAGMA foreign_keys=OFF;' 'BEGIN TRANSACTION;' \
    'CREATE TABLE feature(id TEXT PRIMARY KEY, status TEXT NOT NULL, line TEXT NOT NULL, since TEXT);' "$1" 'COMMIT;'
}

# A repository at `$1` whose base holds four rows. The tag `base` names the
# base. The change edits the lines of `alpha`, `beta` and `gamma`, and keeps
# the line of `delta`. `alpha` has the status implemented and no since,
# `beta` the status partial and a since, and `gamma` the status planned.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  identity
  mkdir ledger
  commit ledger/features.sql "$(table "INSERT INTO feature VALUES('alpha','implemented','one, (two)',NULL);
INSERT INTO feature VALUES('beta','partial','three','b87a65d #866');
INSERT INTO feature VALUES('delta','implemented','five','#12');
INSERT INTO feature VALUES('gamma','planned','four',NULL);")" base
  git tag base
  commit ledger/features.sql "$(table "INSERT INTO feature VALUES('alpha','implemented','one, (two) more',NULL);
INSERT INTO feature VALUES('beta','partial','three more','b87a65d #866');
INSERT INTO feature VALUES('delta','implemented','five','#12');
INSERT INTO feature VALUES('gamma','planned','four more',NULL);")" change
}

since() { { cat ledger/features.sql; echo "SELECT id || '=' || coalesce(since, 'NULL') FROM feature ORDER BY id;"; } | sqlite3 | paste -sd ' '; }

# The touched implemented and partial rows take the number. A planned row and
# an untouched row keep their since. The commit holds the ledger alone.
got=$(
  setup "$scratch/stamped"
  "$stamp" 7 base > /dev/null
  echo "$(since) | $(git log -1 --format=%s) | $(git show --name-only --format= HEAD)"
)
want="alpha=#7 beta=b87a65d #866 #7 delta=#12 gamma=NULL | chore(repo): the ledger rows of #7 carry its number | ledger/features.sql"
[[ $got == "$want" ]] || fail "#7978: the touched rows take the number and nothing else changes" "$got"

# A second run finds each row stamped, and writes and commits nothing.
got=$(
  setup "$scratch/again"
  "$stamp" 7 base > /dev/null
  before=$(git rev-parse HEAD)
  out=$("$stamp" 7 base)
  if [[ $(git rev-parse HEAD) == "$before" ]]; then echo "$out"; else echo "committed again"; fi
)
[[ $got == "ledger:stamp: no row that the change touches lacks #7" ]] || fail "#7978: a second run writes nothing" "$got"

# A ledger with changes that no commit holds is refused, and nothing moves.
got=$(
  setup "$scratch/dirty"
  echo '-- note' >> ledger/features.sql
  before=$(git rev-parse HEAD)
  status=0
  "$stamp" 7 base > /dev/null 2>&1 || status=$?
  echo "$status $([[ $(git rev-parse HEAD) == "$before" ]] && echo kept || echo moved)"
)
[[ $got == "2 kept" ]] || fail "#7978: a ledger with uncommitted changes is refused" "$got"

# A commit that a hook refuses leaves the ledger as `HEAD` holds it. So the
# repair that the refusal of `pr:land` names starts on a clean file.
got=$(
  setup "$scratch/refused"
  printf '%s\n' '#!/bin/sh' 'exit 1' > .git/hooks/commit-msg
  chmod +x .git/hooks/commit-msg
  before=$(git rev-parse HEAD)
  status=0
  "$stamp" 7 base > /dev/null 2>&1 || status=$?
  echo "$status $([[ $(git rev-parse HEAD) == "$before" ]] && echo kept || echo moved) [$(git status --porcelain)]"
)
[[ $got == "2 kept []" ]] || fail "#7978: a refused commit leaves the ledger clean" "$got"

# The message of the stamp keeps the commit rules with a number of seven
# digits. The hook runs commitlint with the repository's configuration.
config=$(git -C "$here" rev-parse --show-toplevel)/commitlint.config.mjs
commitlint=$(cd "$here" && mise which commitlint)
got=$(
  setup "$scratch/message"
  printf '%s\n' '#!/bin/sh' "exec \"$commitlint\" --config \"$config\" --edit \"\$1\"" > .git/hooks/commit-msg
  chmod +x .git/hooks/commit-msg
  before=$(git rev-parse HEAD)
  "$stamp" 1234567 base 2>&1 > /dev/null || true
  if [[ $(git rev-parse HEAD) != "$before" ]]; then echo committed; fi
)
[[ $got == committed ]] || fail "#7995: the message of the stamp keeps the commit rules" "$got"

(( failed == 0 )) || exit 1
echo "ledger stamp OK: 5 cases stamp, write nothing again, refuse, give the ledger back and keep the commit rules as recorded"
