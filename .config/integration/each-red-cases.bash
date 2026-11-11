#!/usr/bin/env bash
# The head watcher reads every red test of a head (#6750), run by
# `check:integration`. The watcher's suite once stopped at its first red: on
# `61eaa95bd` the red of #6736, which the green head held too, hid 4,822
# tests, and the watcher read the check as the host's and filed nothing. The
# case builds a scratch workspace of two packages, `red` and `green`, each
# with one red test, and runs the suite over the scope that the watcher's
# setting gives (`test-scope.bash`, `GATE_TEST_EVERY_RED`), as
# `check:tests-enforcing` runs it under `mise run --output prefix`. The
# watcher's reading of that log (`watch_failed`) gives one line for each red
# test. A lane's scope keeps fail-fast. The watcher then runs one line alone
# (`watch_test`), through a stub `mise` that runs the suite over
# `GATE_TEST_SCOPE`. The line fails where its test fails. It passes where
# only a test of the same name in another package fails, and where the
# commit lacks the test's package: nextest refuses a filter that names an
# absent binary.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scope="$here/../gate-scope/test-scope.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-each-red.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state CARGO_TARGET_DIR=$work/target
# shellcheck source=watch.bash
source "$here/watch.bash"
failed=0
fail() {
  echo "watch-each-red case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A package at `$1/$2` whose one test asserts that `1 + 1` is `$3`.
package() {
  mkdir -p "$1/$2/src"
  printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n' "$2" > "$1/$2/Cargo.toml"
  printf '#[test]\nfn adds() {\n    assert_eq!(1 + 1, %s);\n}\n' "$3" > "$1/$2/src/lib.rs"
}

mkdir -p "$work/head"
printf '[workspace]\nmembers = ["red", "green"]\nresolver = "2"\n' > "$work/head/Cargo.toml"
package "$work/head" red 3
package "$work/head" green 3
(cd "$work/head" && cargo generate-lockfile --offline --quiet)

# The suite's log as the gate writes it: each line under the check's prefix,
# and mise's line for a task that fails.
args=$(GATE_TEST_EVERY_RED=1 "$scope")
{
  # shellcheck disable=SC2086 # the scope is a list of arguments
  (cd "$work/head" && cargo nextest run $args --offline 2>&1) | sed 's/^/[check:tests-enforcing] /' || :
  echo '[check:tests-enforcing] ERROR task failed'
} > "$work/log"
got=$(watch_failed "$work/log" | paste -sd ',' -)
[[ $got == "check:tests-enforcing green adds,check:tests-enforcing red adds" ]] \
  || fail "#6750: a head with two red tests in two packages gives the watcher's reading two lines, one for each test" "$got"

# A lane's scope is its touched packages and the dispatcher (#6812), with
# no `--no-fail-fast`.
got=$(env -u GATE_TEST_EVERY_RED "$scope" 2> /dev/null)
[[ $got != *--no-fail-fast* ]] || fail "#6750: a lane's scope keeps fail-fast" "$got"

# A stub `mise` that runs `check:tests-enforcing` over `GATE_TEST_SCOPE`.
mkdir -p "$work/bin"
printf '#!/usr/bin/env bash\neval "cargo nextest run $GATE_TEST_SCOPE --offline"\n' > "$work/bin/mise"
chmod +x "$work/bin/mise"
# The result of the line `$1` in the workspace `$2`.
line() {
  watch_tree=$2
  if PATH="$work/bin:$PATH" watch_test "$1" "$work/line.log"; then echo pass; else echo fail; fi
}
got=$(line "check:tests-enforcing red adds" "$work/head")
[[ $got == fail ]] || fail "#6750: the line of a red test fails where the test fails" "$got"

package "$work/head" red 2
got=$(line "check:tests-enforcing red adds" "$work/head")
[[ $got == pass ]] || fail "#6750: the line of a red test passes where only a test of the same name in another package fails" "$got"

got=$(line "check:tests-enforcing gone adds" "$work/head")
[[ $got == pass ]] || fail "#6750: the line of a red test passes on a commit that lacks the test's package" "$got"

printf 'fn broken(' > "$work/head/red/src/lib.rs"
got=$(line "check:tests-enforcing red adds" "$work/head")
[[ $got == fail ]] || fail "#6750: the line of a red test fails where the suite builds no test" "$got"

(( failed == 0 )) || exit 1
echo "watch-each-red check OK: the watcher's reading of a head with two red tests in two packages gives two lines, a lane keeps fail-fast, and one line fails only where its own test fails"
