#!/usr/bin/env bash
# A lane's gate runs the suites of the packages a change touches and of
# `gandr-surface-dispatcher` (#6812), and the head watcher's gate runs the
# whole workspace (#6750), run by `check:gate-scope`. Pull request 6563
# changed the checker and broke two of its tests, and its gate passed, since
# the gate ran no test (#6595). #6709 and #6712 each turned a test of the
# dispatcher red on `landing`, a package they did not touch (#6738). Each
# case builds a scratch workspace of three packages, `red`, `green` and
# `gandr-surface-dispatcher`, whose tests pass at its fork from
# `origin/$trunk`. The case changes one package, reads the suite's scope as
# `check` reads it (`test-scope.bash`) and runs the suite over that scope as
# `check:tests-enforcing` runs it.
set -euo pipefail
# Each case reads a lane's scope, and the watcher's case sets the watcher's
# setting on its own call alone (#6739). The scope reads the change against
# the scratch workspace's fork, never against the base of the gate that runs
# the check (`GATE_BASE`, #6894).
unset GATE_TEST_EVERY_RED GATE_BASE
here="$(cd "${BASH_SOURCE[0]%/*}" && pwd)"
source "$here/../cases/scratch.bash"
scope="$here/test-scope.bash"
source "$here/../pr-stack/trunk.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export CARGO_TARGET_DIR="$scratch/target"
failed=0

fail() {
  echo "tests case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A package named `$3` at `$1/$2` whose one test asserts that `1 + 1` is `$4`.
package() {
  mkdir -p "$1/$2/src"
  printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n' "$3" > "$1/$2/Cargo.toml"
  printf '#[test]\nfn adds() {\n    assert_eq!(1 + 1, %s);\n}\n' "$4" > "$1/$2/src/lib.rs"
}

# A workspace at `$1` of `red`, `green` and the dispatcher, every test
# passing, whose `origin/$trunk` is its base commit.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  identity
  printf '[workspace]\nmembers = ["red", "green", "dispatcher"]\nresolver = "2"\n' > Cargo.toml
  printf 'target/\n' > .gitignore
  package . red red 2
  package . green green 2
  package . dispatcher gandr-surface-dispatcher 2
  cargo generate-lockfile --offline --quiet
  git add . && git commit --quiet -m base
  git update-ref "refs/remotes/origin/$trunk" HEAD
}

# The suite over the scope that the gate reads, as the gate runs it. The case
# runs every test past a red one, so its output names each package it ran;
# the watcher's scope asks for that already. The scratch workspace defines no
# nextest profile, so the suite runs without the caller's `NEXTEST_PROFILE`
# (#7075).
suite() {
  local args
  args=$("$scope" 2> /dev/null)
  [[ $args == *--no-fail-fast* ]] || args+=" --no-fail-fast"
  # shellcheck disable=SC2086 # the scope is a list of arguments
  env -u NEXTEST_PROFILE cargo nextest run $args --locked 2>&1
}

# The packages whose tests a suite's output ran, one a line.
ran() {
  [[ $1 == *"red adds"* ]] && echo "ran red"
  [[ $1 == *"green adds"* ]] && echo "ran green"
  [[ $1 == *"gandr-surface-dispatcher adds"* ]] && echo "ran dispatcher"
  :
}

# A change that breaks a test of the package it touches.
got=$(
  setup "$scratch/broken"
  package . red red 3
  if out=$(suite); then echo "passed"; else echo "refused"; fi
  ran "$out"
)
[[ $got == $'refused\nran red\nran dispatcher' ]] || fail "#6595: a change that breaks a test of the package it touches is refused, and the refusal names the test" "$got"

# A change to `green` alone, with `red` broken at the fork: a lane's gate
# runs `green` and the dispatcher, and no other.
got=$(
  setup "$scratch/narrow"
  package . red red 3
  git commit --quiet -am 'red breaks at the fork'
  git update-ref "refs/remotes/origin/$trunk" HEAD
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(suite); then echo "passed"; else echo "refused"; fi
  ran "$out"
)
[[ $got == $'passed\nran green\nran dispatcher' ]] || fail "#6812: a change in one crate runs that crate's suite and the dispatcher's, and no other" "$got"

# The head watcher's gate of the same head runs the whole workspace and
# refuses it by the red test of `red`.
got=$(
  setup "$scratch/whole"
  package . red red 3
  git commit --quiet -am 'red breaks at the fork'
  git update-ref "refs/remotes/origin/$trunk" HEAD
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(GATE_TEST_EVERY_RED=1 suite); then echo "passed"; else echo "refused"; fi
  ran "$out"
)
[[ $got == $'refused\nran red\nran green\nran dispatcher' ]] || fail "#6738, #6750, #6812: the head watcher's gate runs the whole workspace, and a red test of an untouched package refuses a change to another" "$got"

# A caller's nextest profile, as `NEXTEST_PROFILE=ci mise run gate:all` sets
# it, leaves the scratch suite as it is (#7075): the scratch workspace defines
# no profile, and nextest refuses a profile that it does not find.
got=$(
  setup "$scratch/profile"
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(NEXTEST_PROFILE=ci suite); then echo "passed"; else echo "refused"; fi
  ran "$out"
)
[[ $got == $'passed\nran green\nran dispatcher' ]] || fail "#7075: a caller's NEXTEST_PROFILE stopped the scratch suite before it ran a test" "$got"

(( failed == 0 )) || exit 1
echo "gate tests OK: a broken test of a touched package is refused, a lane's suite runs the touched package and the dispatcher alone, and the watcher's whole suite refuses a red untouched package"
