#!/usr/bin/env bash
# The landing's gate runs the enforcing suite of the whole workspace
# (#6738), run by `check:gate-scope`. Pull request 6563 changed the checker
# and broke two of its tests, and its gate passed, since the gate ran no test
# (#6595). The suite of the touched packages alone then passed #6709 and
# #6712, which each turned a test of an untouched package red on `landing`.
# Each case builds a scratch workspace of two packages, `red` and `green`,
# whose tests pass at its fork from `origin/$trunk`. The case changes one
# package, reads the suite's scope as `check` reads it (`test-scope.bash`)
# and runs the suite over that scope as `check:tests-enforcing` runs it. A
# change that breaks a test of `red` is refused, and the refusal names the
# test. A change to `green` alone, with `red` broken at the fork, is refused
# too, and the refusal names the test of `red`.
set -euo pipefail
# The head watcher's setting reaches no case (#6739, #6750): each case reads
# a lane's scope.
unset GATE_TEST_EVERY_RED
here="$(cd "${BASH_SOURCE[0]%/*}" && pwd)"
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

# A package at `$1/$2` whose one test asserts that `1 + 1` is `$3`.
package() {
  mkdir -p "$1/$2/src"
  printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n' "$2" > "$1/$2/Cargo.toml"
  printf '#[test]\nfn adds() {\n    assert_eq!(1 + 1, %s);\n}\n' "$3" > "$1/$2/src/lib.rs"
}

# A workspace at `$1` of `red` and `green`, both tests passing, whose
# `origin/$trunk` is its base commit.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  git config user.email gate@example.invalid
  git config user.name gate
  git config commit.gpgsign false
  printf '[workspace]\nmembers = ["red", "green"]\nresolver = "2"\n' > Cargo.toml
  printf 'target/\n' > .gitignore
  package . red 2
  package . green 2
  cargo generate-lockfile --offline --quiet
  git add . && git commit --quiet -m base
  git update-ref "refs/remotes/origin/$trunk" HEAD
}

# The suite over the scope that the gate reads, as the gate runs it.
suite() {
  local args
  args=$("$scope" 2> /dev/null)
  # shellcheck disable=SC2086 # the scope is a list of arguments
  cargo nextest run $args --locked --no-fail-fast 2>&1
}

# A change that breaks a test of the package it touches.
got=$(
  setup "$scratch/broken"
  package . red 3
  if out=$(suite); then echo "passed"; else echo "refused"; fi
  [[ $out == *"red adds"* ]] && echo "names red adds"
)
[[ $got == $'refused\nnames red adds' ]] || fail "#6595: a change that breaks a test of the package it touches is refused, and the refusal names the test" "$got"

# A change to `green` alone, with `red` broken at the fork: #6709 changed the
# corpus and the checker, and two tests of the dispatcher, which it did not
# touch, went red. The suite runs `red` and refuses the change.
got=$(
  setup "$scratch/untouched"
  package . red 3
  git commit --quiet -am 'red breaks at the fork'
  git update-ref "refs/remotes/origin/$trunk" HEAD
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(suite); then echo "passed"; else echo "refused"; fi
  [[ $out == *"red adds"* ]] && echo "names red adds"
  [[ $out == *"green subtracts"* ]] && echo "ran green subtracts"
)
[[ $got == $'refused\nnames red adds\nran green subtracts' ]] || fail "#6738: a lane's gate of a change to the green package alone is refused and names the red test of the untouched package" "$got"

(( failed == 0 )) || exit 1
echo "gate tests OK: a broken test of a touched package is refused, and a red test of an untouched package refuses a change to another"
