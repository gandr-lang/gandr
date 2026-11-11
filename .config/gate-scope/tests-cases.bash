#!/usr/bin/env bash
# The landing's gate runs the suite of the packages a change touches (#6595),
# run by `check:gate-scope`. Pull request 6563 changed the checker and broke
# two of its tests, and its gate passed, since the gate ran no test. Each case
# builds a scratch workspace of two packages, `red` and `green`, whose tests
# pass at its fork from `origin/$trunk`. The case changes one package, reads
# the suite's scope as `check` reads it (`scope.bash --touched`) and runs the
# suite over that scope as `check:tests-enforcing` runs it. A change that
# breaks a test of `red` is refused, and the refusal names the test. A change
# to `green` alone passes, and its suite keeps `red` out. The head watcher's
# suite (`GATE_TEST_WHOLE`, #6725) runs `red` too, so it refuses that change.
set -euo pipefail
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

# The suite over the change's touched packages, as the gate runs it, or over
# the whole workspace when `GATE_TEST_WHOLE` is set, as the watcher runs it.
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

# A change to `green` alone, with `red` broken at the fork: the suite runs
# `green` and keeps `red` out.
got=$(
  setup "$scratch/narrow"
  package . red 3
  git commit --quiet -am 'red breaks at the fork'
  git update-ref "refs/remotes/origin/$trunk" HEAD
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(suite); then echo "passed"; else echo "refused"; fi
  [[ $out == *"red adds"* ]] && echo "ran red"
  [[ $out == *"green subtracts"* ]] && echo "ran green subtracts"
)
[[ $got == $'passed\nran green subtracts' ]] || fail "#6595: a change to one package runs that package's suite and no other" "$got"

# The head watcher's suite over the same head: #6709 changed the corpus and
# the checker, and two tests of the dispatcher, which it did not touch, went
# red. The whole suite runs `red` and refuses the head.
got=$(
  setup "$scratch/whole"
  package . red 3
  git commit --quiet -am 'red breaks at the fork'
  git update-ref "refs/remotes/origin/$trunk" HEAD
  printf '\n#[test]\nfn subtracts() {\n    assert_eq!(2 - 1, 1);\n}\n' >> green/src/lib.rs
  if out=$(GATE_TEST_WHOLE=1 suite); then echo "passed"; else echo "refused"; fi
  [[ $out == *"red adds"* ]] && echo "names red adds"
)
[[ $got == $'refused\nnames red adds' ]] || fail "#6725: the head watcher's suite refuses a head with a red test in a package that the change does not touch" "$got"

(( failed == 0 )) || exit 1
echo "gate tests OK: a broken test of a touched package is refused, the suite keeps an untouched package out, and the watcher's whole suite refuses a red untouched package"
