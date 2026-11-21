#!/usr/bin/env bash
# The known-red filter of a lane's gate (#7061), read against a recorded list
# in a scratch repository. A row at a head below the branch's base gives its
# filter and one line. A row at a head that the base does not hold, a closed
# list, a list with no row and a list that does not parse give no filter.
# The filter runs a scratch crate's suite: the listed red test is left out,
# and the suite passes; without the filter it fails.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
script=$here/known-red.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
fail() {
  echo "known-red: $*" >&2
  failed=1
}

# The scratch commits carry the scratch identity and sign nothing, whatever
# the host's configuration (#7159). A host that signs each commit through a
# signer that needs a desktop agent fails each signed commit over a remote
# shell. So the cases run under a global configuration that signs each commit
# through a signer that always fails.
printf '[commit]\n\tgpgsign = true\n[gpg]\n\tformat = ssh\n[gpg "ssh"]\n\tprogram = false\n' > "$scratch/gitconfig"
export GIT_CONFIG_GLOBAL=$scratch/gitconfig
repo=$scratch/repo
git init -q -b main "$repo"
(cd "$repo" && identity)
git -C "$repo" commit -q --allow-empty -m red
red=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" commit -q --allow-empty -m base
git -C "$repo" update-ref refs/remotes/origin/landing HEAD
git -C "$repo" switch -q -c lane
git -C "$repo" commit -q --allow-empty -m change
git -C "$repo" switch -q --orphan apart
git -C "$repo" commit -q --allow-empty -m apart
apart=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" switch -q lane
for commit in "$red" "$apart"; do
  [[ $(git -C "$repo" cat-file commit "$commit") != *gpgsig* ]] \
    || fail "#7159: a scratch commit signs nothing under a host that signs each commit"
done

# The body as `known-red.jq` writes it, with the head `$1` and the state `$2`.
found() {
  jq -cn --arg head "${1:0:12}" --arg state "$2" '{number: 5469, state: $state, body: ([
    "The integration cycle keeps this list (#5440).",
    "The cycle on `\($head)` fails: [run 7](https://example.invalid/7).",
    "<details><summary>Known-red tests: 3, red</summary>",
    "",
    "|Test|Binary|Lanes|",
    "|---|---|---|",
    "|`tests::red_one`|`known-red-case`|cargo-test-enforcing-shard-rest|",
    "|`sweeps::red_two`|`known-red-case::tests`|cargo-test-enforcing-shard-rest|",
    "|`lower::tests::elsewhere`|`another-package`|cargo-test-enforcing-shard-lowering|",
    "",
    "</details>"] | join("\n"))}'
}
run() {
  (cd "$repo" && KNOWN_RED_FOUND=$1 "$script" -p known-red-case -p gandr-surface-dispatcher 2> "$scratch/lines")
}

filter=$(run "$(found "$red" OPEN)")
[[ $filter == "not (binary_id(=known-red-case) & test(=tests::red_one)) & not (binary_id(=known-red-case::tests) & test(=sweeps::red_two))" ]] \
  || fail "#7061: a list at a head below the base gave the filter of its rows in the scope: $filter"
[[ $(cd "$repo" && KNOWN_RED_FOUND=$(found "$red" OPEN) "$script" --workspace 2> /dev/null) == "$filter & not (binary_id(=another-package) & test(=lower::tests::elsewhere))" ]] \
  || fail "#7061: a list read with the whole workspace dropped a row"
[[ $(< "$scratch/lines") == "check: #5469 lists tests::red_one red at ${red:0:12}, below this branch's base; the gate leaves it to the fixer"$'\n'"check: #5469 lists sweeps::red_two red at ${red:0:12}, below this branch's base; the gate leaves it to the fixer" ]] \
  || fail "#7061: a list at a head below the base gave no line for each test: $(< "$scratch/lines")"
[[ -z $(run "$(found "$apart" OPEN)") ]] || fail "#7061: a list at a head that the base does not hold gave a filter"
[[ -z $(run "$(found "$red" CLOSED)") ]] || fail "#7061: a closed list gave a filter"
[[ -z $(run '{"number": 5469, "state": "OPEN", "body": "The cycle on `0123456789ab` passes."}') ]] || fail "#7061: a list with no row gave a filter"
[[ -z $(run 'not json') ]] || fail "#7061: a list that does not parse gave a filter"
[[ -z $(run null) ]] || fail "#7061: no list gave a filter"

# The filter on a scratch crate's suite: the red test fails the suite alone,
# and the filter leaves it out.
crate=$scratch/known-red-case
mkdir -p "$crate/src"
printf '[package]\nname = "known-red-case"\nversion = "0.0.0"\nedition = "2024"\n\n[workspace]\n' > "$crate/Cargo.toml"
printf '#[cfg(test)]\nmod tests {\n    #[test]\n    fn red_one() {\n        panic!("red");\n    }\n\n    #[test]\n    fn green() {}\n}\n' > "$crate/src/lib.rs"
mkdir -p "$crate/tests"
printf 'mod sweeps {\n    #[test]\n    fn red_two() {\n        panic!("red");\n    }\n}\n' > "$crate/tests/tests.rs"
export CARGO_TARGET_DIR=$scratch/target
# The scratch crate defines no nextest profile, so its suite runs without the
# caller's `NEXTEST_PROFILE` (#7075).
if (cd "$crate" && env -u NEXTEST_PROFILE cargo nextest run --no-fail-fast > "$scratch/plain.log" 2>&1); then
  fail "#7061: the scratch suite passed with its red test"
fi
(cd "$crate" && env -u NEXTEST_PROFILE cargo nextest run -E "$filter" > "$scratch/filtered.log" 2>&1) \
  || fail "#7061: the filter left the red test in the suite: $(< "$scratch/filtered.log")"

(( failed == 0 )) || exit 1
echo "known-red check OK: a list below the base leaves each listed test of the suite's scope out and names it; another head, a closed list, no row, no parse and no list leave every test in"
