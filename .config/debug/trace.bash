#!/usr/bin/env bash
# One test under lldb, its transcript the witness of a defect's observation
# (#3758). `debug:test` and `debug:refusal` run it.
#
# The test profile inherits `release` and carries no debug information, so the
# test binary is built here with full debug information at opt-level 0, in its
# own target directory (`target/debug-trace`): the gate's builds stay as they
# are. `cargo nextest list` builds the package's test binaries and names the
# one holding the test, and the directory it runs in. lldb runs that binary on
# the one test in batch mode, stopped at each `--at <file>:<line>`, at each
# function `--break` names by regular expression, and at a panic. At the stop
# it prints the backtrace, the frame's locals and the caller's, with the
# checkout's Rust formatters loaded first (`lldbinit`, #3760).
#
# The transcript goes to standard output and to
# `<package dir>/tests/debug-traces/<test>.txt`, `::` written as `.`, the
# workspace root and the home directory taken out of every path in it. Its
# first lines name the test and the command that wrote it, which
# `.config/claims/observed.jq` reads.
#
# Usage: trace.bash <package> <test> [--at <file>:<line>]... [--break <regex>]...
#   [--command <text>]. Exits 2 when the package holds no such test.
set -euo pipefail
package=${1:?trace.bash <package> <test>}
test=${2:?trace.bash <package> <test>}
shift 2
ats=()
breaks=()
command="mise run debug:test $package $test"
while (( $# > 0 )); do
  case $1 in
    --at) ats+=("${2:?--at takes <file>:<line>}"); shift 2 ;;
    --break) breaks+=("${2:?--break takes a regular expression over function names}"); shift 2 ;;
    --command) command=${2:?--command takes the command}; shift 2 ;;
    *) echo "debug: unknown argument \`$1\`" >&2; exit 2 ;;
  esac
done
root=$(git rev-parse --show-toplevel)
unset RUSTFLAGS
export CARGO_TARGET_DIR=$root/target/debug-trace CARGO_PROFILE_TEST_DEBUG=full CARGO_PROFILE_TEST_OPT_LEVEL=0
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
"$root/.config/mise/scope" cargo nextest list --locked --package "$package" --message-format json > "$scratch/listing.json"
suite=$(jq -c --arg test "$test" '[."rust-suites"[] | select(.testcases | has($test))] | first // empty' "$scratch/listing.json")
if [[ -z $suite ]]; then
  echo "debug: $package holds no test named \`$test\`; \`cargo nextest list --package $package\` names them" >&2
  exit 2
fi
binary=$(jq -r '."binary-path"' <<< "$suite")
cwd=$(jq -r .cwd <<< "$suite")
commands=(-o "command source $root/.config/debug/lldbinit" -o 'settings set target.max-children-count 16')
for at in "${ats[@]}"; do commands+=(-o "breakpoint set --file ${at%:*} --line ${at##*:}"); done
for function in "${breaks[@]}"; do commands+=(-o "breakpoint set --func-regex $function"); done
commands+=(-o 'breakpoint set --name rust_panic' -o run -o 'bt 24' -o 'frame variable --depth 3' -o up -o 'frame variable --depth 3')
trace=$cwd/tests/debug-traces/${test//::/.}.txt
mkdir -p "${trace%/*}"
{
  printf 'test: %s\npackage: %s\ncommand: %s\n\n' "$test" "$package" "$command"
  (cd "$cwd" && CARGO_MANIFEST_DIR=$cwd timeout 900 lldb --batch "${commands[@]}" -- "$binary" "$test" --exact --nocapture --test-threads=1 2>&1) || true
} | sed -e "s|$root/||g" -e "s|$HOME|~|g" | tee "$trace"
echo "debug: the transcript is ${trace#"$root"/}" >&2
