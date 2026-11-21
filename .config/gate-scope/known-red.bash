#!/usr/bin/env bash
# Prints the nextest filter that leaves out of a lane's suite each test that
# the integration cycle's known-red list names red below the branch's base
# (#7061), and one line on stderr for each test it leaves out.
#
# The cycle keeps the list in one issue (#5469, `known-red.jq`). Its body
# names the head of the failed cycle, `The cycle on <head> fails`, and holds
# one row for each red test: the test and its binary, as nextest's JUnit
# report names them. A row binds to that head. When the issue is open and the
# head is an ancestor of the merge base of `HEAD` and `origin/<trunk>`, the
# test is red at the branch's base. The fixer repairs it, so it does not hold
# a lane's gate. A closed list, a list with no row, another head and a failed
# read print nothing, and the gate runs every test of its scope. The gate
# cannot tell the base's red of a listed test from a new red of the same
# test, and the cycle reads both.
#
# The arguments are the suite's package arguments, `GATE_TEST_SCOPE`. A row
# of a package outside them is dropped: its test does not run, and nextest
# refuses a `binary_id` that matches no binary of the run. With
# `--workspace`, or with no `-p`, every row stays.
#
# `KNOWN_RED_FOUND` holds the issue as `issue_found` gives it, and the script
# then reads no issue: the cases give a recorded list.
#
# Usage: known-red.bash [-p <package>]... | [--workspace]
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
packages=()
while (( $# > 0 )); do
  case $1 in
    -p | --package) packages+=("$2"); shift 2 ;;
    --workspace) packages=(); break ;;
    *) shift ;;
  esac
done
if [[ -n ${KNOWN_RED_FOUND+set} ]]; then
  found=$KNOWN_RED_FOUND
else
  source "$here/../issues/keep.bash"
  found=$(issue_found "integration: the known-red list" 2> /dev/null) || exit 0
fi
# One line for the head, then one line for each row: the test and its binary.
rows=$(jq -r '
  select(.state == "OPEN")
  | .body as $body
  | ($body | capture("The cycle on `(?<head>[0-9a-f]{7,40})` fails") | .head) as $head
  | $head,
    ($body | split("\n")[]
      | capture("^\\|`(?<test>[^`]+)`\\|`(?<binary>[^`]+)`\\|")
      | "\(.test)\t\(.binary)")
' <<< "$found" 2> /dev/null) || exit 0
[[ -n $rows ]] || exit 0
head=${rows%%$'\n'*}
[[ $rows == *$'\n'* ]] || exit 0
source "$here/../pr-stack/trunk.bash"
base=$(git merge-base "origin/$trunk" HEAD 2> /dev/null) || exit 0
git merge-base --is-ancestor "$head" "$base" 2> /dev/null || exit 0
filter=
while IFS=$'\t' read -r test binary; do
  if (( ${#packages[@]} > 0 )) && [[ " ${packages[*]} " != *" ${binary%%::*} "* ]]; then
    continue
  fi
  filter+="${filter:+ & }not (binary_id(=$binary) & test(=$test))"
  echo "check: #5469 lists $test red at $head, below this branch's base; the gate leaves it to the fixer" >&2
done <<< "${rows#*$'\n'}"
printf '%s\n' "$filter"
