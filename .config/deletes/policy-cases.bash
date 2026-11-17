#!/usr/bin/env bash
# The cases of `policy.bash`, run by `check:deletes`. The record run of the
# check once gave `cargo dylint` the records' directory alone (#6838).
# `answer_totality` then read no tables and fired nowhere, so each of the 69
# expectations of it in `gandr-surface-pretty` was unfulfilled, and the
# records of any change to that crate did not build. The cases read this
# tree's `check:dylint` through `policy.bash`. They find its tables, the
# records' directory and its denials, and they find no template. A tree with
# no such settings is refused with exit 2.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-policy.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
fail() {
  echo "deletes policy case FAILED: $1"
  echo "  got: $2"
  failed=1
}

config=$("$here/policy.bash" "$root" /records)
for line in 'evidence_directory = "/records"' 'dishonest_constructors = [' 'presenters = [' \
  '[quenchant-dylints.productions]' '[quenchant-dylints.embedded_source]' "directory = \"$root/target/embedded-sources\""; do
  grep -qxF -- "$line" <<< "$config" \
    || fail "#6838: the record run gives cargo dylint the tables of check:dylint, with the line $line" "$(grep -c '' <<< "$config") lines"
done
if [[ $(grep -c '^evidence_directory = ' <<< "$config") != 1 ]]; then
  fail "#6838: the records go to the run's directory alone" "$(grep '^evidence_directory = ' <<< "$config")"
fi
if grep -qF '{{' <<< "$config"; then
  fail "#6838: no template of check:dylint is left in the record run's configuration" "$(grep -F '{{' <<< "$config")"
fi
flags=$("$here/policy.bash" --flags "$root" /records)
[[ $flags == *'-D spec_attribute_present'* ]] \
  || fail "#6838: the record run takes the denials of check:dylint" "$flags"

# The crates whose expectations the old run left unfulfilled: each expects a
# lint that reads its table from the configuration, and the run gives it the
# table. `gandr-surface-pretty` expects `answer_totality` 69 times, and
# `gandr-surface-lsp`'s replay expects `embedded_source`.
for crate in 'surface-pretty answer_totality presenters = [' 'surface-pretty answer_totality [quenchant-dylints.productions]' \
  'surface-lsp embedded_source [quenchant-dylints.embedded_source]'; do
  read -r dir lint table <<< "$crate"
  git -C "$root" grep -q -E "^[[:space:]]*(expect\()?$lint,?" -- "crates/$dir" \
    || fail "#6838: crates/$dir expects $lint, so its records need the table" "no expectation of $lint"
  grep -qxF -- "$table" <<< "$config" \
    || fail "#6838: the record run of crates/$dir gives $lint its table $table" "no such line"
done

# Each grep of these scripts reads POSIX classes alone (#6853). git 2.54 on
# macOS reads the pattern of `git grep -E` with the regex library of the
# system, which takes no Perl class: the case above then found no line.
perl='\\[sdwbSDWB]'
while IFS= read -r hit; do
  fail "#6853: a grep of .config/deletes reads POSIX classes alone" "$hit"
done < <(git -C "$root" grep -n -E "^[^#]*grep .*$perl" -- '.config/deletes/*.bash' || :)

# A sign-off names its commit by a whole word of 7 to 40 hexadecimal digits
# (#6853), the word that the word boundary of GNU's grep bounds. A digest
# inside a longer word is no match, and a word of 41 digits is none either.
source "$here/digests.bash"
long=0123456789abcdef0123456789abcdef01234567
got=$(digests <<< "signed at abc1234 and $long, not xabc1234, abc1234g, dead_beef1234 or ${long}8" | tr '\n' ' ')
[[ $got == "abc1234 $long " ]] \
  || fail "#6853: a sign-off names its commit by a whole word of 7 to 40 hexadecimal digits, never by part of a longer word" "$got"

mkdir -p "$work/empty/.config/mise/tasks"
: > "$work/empty/.config/mise/tasks/mise-tasks-check.toml"
for mode in '' --flags; do
  status=0
  "$here/policy.bash" ${mode:+"$mode"} "$work/empty" /records > /dev/null 2>&1 || status=$?
  (( status == 2 )) || fail "#6838: a tree with no settings of check:dylint is refused with exit 2 (${mode:-config})" "status $status"
done

(( failed == 0 )) || exit 1
echo "deletes policy OK: the record run reads the tables, the records' directory and the denials of check:dylint, and refuses a tree with none; each grep reads POSIX classes alone"
