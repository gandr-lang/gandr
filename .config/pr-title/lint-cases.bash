#!/usr/bin/env bash
# The cases of `lint.bash`. Stubs of `gh` and `mise` on `PATH` give the title
# from the API or the caller and record what commitlint reads. Each case names
# the issue it keeps closed.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
lint=$root/.config/pr-title/lint.bash
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir "$scratch/bin"
cat > "$scratch/bin/gh" << 'EOF'
#!/usr/bin/env bash
printf '%s' "${STUB_GH_OUT:-}"
printf '%s' "${STUB_GH_ERR:-}" >&2
exit "${STUB_GH_STATUS:-0}"
EOF
cat > "$scratch/bin/mise" << 'EOF'
#!/usr/bin/env bash
printf '%s' "${COMMITLINT_TITLE:-}" > "$STUB_TITLE_MODE"
cat > "$STUB_LINTED"
exit "${STUB_LINT_STATUS:-0}"
EOF
chmod +x "$scratch/bin/gh" "$scratch/bin/mise"

failed=0
fail() {
  printf 'pr title check FAILED: %s\n' "$1" >&2
  failed=1
}

# Runs `lint.bash 6772` under the stubs and the given environment. Sets
# `status`, `stderr`, `linted` and `title_mode`. `linted` is `-` when
# commitlint does not run.
record() {
  stderr=$(< "$scratch/stderr")
  if [[ -f $scratch/linted ]]; then linted=$(< "$scratch/linted"); else linted=-; fi
  if [[ -f $scratch/title-mode ]]; then title_mode=$(< "$scratch/title-mode"); else title_mode=-; fi
}

run() {
  rm -f "$scratch/linted" "$scratch/title-mode"
  status=0
  env PATH="$scratch/bin:$PATH" GITHUB_REPOSITORY=gandr-lang/gandr STUB_LINTED="$scratch/linted" STUB_TITLE_MODE="$scratch/title-mode" "$@" \
    "$lint" 6772 2> "$scratch/stderr" || status=$?
  record
}

run_title() {
  local title=$1
  shift
  rm -f "$scratch/linted" "$scratch/title-mode"
  status=0
  env PATH="$scratch/bin:$PATH" STUB_LINTED="$scratch/linted" STUB_TITLE_MODE="$scratch/title-mode" "$@" \
    "$lint" --title "$title" 2> "$scratch/stderr" || status=$?
  record
}

run STUB_GH_STATUS=1 STUB_GH_ERR="invalid character 'S' looking for beginning of value"
[[ $status == 1 ]] || fail "#6774: a failed read exits $status, not 1"
[[ $stderr == "the read of the title of #6772 failed: invalid character 'S' looking for beginning of value" ]] ||
  fail "#6774: a failed read does not name the read: $stderr"
[[ $linted == - ]] || fail "#6774: commitlint runs after a failed read"

run STUB_GH_OUT=$'\n'
[[ $status == 1 && $stderr == 'the read of the title of #6772 gave no title' && $linted == - ]] ||
  fail "#6774: a read with no title exits $status and commitlint reads '$linted'"

run STUB_GH_OUT=$'fix(ci): lint the title\n'
[[ $status == 0 && $linted == 'fix(ci): lint the title' && $title_mode == 1 ]] ||
  fail "a title that the read gives does not reach commitlint: exit $status, commitlint reads '$linted' in title mode '$title_mode'"

run STUB_GH_OUT=$'Fix the title\n' STUB_LINT_STATUS=1
[[ $status == 1 && $linted == 'Fix the title' && $title_mode == 1 ]] ||
  fail "a title that commitlint refuses exits $status, not 1"

long_title='fix(workflow): '
long_title+=$(printf 'x%.0s' {1..76})
run_title "$long_title" STUB_LINT_STATUS=1
[[ $status == 1 && $linted == "$long_title" && $title_mode == 1 ]] ||
  fail "#7880: a 91-character opening title reaches commitlint in title mode"

if ((failed)); then
  exit 1
fi
echo 'pr title check OK: 5 cases; a failed read names itself and commitlint lints each title it receives'
