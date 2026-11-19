#!/usr/bin/env bash
# The workflow lists two pages, sorts old weekly packages and deletes no more
# than eight. The dispatch path reads the same set and deletes no package.
set -euo pipefail

tree=$(git rev-parse --show-toplevel)
workflow=$tree/.github/workflows/nightly-cache-retention.yml
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
fake=$scratch/fake
mkdir "$fake"

cat > "$fake/date" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$*" == '-u +%Gw%V' ]]
printf '2026w47\n'
EOF
chmod +x "$fake/date"

cat > "$fake/gh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ $1 == api && $2 == rate_limit ]]; then
  printf '0\n'
  exit 0
fi
if [[ $1 == api && $2 == --method && $3 == DELETE ]]; then
  printf '%s\n' "$4" >> "$CACHE_RETENTION_DELETES"
  exit 0
fi
if [[ $1 == api && $2 == *'page=1' ]]; then
  cat "$CACHE_RETENTION_PAGE_ONE"
  exit 0
fi
if [[ $1 == api && $2 == *'page=2' ]]; then
  cat "$CACHE_RETENTION_PAGE_TWO"
  exit 0
fi
printf 'unexpected gh call: %s\n' "$*" >&2
exit 1
EOF
chmod +x "$fake/gh"

cat > "$scratch/page-one" <<'EOF'
gandr-kache-2026w04
gandr-kache-2026w47
gandr-kache-2026w01
gandr-kache-2026w08
gandr-kache-2026w02
EOF
cat > "$scratch/page-two" <<'EOF'
gandr-kache-2026w06
gandr-kache-2025w52
gandr-kache-2026w48
gandr-kache-2026w05
gandr-kache-2026w07
gandr-kache-2026w03
EOF

list=$(yq -r '.jobs.retention.steps[] | select(.name == "list older weekly packages") | .run' "$workflow")
retain=$(yq -r '.jobs.retention.steps[] | select(.name == "delete older weekly packages") | .run' "$workflow")
run() {
  local dry_run=$1
  mkdir -p "$scratch/runner"
  : > "$scratch/env"
  : > "$scratch/deletes"
  : > "$scratch/summary"
  PATH=$fake:$PATH \
    GITHUB_REPOSITORY_OWNER=gandr-lang \
    GITHUB_ENV=$scratch/env \
    XDG_CACHE_HOME=$scratch/cache \
    RUNNER_TEMP=$scratch/runner \
    CACHE_RETENTION_PAGE_ONE=$scratch/page-one \
    CACHE_RETENTION_PAGE_TWO=$scratch/page-two \
    CACHE_RETENTION_DELETES=$scratch/deletes \
    bash -c "$list"
  set -a
  # shellcheck source=/dev/null
  source "$scratch/env"
  set +a
  PATH=$fake:$PATH \
    GITHUB_REPOSITORY_OWNER=gandr-lang \
    GITHUB_STEP_SUMMARY=$scratch/summary \
    CACHE_RETENTION_DELETES=$scratch/deletes \
    CACHE_RETENTION_DRY_RUN=$dry_run \
    bash -c "$retain" > "$scratch/output-$dry_run"
}

run false
printf '%s\n' \
  'orgs/gandr-lang/packages/container/gandr-kache-2025w52' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w01' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w02' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w03' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w04' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w05' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w06' \
  'orgs/gandr-lang/packages/container/gandr-kache-2026w07' > "$scratch/expected-deletes"
cmp -s "$scratch/expected-deletes" "$scratch/deletes"
[[ $(<"$scratch/summary") == 'cache retention: deleted 8 earlier package(s); 1 earlier package(s) wait; 2 current or later package(s) stay.' ]]

run true
[[ ! -s $scratch/deletes ]]
[[ $(<"$scratch/summary") == 'cache retention: would delete 8 earlier package(s); 1 earlier package(s) wait; 2 current or later package(s) stay.' ]]
printf 'cache retention check OK: two pages delete the eight oldest weeks, and the dispatch path deletes none\n'
