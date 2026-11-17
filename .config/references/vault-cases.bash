#!/usr/bin/env bash
set -euo pipefail
source .config/references/ledger.bash
source .config/cases/scratch.bash
case=$(jq -c '.[0]' .config/references/vault-cases.json)
old=$(jq -r .old <<< "$case")
new=$(jq -r .new <<< "$case")
missing=$(jq -r .missing <<< "$case")
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
git init --bare --quiet "$scratch/origin"
git init --quiet "$scratch/writer"
identity "$scratch/writer"
git -C "$scratch/writer" remote add origin "$scratch/origin"
printf 'mint: %s\n' "$old" > "$scratch/writer/page.md"
git -C "$scratch/writer" add page.md
git -C "$scratch/writer" commit --quiet -m initial
git -C "$scratch/writer" push --quiet origin HEAD
branch=$(git -C "$scratch/writer" branch --show-current)
git clone --quiet --branch "$branch" "$scratch/origin" "$scratch/checkout"
printf 'mint: %s\n' "$new" >> "$scratch/writer/page.md"
git -C "$scratch/writer" add page.md
git -C "$scratch/writer" commit --quiet -m added
git -C "$scratch/writer" push --quiet origin HEAD
git -C "$scratch/checkout" fetch --quiet origin
printf 'vault:%s\nvault:%s\n' "$new" "$missing" > "$scratch/unresolved"
references_vault_upstream "$scratch/checkout" "$scratch/unresolved" "$scratch/known" "$scratch/state"
[[ $(cat "$scratch/known") == "vault:$new" ]] || { echo 'references vault case FAILED: upstream key'; exit 1; }
IFS=$'\t' read -r checkout behind upstream < "$scratch/state"
[[ $checkout == "$scratch/checkout" && $behind == 1 && -n $upstream ]] || { echo 'references vault case FAILED: stale checkout'; exit 1; }
echo "references vault case $(jq -r .name <<< "$case") OK"
