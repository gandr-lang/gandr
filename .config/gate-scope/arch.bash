#!/usr/bin/env bash
# Prints the package arguments of the lint of the code that only an arm64
# build compiles. It prints them on one line, as `scope.bash` prints them. A
# package is in the set when one of its Rust sources holds a `cfg` or
# `cfg_attr` predicate that names `target_arch = "aarch64"` and not
# `target_arch = "x86_64"`. A predicate that names both compiles the same on
# the two, so the lint on x86-64 holds it. The finder reads the predicates,
# never a list.
# - see: #7684, `check:clippy-arch`
#
# When `GATE_SCOPE` excludes a package, the set omits it too, because the
# change reaches nothing of it. A set with no package prints nothing, and
# the lint runs over nothing.
#
# Usage: arch.bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
packages=$(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml" \
  | jq -c --arg root "$root/" '[.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml"))}]')
# Each file whose predicates name `aarch64` without `x86_64`. A predicate
# spans lines, so the finder reads each file whole and matches its
# parentheses.
files=()
while IFS= read -r file; do
  if perl -0777 -ne '
      my $hit = 0;
      while (/\bcfg(?:_attr)?\s*(\((?:[^()]++|(?1))*\))/g) {
        my $p = $1;
        $hit = 1 if $p =~ /target_arch\s*=\s*"aarch64"/ && $p !~ /target_arch\s*=\s*"x86_64"/;
      }
      exit($hit ? 0 : 1);' "$root/$file"; then
    files+=("$file")
  fi
done < <(git -C "$root" grep -l -E 'target_arch *= *"aarch64"' -- 'crates/*.rs')
set=$(printf '%s\n' "${files[@]}" | jq -R -s -c --slurpfile packages <(printf '%s\n' "$packages") --arg scope "${GATE_SCOPE:-}" '
  ([$scope | scan("--exclude ([^ ]+)")[0]]) as $out
  | [split("\n")[] | select(length > 0) as $file
     | $packages[0] | map(select(.dir as $dir | $file | startswith($dir + "/"))) | max_by(.dir | length) | .name]
  | unique | map(select(IN($out[]) | not))')
echo "arch: $(jq -r 'if length == 0 then "no package holds code that only an arm64 build compiles" else "\(length) packages: \(join(" "))" end' <<< "$set")" >&2
jq -r --slurpfile packages <(printf '%s\n' "$packages") '
  if length == 0 then empty
  else . as $set | ["--workspace"] + [$packages[0][].name | select(IN($set[]) | not) | "--exclude " + .] | join(" ") end' <<< "$set"
