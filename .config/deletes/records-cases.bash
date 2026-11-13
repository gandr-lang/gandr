#!/usr/bin/env bash
# The cases of the records cache of `check:deletes` (`records.bash`, #6823).
# The fast cases build nothing. They make a small workspace in git, a unit
# graph, the messages of a run, its dep-info and the stdout of its build
# scripts, and stand-ins for `rustc` and `cargo`. Then they read the keys
# and the entries that `records.bash` gives:
#   - a change to each part of the key alone misses, and the same content at
#     another path hits;
#   - a change to a file that a dep-info names, to a path that a build script
#     names, to a variable that it names, or to the names in a directory that
#     it lists makes the entry stale;
#   - a stale entry is refused, and a write over it replaces it;
#   - writers of one key at once leave one whole entry, and a writer that
#     stops after half its files leaves no entry;
#   - past the bound, the entries with the oldest touch leave first;
#   - the run of a package records its library, though the run of a package
#     that depends on it built that library first (#7092).
# With `--build`, one case builds: a hit from an entry that a scratch
# worktree writes equals a fresh run in this worktree, byte for byte, for
# each package named (`gandr-core-fork` by default).
#
# Usage: records-cases.bash [--build [<package>=<directory>...]]
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=records.bash
source "$here/records.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-records-cases.XXXXXX")
work=$(cd "$work" && pwd -P)
trap 'rm -rf "$work"' EXIT
fail() { echo "records-cases: $*" >&2; exit 1; }

if [[ ${1:-} == --build ]]; then
  shift
  (( $# )) || set -- gandr-core-fork=crates/core-fork
  root=$(git rev-parse --show-toplevel)
  [[ -z $(git -C "$root" status --porcelain) ]] || fail "--build reads HEAD, and this worktree holds edits that no commit holds"
  git -C "$root" worktree add --quiet --detach "$work/scratch" HEAD
  trap 'git -C "$root" worktree remove --force "$work/scratch"; rm -rf "$work"' EXIT
  summary() { GANDR_DELETES_RECORDS=$1 "$here/records.bash" "$2" "$root/target/deletes" "$3" "${@:4}"; }
  written=$(summary "$work/cache" "$work/scratch" "$work/written" "$@")
  hit=$(summary "$work/cache" "$root" "$work/hit" "$@")
  fresh=$(summary "$work/empty" "$root" "$work/fresh" "$@")
  [[ $written == *": 0 from the cache, $# built" ]] || fail "the scratch worktree reads: $written"
  [[ $hit == *": $# from the cache, 0 built" ]] || fail "this worktree reads: $hit"
  [[ $fresh == *": 0 from the cache, $# built" ]] || fail "the fresh run reads: $fresh"
  diff -r "$work/hit" "$work/fresh" > "$work/diff" || { head -n 20 "$work/diff" >&2; fail "a hit and a fresh run differ"; }
  echo "records-cases OK: a hit from the scratch worktree equals a fresh run here; packages: $#, files: $(ls "$work/hit" | wc -l | tr -d ' ')"
  exit 0
fi

# Stand-ins for the tools, so the fast cases build nothing.
tool_rustc="rustc 1.0.0-nightly (1 2026-01-01)"
tool_dylint="cargo-dylint 1.0.0"
unset DYLINT_LIBRARY_PATH
rustc() {
  case $1 in
    -vV) printf '%s\nhost: x\n' "$tool_rustc" ;;
    --print) echo "$work/sysroot" ;;
  esac
}
# A record run, `cargo dylint --lib <library> -- -p <name> …`, builds the
# library and the test unit of the package and the library of each
# dependency, each unit that its check target lacks, as Cargo builds each
# unit that is not fresh. It writes a record for each unit that it builds.
# The check target is `dylint/target/<toolchain>` of the records target, as
# `cargo dylint` keeps it. `cargo clean --quiet -p <name> --target-dir <dir>`
# takes the units of the package out of `<dir>`.
cargo() {
  case $1 in
    -V) echo "cargo 1.0.0-nightly" ;;
    dylint)
      if [[ $2 == --version ]]; then echo "$tool_dylint"; return; fi
      local unit units=("$6.lib" "$6.test") built=$records_target/dylint/target/nightly-x
      if [[ $6 == a ]]; then units+=(b.lib); fi
      mkdir -p "$built"
      for unit in "${units[@]}"; do
        [[ -e $built/$unit ]] && continue
        touch "$built/$unit"
        echo "{\"unit\": \"$unit\"}" > "$records_work/records/crates_${unit%%.*}_src_lib.rs.${unit#*.}.jsonl"
      done ;;
    clean) rm -f "${6%/}/$4".* ;;
  esac
}

# The workspace: `a` depends on `b`, and `k` stands alone. `a` reads a file of
# `shared` by `include_str!`. The build script of `b` reads a file of `tools`.
# The build script of `k` lists `crates/` and names `crates/k` and `crates/b`.
tree=$work/tree
mkdir -p "$tree"/.cargo "$tree"/crates/{a,b,k}/src "$tree"/crates/{shared,tools,rules}
printf '[workspace]\nmembers = ["crates/*"]\n\n[workspace.lints.rust]\nunsafe_code = "deny"\n' > "$tree/Cargo.toml"
printf 'version = 4\n' > "$tree/Cargo.lock"
printf '[build]\n' > "$tree/.cargo/config.toml"
printf '[toolchain]\nchannel = "nightly"\n' > "$tree/rust-toolchain.toml"
printf '[tools]\n' > "$tree/mise.toml"
: > "$tree/mise.lock"
for crate in a b k; do echo "pub fn $crate() {}" > "$tree/crates/$crate/src/lib.rs"; done
echo 'fn main() {}' > "$tree/crates/b/build.rs"
echo shared > "$tree/crates/shared/data.txt"
echo tools > "$tree/crates/tools/gen.txt"
echo rules > "$tree/crates/rules/surface.rs"
git -C "$tree" init --quiet
git -C "$tree" config core.excludesFile /dev/null
git -C "$tree" config commit.gpgsign false
git -C "$tree" config core.hooksPath /dev/null
git -C "$tree" add -A
git -C "$tree" -c user.name=cases -c user.email=cases@invalid commit --quiet -m fixture
commit() { git -C "$tree" add -A && git -C "$tree" -c user.name=cases -c user.email=cases@invalid commit --quiet -m case; }
restore() { git -C "$tree" reset --quiet --hard "${1:-HEAD}" && git -C "$tree" clean --quiet -fd; }
fixture=$(git -C "$tree" rev-parse HEAD)

records_tree=$tree
records_target=$work/target
records_work=$work/scratch-work
records_cache=$work/cache
mkdir -p "$records_work" "$records_cache" "$records_target"
records_config=$(printf '[quenchant]\nevidence_directory = "%s"\nrule_sources = ["crates/rules/surface.rs"]\nembedded = "%s/target/embedded"\n' "$records_work/records" "$tree")
records_flags="-D spec_attribute_present"

# The unit graph: `$1` the features of `b`'s library unit, as a JSON array.
units() {
  jq -n --arg ws "path+file://$tree/" --argjson features "${1:-[\"default\"]}" '
    def unit($pkg; $kind; $name; $mode; $features; $deps):
      {pkg_id: $pkg, target: {kind: $kind, name: $name, src_path: "-"}, profile: {name: "dev", opt_level: "0"},
       platform: null, mode: $mode, features: $features, dependencies: ($deps | map({index: .}))};
    {version: 1, units: [
      unit($ws + "crates/a#a@0.1.0"; ["lib"]; "a"; "check"; []; [1]),
      unit($ws + "crates/b#b@0.1.0"; ["lib"]; "b"; "check"; $features; [2, 3]),
      unit($ws + "crates/b#b@0.1.0"; ["custom-build"]; "build-script-build"; "run-custom-build"; []; [4]),
      unit("registry+https://github.com/rust-lang/crates.io-index#libc@0.2.0"; ["lib"]; "libc"; "check"; []; []),
      unit($ws + "crates/b#b@0.1.0"; ["custom-build"]; "build-script-build"; "build"; []; []),
      unit($ws + "crates/k#k@0.1.0"; ["lib"]; "k"; "check"; []; [6]),
      unit($ws + "crates/k#k@0.1.0"; ["custom-build"]; "build-script-build"; "run-custom-build"; []; [7]),
      unit($ws + "crates/k#k@0.1.0"; ["custom-build"]; "build-script-build"; "build"; []; [])
    ], roots: [0, 1, 5]}'
}
units > "$work/units.json"

# The key of the package in directory `$1` at the working state of the tree,
# from the unit graph `$2`.
key() {
  records_snapshot
  records_manifest "$(records_fixed)" "$(records_closure "${2:-$work/units.json}" "$1")" | records_sha
}

# `$1` the case, `$2` the directory, `$3` the key before the change alone.
misses() { [[ $(key "$2" "${4:-}") != "$3" ]] || fail "$1: the key of $2 holds"; }
holds() { [[ $(key "$2" "${4:-}") == "$3" ]] || fail "$1: the key of $2 moves"; }

a=$(key crates/a)
b=$(key crates/b)
k=$(key crates/k)
cases=0

# Each part of the key alone.
echo 'pub fn a() { let _ = 1; }' > "$tree/crates/a/src/lib.rs" && commit
misses "the package's tree" crates/a "$a"; holds "the package's tree" crates/k "$k"; restore "$fixture"
echo 'pub fn b() { let _ = 1; }' > "$tree/crates/b/src/lib.rs" && commit
misses "a dependency's tree" crates/a "$a"; holds "a dependency's tree" crates/k "$k"; restore "$fixture"
printf 'version = 4\n\n[[package]]\nname = "libc"\n' > "$tree/Cargo.lock" && commit
misses "Cargo.lock" crates/a "$a"; misses "Cargo.lock" crates/k "$k"; restore "$fixture"
printf '[workspace]\nmembers = ["crates/*"]\n\n[workspace.lints.rust]\nunsafe_code = "allow"\n' > "$tree/Cargo.toml" && commit
for dir in a b k; do misses "a line of [workspace.lints]" "crates/$dir" "${!dir}"; done; restore "$fixture"
for path in .cargo/config.toml rust-toolchain.toml mise.toml mise.lock; do
  echo '# case' >> "$tree/$path" && commit
  misses "$path" crates/a "$a"; restore "$fixture"
done
echo 'rules changed' > "$tree/crates/rules/surface.rs" && commit
misses "a file that the policy names" crates/a "$a"; misses "a file that the policy names" crates/k "$k"; restore "$fixture"
saved=$records_config
records_config+=$'\nreason = "a case"'
misses "the policy configuration" crates/a "$a"; records_config=$saved
records_config=${records_config//$records_work\/records/$work\/elsewhere}
holds "the records' directory of the policy" crates/a "$a"; records_config=$saved
saved=$records_flags
records_flags+=" -D maybe_shape"
misses "a flag" crates/a "$a"; records_flags=$saved
units '["default", "extra"]' > "$work/units-feature.json"
misses "a feature" crates/a "$a" "$work/units-feature.json"; holds "a feature" crates/k "$k" "$work/units-feature.json"
saved=$records_rustflags
records_rustflags+=$'\x1f-Copt-level=1'
misses "the rustflags" crates/a "$a"; records_rustflags=$saved
saved=$tool_rustc
tool_rustc="rustc 1.0.0-nightly (2 2026-01-02)"
misses "the toolchain line" crates/a "$a"; tool_rustc=$saved
saved=$tool_dylint
tool_dylint="cargo-dylint 1.0.1"
misses "the version of cargo-dylint, which builds the lint library" crates/a "$a"; tool_dylint=$saved
export DYLINT_LIBRARY_PATH=$work/libraries
misses "a directory that cargo-dylint searches for the lint library" crates/a "$a"; unset DYLINT_LIBRARY_PATH
echo 'pub fn a() { let _ = 2; }' > "$tree/crates/a/src/lib.rs"
misses "an edit that no commit holds" crates/a "$a"; restore
echo 'mod more;' > "$tree/crates/a/src/more.rs"
misses "a file that no commit holds" crates/a "$a"; holds "a file that no commit holds" crates/b "$b"; restore
cases=$((cases + 23))

# The same content at another path hits: the base's scratch worktree and
# the caller's worktree are at two paths.
saved_tree=$tree saved_config=$records_config saved_work=$records_work
mkdir -p "$work/other" "$work/other-work"
git clone --quiet "$tree" "$work/other/tree"
tree=$work/other/tree records_tree=$work/other/tree records_work=$work/other-work
records_config=${saved_config//$saved_tree/$tree}
records_config=${records_config//$saved_work/$records_work}
units > "$work/units-other.json"
holds "the same content at another path" crates/a "$a" "$work/units-other.json"
# shellcheck disable=SC2034 # the functions of `records.bash` read them.
tree=$saved_tree records_tree=$saved_tree records_config=$saved_config records_work=$saved_work
cases=$((cases + 1))

# The run's messages, its dep-info and the stdout of its build scripts.
out=$records_target/debug/build
mkdir -p "$out/a/1/out" "$out/b/2/out" "$out/b/2/run" "$out/k/3/out" "$out/k/3/run" "$work/run"
printf '%s: crates/a/src/lib.rs crates/shared/data.txt\n\ncrates/a/src/lib.rs:\ncrates/shared/data.txt:\n%s:\n\n# env-dep:A_SETTING=1\n# env-dep:CARGO_PKG_NAME=a\n' \
  "$out/a/1/out/a-1.d" "$out/a/1/out/generated.rs" > "$out/a/1/out/a-1.d"
printf 'cargo:rerun-if-changed=build.rs\ncargo:rerun-if-changed=../tools/gen.txt\ncargo::rerun-if-env-changed=B_SETTING\ncargo:rerun-if-env-changed=CC_aarch64-apple-darwin\n' > "$out/b/2/run/stdout"
printf 'cargo:rerun-if-changed=%s/crates/k\ncargo:rerun-if-changed=%s/crates/b\ncargo:rerun-if-changed=%s/Cargo.lock\n' "$tree" "$tree" "$tree" > "$out/k/3/run/stdout"
{
  jq -n -c --arg pkg "path+file://$tree/crates/a#a@0.1.0" --arg file "$out/a/1/out/liba-1.rmeta" '{reason: "compiler-artifact", package_id: $pkg, filenames: [$file]}'
  jq -n -c --arg pkg "path+file://$tree/crates/b#b@0.1.0" --arg dir "$out/b/2/out" '{reason: "build-script-executed", package_id: $pkg, out_dir: $dir}'
  jq -n -c --arg pkg "path+file://$tree/crates/k#k@0.1.0" --arg dir "$out/k/3/out" '{reason: "build-script-executed", package_id: $pkg, out_dir: $dir}'
} > "$work/messages.json"
for crate in a b k; do
  for unit in lib test; do echo "{\"crate\": \"$crate\", \"unit\": \"$unit\"}" > "$work/run/crates_${crate}_src_lib.rs.$unit.jsonl"; done
done

# Writes the entry of the package in directory `$1`, and prints its key.
write() {
  local key closure
  records_snapshot
  closure=$(records_closure "$work/units.json" "$1")
  records_manifest "$(records_fixed)" "$closure" > "$work/manifest-${1##*/}"
  records_extras "$work/messages.json" "$closure" > "$work/extras-${1##*/}"
  key=$(records_sha < "$work/manifest-${1##*/}")
  records_put "$key" "$work/run" "$(tr '/' '_' <<< "$1")_" "$work/manifest-${1##*/}" "$work/extras-${1##*/}"
  echo "$key"
}
# `$1` the case, `$2` the directory: the entry of the package is valid.
valid() { records_snapshot; records_valid "$(records_sha < "$work/manifest-${2##*/}")" "$work/manifest-${2##*/}" || fail "$1: the entry of $2 is stale"; }
stale() { records_snapshot; ! records_valid "$(records_sha < "$work/manifest-${2##*/}")" "$work/manifest-${2##*/}" || fail "$1: the entry of $2 stays valid"; }

key_a=$(write crates/a)
key_k=$(write crates/k)
expected=$'env A_SETTING\nenv B_SETTING\nenv CC_aarch64-apple-darwin\npath crates/shared/data.txt\npath crates/tools/gen.txt'
[[ $(< "$work/extras-a") == "$expected" ]] || fail "the inputs outside the key of a read: $(< "$work/extras-a")"
expected=$'names crates\npath Cargo.lock\npath crates/b'
[[ $(< "$work/extras-k") == "$expected" ]] || fail "the inputs outside the key of k read: $(< "$work/extras-k")"
mkdir -p "$work/taken"
records_snapshot
records_take "$key_a" "$work/taken" "$work/manifest-a" || fail "a fresh entry of a is not taken"
for file in "$work"/run/crates_a_*; do
  cmp -s "$file" "$work/taken/${file##*/}" || fail "the hit of a differs from its records at ${file##*/}"
done
[[ $(ls "$work/taken" | wc -l) -eq 2 ]] || fail "the hit of a holds $(ls "$work/taken" | wc -l) files, and its records are 2"
cases=$((cases + 3))

# A closure past the bound of one argument gives the inputs of the closure
# that it pads (#7062). Linux admits 131,072 bytes for one argument, and
# macOS admits 1 MiB for all of them, so the pad passes both.
large=$(records_closure "$work/units.json" crates/a | jq -c '.packages += [range(24000) | "registry+https://example.invalid#padding-\(.)@0.1.0"]')
(( ${#large} > 1048576 )) || fail "the padded closure holds ${#large} bytes, not past 1048576"
[[ $(records_extras "$work/messages.json" "$large") == "$(< "$work/extras-a")" ]] || fail "#7062: a closure of ${#large} bytes does not give the inputs of a"
cases=$((cases + 1))

echo changed > "$tree/crates/shared/data.txt" && commit
stale "a file that a dep-info names" crates/a; valid "a file that a dep-info names" crates/k; restore "$fixture"
echo changed > "$tree/crates/tools/gen.txt" && commit
stale "a path that a build script names" crates/a; restore "$fixture"
B_SETTING=1 stale "a variable that a build script names" crates/a
export A_SETTING=2; stale "a variable that a dep-info names" crates/a; unset A_SETTING
mkdir -p "$tree/crates/c" && echo c > "$tree/crates/c/README.md" && commit
stale "a directory added under crates/, which the build script of k lists" crates/k
valid "a directory added under crates/, which the build script of a does not list" crates/a; restore "$fixture"
echo changed > "$tree/crates/b/src/lib.rs" && commit
stale "the tree of a path that a build script names" crates/k; restore "$fixture"
valid "the fixture again" crates/a; valid "the fixture again" crates/k
cases=$((cases + 8))

# A stale entry under a true key is refused, and the next write replaces it.
printf 'other\n' >> "$records_cache/$key_a/manifest"
records_take "$key_a" "$work/taken" "$work/manifest-a" && fail "an entry with another manifest under the key is taken"
[[ $(write crates/a) == "$key_a" ]] && valid "a write over a stale entry" crates/a
echo 0000 > "$records_cache/$key_a/extras.sha"
records_take "$key_a" "$work/taken" "$work/manifest-a" && fail "an entry with another digest of its inputs is taken"
write crates/a > /dev/null && valid "a write over a stale digest" crates/a
cases=$((cases + 2))

# Writers of one key at once leave one whole entry.
rm -rf "${records_cache:?}/$key_a"
for writer in 1 2 3 4 5 6 7 8; do (records_work=$work/writer-$writer && mkdir -p "$records_work" && write crates/a > /dev/null) & done
wait
valid "eight writers at once" crates/a
[[ $(ls "$records_cache/$key_a/files" | wc -l) -eq 2 ]] || fail "eight writers at once leave $(ls "$records_cache/$key_a/files" | wc -l) files"
[[ -z $(find "$records_cache" -mindepth 1 -maxdepth 1 -name '.tmp-*') ]] || fail "eight writers at once leave a temporary directory"

# A writer that stops after half its files leaves no entry under the key,
# and its temporary directory leaves once it is older than one hour.
rm -rf "${records_cache:?}/$key_a"
(
  # shellcheck disable=SC2329 # `records_put` calls it.
  records_clone() { cp "$1" "${*: -1}"; exit 9; }
  records_put "$key_a" "$work/run" crates_a_ "$work/manifest-a" "$work/extras-a"
) && fail "the writer that stops goes on"
[[ ! -e $records_cache/$key_a ]] || fail "a writer that stops after half its files leaves an entry"
leftover=$(find "$records_cache" -mindepth 1 -maxdepth 1 -name '.tmp-*')
[[ -n $leftover && $(ls "$leftover/files" | wc -l) -eq 1 ]] || fail "the writer that stops leaves no half directory"
records_evict
[[ -e $leftover ]] || fail "a temporary directory younger than one hour leaves"
touch -t 202601010000 "$leftover"
records_evict
[[ ! -e $leftover ]] || fail "a temporary directory older than one hour stays"
cases=$((cases + 3))

# Past the bound, the entries with the oldest touch leave first.
write crates/a > /dev/null
touch -t 202601010000 "$records_cache/$key_k"
# shellcheck disable=SC2034 # `records_evict` reads it.
records_bound_kib=$(( $(du -sk "$records_cache" | awk '{ print $1 }') - 1 ))
records_evict
[[ ! -e $records_cache/$key_k && -e $records_cache/$key_a ]] || fail "past the bound, the entry with the oldest touch does not leave first"
cases=$((cases + 1))

# The run of `b` records its library, though the run of `a`, which depends
# on `b`, built that library first (#7092).
rm -rf "$records_target/dylint"
records_build a || fail "#7092: the run of a does not build"
records_build b || fail "#7092: the run of b does not build"
[[ -e $records_work/records/crates_b_src_lib.rs.lib.jsonl ]] \
  || fail "#7092: the run of b after the run of a records no library unit of b: $(ls "$records_work/records" | tr '\n' ' ')"
cases=$((cases + 1))

echo "records-cases OK: $cases cases"
