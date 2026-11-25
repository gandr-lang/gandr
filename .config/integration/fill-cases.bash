#!/usr/bin/env bash
# shellcheck disable=SC2154 # watch.bash, sourced below, sets watch_tree, watch_records and watch_fill_state
# The head watcher fills the records cache of `check:deletes` for each green
# head (#6861), run by `check:integration`. The cases source the real script
# over a scratch state directory and a scratch clone. Each head of the clone
# holds a stand-in of `.config/deletes/records.bash`, which writes the package
# that it gets and the head of its tree to a log.
#
# - A fill runs over each package that the move touches, at the head, one
#   package at a time. A directory with no `Cargo.toml` holds no package.
# - A newer green head stops a fill before its next package, and the head
#   stays unfilled.
# - A head with no `records.bash` fills nothing, and counts as filled.
# - A reading starts no fill while a fill runs, and none for a filled head.
# - A reading starts a fill in the background from the last filled head.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../cases/scratch.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-fill.XXXXXX")
work=$(cd "$work" && pwd -P)
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state
# shellcheck source=watch.bash
source "$here/watch.bash"
failed=0
fail() {
  echo "watch-fill case FAILED: $1"
  echo "  got: $2"
  failed=1
}
# The scratch worktrees take no entry in the host's list of trusted
# configurations, and `mise exec` runs its command as it is. The fill in the
# background is a fresh shell, so the stand-in is exported.
mise() { if [[ $1 == exec ]]; then shift 2; "$@"; fi; }
export -f mise
export FILL_LOG=$work/log FILL_STATE=$watch_state FILL_MOVE=$work/move

mkdir -p "$watch_tree"
git init --quiet "$watch_tree"
identity "$watch_tree"
git -C "$watch_tree" config core.hooksPath /dev/null
mkdir -p "$watch_tree"/crates/{a,b,c}/src "$watch_tree/.config/deletes"
printf '[package]\nname = "gandr-a"\n\n[dependencies]\nname = "other"\n' > "$watch_tree/crates/a/Cargo.toml"
printf '[package]\nname = "gandr-b"\n' > "$watch_tree/crates/b/Cargo.toml"
for crate in a b; do echo "pub fn f() {}" > "$watch_tree/crates/$crate/src/lib.rs"; done
echo c > "$watch_tree/crates/c/README.md"
cat > "$watch_tree/.config/deletes/records.bash" << 'EOF'
#!/usr/bin/env bash
# The stand-in: logs the package and the head of the tree, and moves the
# green head of the state when the case asks it to.
echo "$4 $(git -C "$1" rev-parse --short HEAD)" >> "$FILL_LOG"
if [[ -f $FILL_MOVE ]]; then printf '{"green":"%s"}\n' "$(< "$FILL_MOVE")" > "$FILL_STATE"; fi
EOF
chmod +x "$watch_tree/.config/deletes/records.bash"
commit() { git -C "$watch_tree" add -A && git -C "$watch_tree" commit --quiet -m "$1" && git -C "$watch_tree" rev-parse HEAD; }
base=$(commit base)
echo 'pub fn g() {}' >> "$watch_tree/crates/a/src/lib.rs"
echo more >> "$watch_tree/crates/c/README.md"
first=$(commit first)
echo 'pub fn g() {}' >> "$watch_tree/crates/b/src/lib.rs"
echo 'pub fn h() {}' >> "$watch_tree/crates/a/src/lib.rs"
second=$(commit second)
echo 'pub fn i() {}' >> "$watch_tree/crates/b/src/lib.rs"
third=$(commit third)
git -C "$watch_tree" rm --quiet .config/deletes/records.bash
echo 'pub fn j() {}' >> "$watch_tree/crates/a/src/lib.rs"
bare=$(commit bare)
git -C "$watch_tree" checkout --quiet --detach "$base"
short() { git -C "$watch_tree" rev-parse --short "$1"; }
filled() { jq -r '.filled // empty' "$watch_fill_state" 2> /dev/null || :; }
log() { if [[ -f $FILL_LOG ]]; then paste -sd ',' - < "$FILL_LOG"; fi; }

# A fill runs over each package that the move touches, at the head.
watch_remember "{\"green\":\"$first\"}"
watch_fill "$first" "$base" 2> /dev/null
got="$(log) $(filled)"
[[ $got == "gandr-a=crates/a $(short "$first") $first" ]] \
  || fail "#6861: a fill runs records.bash over the package that the move touches, at the head, and the directory with no Cargo.toml holds none" "$got"

# A newer green head stops a fill before its next package.
rm -f "$FILL_LOG"
watch_remember "{\"green\":\"$second\"}"
echo "$third" > "$FILL_MOVE"
watch_fill "$second" "$first" 2> /dev/null
rm -f "$FILL_MOVE"
got="$(log) $(filled)"
[[ $got == "gandr-a=crates/a $(short "$second") $first" ]] \
  || fail "#6861: a newer green head stops the fill before its next package, and the head stays unfilled" "$got"

# A head with no records.bash fills nothing, and counts as filled.
rm -f "$FILL_LOG"
watch_remember "{\"green\":\"$bare\"}"
watch_fill "$bare" "$third" 2> /dev/null
got="$(log) $(filled)"
[[ $got == " $bare" ]] || fail "#6861: a head with no records.bash fills nothing and counts as filled" "$got"

# A reading starts no fill while a fill runs, and none for a filled head. The
# process of the case stands for the running fill. A background `sleep` would
# be a subshell that runs the trap of the case when it is killed.
rm -f "$FILL_LOG"
jq -n -c --arg head "$first" '{filled: $head}' > "$watch_fill_state"
echo "$$" > "$watch_fill_state.pid"
watch_prefill "$third"
got=$(< "$watch_fill_state.pid")
[[ $got == "$$" ]] || fail "#6861: a reading starts a second fill while one runs" "$got"
/bin/sh -c 'exit 0' &
running=$!
wait "$running"
echo "$running" > "$watch_fill_state.pid"
watch_prefill "$first"
got=$(< "$watch_fill_state.pid")
[[ $got == "$running" ]] || fail "#6861: a reading starts a fill for a filled head" "$got"

# A reading starts a fill in the background from the last filled head.
watch_remember "{\"green\":\"$third\"}"
watch_prefill "$third"
started=$(< "$watch_fill_state.pid")
if [[ $started == "$running" ]]; then
  fail "#6861: a reading starts no fill for a new green head" "$started"
else
  wait "$started" 2> /dev/null || :
  got="$(log) $(filled)"
  [[ $got == "gandr-a=crates/a $(short "$third"),gandr-b=crates/b $(short "$third") $third" ]] \
    || fail "#6861: the fill of a new green head runs over the move from the last filled head" "$got"
fi

(( failed == 0 )) || exit 1
echo "watch-fill check OK: a fill runs over each package that the move touches at the head, stops at a newer green head, fills nothing with no records.bash, and starts in the background from the last filled head, one at a time"
