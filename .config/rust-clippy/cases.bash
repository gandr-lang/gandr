#!/usr/bin/env bash
# The cases of `.github/docker/rust-clippy.bash` (#3531), each in
# `.config/rust-clippy/cases.json`, in order, against a scratch rust-clippy
# whose first-parent line sets two channels: an earlier one, then the
# toolchain's at the commit `sets`, kept by the later commit `after`. A case
# pins the script to one of the two commits, as `toolchain:bump` writes the
# pin, and runs it with a channel, a repository under the scratch cache (a
# later case reads what an earlier one fetched), a source (`upstream`, or
# `absent` for none) and a command: `clone` is a driver build's clone of
# rust-clippy, printing its `master` and the parent's `rust-toolchain.toml`;
# `touch` marks that the command ran. A case with `"mv": "bsd"` runs with an
# `mv` that refuses `-T` as darwin's BSD `mv` does (#3601). The exit and
# output are compared, `{sets}` and `{after}` standing for the commits, and a
# refused case must not run its command. No network is read.
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1

upstream=$scratch/upstream
git init --quiet -b main "$upstream"
commit() {
  printf '[toolchain]\nchannel = "%s"\n' "$1" > "$upstream/rust-toolchain.toml"
  git -C "$upstream" add rust-toolchain.toml
  git -C "$upstream" -c user.name=case -c user.email=case@example.invalid -c commit.gpgsign=false \
    commit --quiet --allow-empty -m "$2"
  git -C "$upstream" rev-parse HEAD
}
commit nightly-2026-05-13 'an earlier channel' > /dev/null
sets=$(commit nightly-2026-06-25 'set the channel')
after=$(commit nightly-2026-06-25 'a later change')
# darwin's `mv`, which has no `-T`: it refuses the option as BSD `mv` does.
mkdir "$scratch/bsd"
printf '#!/usr/bin/env bash\nfor a in "$@"; do [[ $a == -T ]] && { echo "mv: illegal option -- T" >&2; exit 64; }; done\nexec %q "$@"\n' "$(command -v mv)" > "$scratch/bsd/mv"
chmod +x "$scratch/bsd/mv"

failed=0
while IFS= read -r case; do
  name=$(jq -r .name <<< "$case")
  pin=$(jq -r 'if .pin == "sets" then $sets else $after end' --arg sets "$sets" --arg after "$after" <<< "$case")
  awk -v rev="$pin" '/^rev=/ { print "rev=" rev; next } { print }' "$root/.github/docker/rust-clippy.bash" > "$scratch/rust-clippy.bash"
  chmod +x "$scratch/rust-clippy.bash"
  case $(jq -r .run <<< "$case") in
    clone) command=(bash -c 'rm -rf "$1" && git clone --quiet https://github.com/rust-lang/rust-clippy "$1" && git -C "$1" rev-parse master && git -C "$1" show master^:rust-toolchain.toml' _ "$scratch/clone") ;;
    touch) command=(touch "$scratch/ran") ;;
  esac
  rm -f "$scratch/ran"
  path=$PATH
  if [[ $(jq -r '.mv // "gnu"' <<< "$case") == bsd ]]; then path=$scratch/bsd:$PATH; fi
  status=0
  output=$(PATH=$path RUST_CLIPPY_URL="file://$scratch/$(jq -r .source <<< "$case")" \
    "$scratch/rust-clippy.bash" "$scratch/cache/$(jq -r .repository <<< "$case").git" "$(jq -r .channel <<< "$case")" "${command[@]}" 2>&1) || status=$?
  want=$(jq -r '.output | gsub("\\{sets\\}"; $sets) | gsub("\\{after\\}"; $after)' --arg sets "$sets" --arg after "$after" <<< "$case")
  if [[ $status != $(jq .exit <<< "$case") || $output != "$want" ]]; then
    printf 'rust-clippy case FAILED: %s\n  exit %s, wanted %s\n  got:  %s\n  want: %s\n' "$name" "$status" "$(jq .exit <<< "$case")" "$output" "$want" >&2
    failed=1
  elif [[ $(jq .exit <<< "$case") != 0 && -e $scratch/ran ]]; then
    printf 'rust-clippy case FAILED: %s\n  the command ran under a refused pin\n' "$name" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$root/.config/rust-clippy/cases.json")
(( failed == 0 )) || exit 1
echo "rust-clippy check OK: $(jq length "$root/.config/rust-clippy/cases.json") cases gave their exit and output"
