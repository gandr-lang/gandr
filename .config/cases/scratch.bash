# shellcheck shell=bash
# The scratch repository that a case harness builds (#5262), sourced by each
# harness that commits in one. It holds the setup alone, never a rule that a
# harness checks: the identity a scratch commit carries, and a commit of one
# file. One copy serves every harness, so a Git setting that each scratch
# commit needs changes in one place.

# Sets the scratch identity on the repository in the working directory: a
# name and an address that no server reads, and no signing by default. A
# command that asks for a signature (`rebase --gpg-sign` in `chain_replay`)
# signs with a key of the scratch repository's own, through `ssh-keygen`. So
# a host's signing key, and the rate limit of the secret that holds it, never
# touches a scratch commit.
identity() {
  local key
  key=$(git rev-parse --absolute-git-dir)/scratch-signing-key
  [[ -e $key ]] || ssh-keygen -q -t ed25519 -N '' -C case -f "$key"
  git config user.name case
  git config user.email case@example.invalid
  git config commit.gpgsign false
  git config gpg.format ssh
  git config gpg.ssh.program ssh-keygen
  git config user.signingkey "$key"
}

# Writes `$2` as the whole of the file `$1`, stages it and commits it with the
# message `$3`.
commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
