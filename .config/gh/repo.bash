# shellcheck shell=bash
# The repository's `owner/name` as text, for a task that puts it where gh
# fills no `{owner}/{repo}` placeholder: a `-R` flag, a `-f` field, a message
# or the input of a mutation (#5749). A path or a `-F` field takes the
# placeholder and needs none of this. The name comes from the first source
# that gives it, and only the last one costs a call:
# - `GH_REPO`, which gh itself reads first;
# - `GITHUB_REPOSITORY`, which each workflow run sets;
# - the URL of `origin`, when it is a github.com URL, as gh reads a clone with
#   one remote;
# - `gh repo view`, one GraphQL call, for a clone whose origin is elsewhere,
#   as the scratch clones of the cases are.
repo_name() {
  local url
  if [[ -n ${GH_REPO:-} ]]; then
    printf '%s\n' "${GH_REPO#*github.com/}"
    return
  fi
  if [[ -n ${GITHUB_REPOSITORY:-} ]]; then
    printf '%s\n' "$GITHUB_REPOSITORY"
    return
  fi
  url=$(git remote get-url origin 2> /dev/null) || url=
  if [[ $url =~ ^(https://|ssh://git@|git@)github\.com[:/]([^/]+/[^/]+)$ ]]; then
    printf '%s\n' "${BASH_REMATCH[2]%.git}"
    return
  fi
  gh repo view --json nameWithOwner --jq .nameWithOwner
}
