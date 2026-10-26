# The branches no unit accounts for (#2539), which `branches:sweep` lists for
# the session close-out to delete: landing is transactional, so no branch
# outlives its unit unless it is named `wip/<name>` and an open issue names
# it. The listing deletes nothing.
#
# Input: an object with
#   trunk    the default branch;
#   remote   the remote's branch names;
#   local    this clone's branches, each `{name, worktree}`, `worktree` the
#            path holding it or null;
#   heads    the head branch of every open pull request;
#   issues   the title and body of every open issue, each one string.
#
# A branch is accounted for when it is the trunk, the head of an open pull
# request, a merge-queue branch (`gh-readonly-queue/…`, GitHub's own), or a
# `wip/` branch: those are listed apart, unaccounted for when no open issue
# names `wip/<name>` whole.
#
# Output: `{remote, local, wip}`: the remote branch names and the local
# `{name, worktree}`s no open pull request accounts for, and the `wip/`
# branch names, local or remote, no open issue names; each sorted.

def wip: startswith("wip/");
def named($issues): . as $name | any($issues[]; test("(^|[^A-Za-z0-9_./-])\($name | gsub("[.]"; "\\."))($|[^A-Za-z0-9_./-])"));

.trunk as $trunk
| (.heads // []) as $heads
| (.issues // []) as $issues
| def stray: (. == $trunk or startswith("gh-readonly-queue/") or wip or IN($heads[])) | not;
{
  remote: [(.remote // [])[] | select(stray)] | sort,
  local: [(.local // [])[] | select(.name | stray)] | sort_by(.name),
  wip: [((.remote // [])[], (.local // [])[].name) | select(wip) | select(named($issues) | not)] | unique
}
