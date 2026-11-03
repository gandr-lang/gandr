# The issues a pull request body works, by the keyword that names each:
# `Advances #n` for a slice, `Closes`, `Fixes` or `Resolves #n` for an issue
# it finishes. The claim lifecycle (`decide.jq`) and the lint assessment
# (`evidence:obligations`) read targets the same way.

def closing: "(close[sd]?|fix(e[sd])?|resolve[sd]?)";
def working: "(\(closing)|advances)";
def targets($keyword): [match("(?i)\\b\($keyword)\\s+#([0-9]+)\\b"; "g") | .captures[-1].string | tonumber];

# Whether an open pull request, `{body, head}`, names issue `$n`: a working
# keyword in its body, or the number in its branch. A claim it names keeps
# its seat (`decide.jq`, `next.jq`).
def names($n):
  (.body | test("(?i)\\b\(working)\\s+#\($n)\\b"))
  or (.head | test("(^|[^0-9])\($n)([^0-9]|$)"));

# The closing keywords a body carries outside its head's keyword lines
# (#2980): GitHub closes the issue a keyword names when the pull request
# merges, wherever the keyword stands, so `closed #628` in prose closes #628.
# A keyword line is one that is exactly `Closes #n`, `Fixes #n` or
# `Resolves #n` (more issues after commas, a full stop allowed), among the
# lines before the first `## ` heading; GitHub's grammar is matched
# case-insensitively, the issue as `#n` or `owner/name#n`. Code spans and
# fenced blocks are not set aside: GitHub closes nothing from a code span
# (#2845's quoted keyword for #2687 left it open), but `targets` reads
# keywords there too, so `pr:open`'s defect rule and the claim lifecycle
# would take a quoted one as a closing target. Each stray is `{line,
# keyword}`.
def strays:
  (split("\n") | map(sub("\r$"; ""))) as $lines
  | (($lines | to_entries | map(select(.value | test("^## "))) | first.key) // ($lines | length)) as $head
  | [$lines | to_entries[]
      | select(.key < $head and (.value | test("^(?i:closes|fixes|resolves) #[0-9]+(, #[0-9]+)*\\.?$")) | not)
      | .value as $line
      | $line | match("(?i)\\b\(closing):?\\s+(#[0-9]+|[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+#[0-9]+)\\b"; "g")
      | {line: $line, keyword: .string}];

# The units a commit `{subject, body}` names (#4638): each issue a working
# keyword names in its message, as the commit rules give every unit's commit
# its `Closes #n` line, and the number a ` (#n)` ends its subject with.
def commit_units:
  ([.subject | match(" \\(#([0-9]+)\\)$") | .captures[0].string | tonumber]
   + ("\(.subject)\n\(.body // "")" | targets(working)))
  | unique;

# The commits of `$commits` that are another unit's (#4638): each names a
# unit, and none of `$units`, the units its pull request works. A commit
# naming no unit is read as the pull request's own. Each is `{oid, subject,
# units, pulls}`, `units` the ones it names and `pulls` the numbers of the
# pull requests of `$pulls`, each `{number, body, head}`, that name one.
def foreign($units; $commits; $pulls):
  [$commits[] | commit_units as $named
    | select($named != [] and ($named - $units) == $named)
    | {oid, subject, units: $named,
       pulls: [$pulls[] | select(. as $pull | any($named[]; . as $n | $pull | names($n))) | .number] | unique}];
