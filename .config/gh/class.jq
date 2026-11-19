# The API and kind of a `gh` call's verb (#5061), as `sites.awk` spells it:
# `{api, kind}`, the API `graphql` or `rest` and the kind `read` or
# `write`. A verb gh serves through GraphQL reads there, as `pr view`; a
# verb this file does not name is a GraphQL write, the dearest guess.
def class:
  if . == "api graphql" then {api: "graphql", kind: "read"}
  elif . == "api GET" then {api: "rest", kind: "read"}
  elif startswith("api ") then {api: "rest", kind: "write"}
  elif test("^(pr (view|list|checks|status|diff)|issue (view|list|status)|repo view|label list)$") then {api: "graphql", kind: "read"}
  elif test("^(run (list|view|download)|cache list|search [a-z]+|extension install|release (view|list|download))$") then {api: "rest", kind: "read"}
  elif test("^(run (rerun|cancel)|workflow run|cache delete|label create)$") then {api: "rest", kind: "write"}
  else {api: "graphql", kind: "write"} end;

# The class of a call `.`, a site with its `verb` and `input`, true when the
# call reads its request from `--input`. Such a GraphQL call names no query
# in its arguments, and the check cannot read the request, so it is a write,
# the dearest guess, as the router counts it (#5695).
def call_class:
  (.verb | class) as $class
  | if $class.api == "graphql" and .input == true then $class + {kind: "write"} else $class end;
