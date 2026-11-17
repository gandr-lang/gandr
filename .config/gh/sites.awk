# The `gh` call sites of the files given (#5061): one line per call,
# `<file>\t<scope>\t<verb>`, read by `check:gh-budget` and by `pr:open`.
#
# - A call is `gh` at a word boundary, followed by a subcommand, on a line
#   that is not a comment and not a task's `description`, which is prose. A
#   line that ends in `\` continues on the next.
# - The scope is where the call stands. In a mise task file it is the task,
#   then `/` and the shell function around the call. In a shell file it is
#   the function around the call, or `-` at the top level. In a workflow it
#   is the job, then `/` and the step's name, or its id when it has no name.
# - The verb is the subcommand and its first word, as `pr view`. For `gh api`
#   it is `api graphql`, or `api` and the REST method: the method `-X` or
#   `--method` names, else POST when the call gives a field, else GET, as gh
#   chooses it.
# - With `-v text=1`, a fourth field holds the call's text from `gh` to the
#   end of its line, so a measurement can run it.
# - `calls.toml` is the table of these calls, data and not a task file, so
#   its triggers' prose names no call.

function reset_file() {
  task = ""; fn = ""; job = ""; step = ""; in_jobs = 0; item = -1
  kind = FILENAME ~ /\.toml$/ ? "toml" : FILENAME ~ /\.ya?ml$/ ? "yml" : "sh"
}

function scope() {
  if (kind == "yml") return job == "" ? "-" : (step == "" ? job : job "/" step)
  if (kind == "toml") return task == "" ? "-" : (fn == "" ? task : task "/" fn)
  return fn == "" ? "-" : fn
}

# The verb of the call that starts at the head of `rest`.
function verb(rest,    words, n, sub_, command, method) {
  n = split(rest, words, /[ \t]+/)
  sub_ = words[2]
  if (sub_ != "api") return sub_ " " words[3]
  command = rest
  sub(/[|;)].*$/, "", command)
  sub(/&&.*$/, "", command)
  if (command ~ /[ \t]graphql([ \t]|$)/) return "api graphql"
  method = ""
  if (match(command, /(-X[ \t]*|--method[ \t=]+)[A-Za-z]+/)) {
    method = substr(command, RSTART, RLENGTH)
    sub(/^(-X[ \t]*|--method[ \t=]+)/, "", method)
    method = toupper(method)
  }
  else if (command ~ /(^|[ \t])(-f|-F|--field|--raw-field|--input)([ \t=]|[^ \t])/) method = "POST"
  else method = "GET"
  return "api " method
}

FNR == 1 { reset_file(); held = "" }

FILENAME ~ /(^|\/)\.config\/gh\/calls\.toml$/ { nextfile }

{
  line = held $0
  if (line ~ /\\$/) { held = substr(line, 1, length(line) - 1) " "; next }
  held = ""
}

kind == "toml" && match(line, /^\[(tasks\.)?"[^"]+"\]/) {
  task = substr(line, RSTART, RLENGTH)
  sub(/^\[(tasks\.)?"/, "", task); sub(/"\]$/, "", task)
  fn = ""
  next
}

kind == "toml" && line ~ /^description[ \t]*=/ { next }

kind == "yml" {
  if (line ~ /^jobs:[ \t]*$/) { in_jobs = 1; next }
  if (line ~ /^[^ \t#]/) in_jobs = 0
  if (in_jobs && match(line, /^  [A-Za-z0-9_-]+:[ \t]*$/)) {
    job = substr(line, 3); sub(/:.*$/, "", job); step = ""; item = -1
    next
  }
  if (match(line, /^[ \t]*- /)) {
    item = RLENGTH; step = ""; named = 0
  }
  if (item >= 0 && match(line, /^[ \t]*(- )?(name|id):[ \t]*/)) {
    value = substr(line, RLENGTH + 1)
    key = line; sub(/^[ \t]*(- )?/, "", key); sub(/:.*$/, "", key)
    gsub(/^["']|["'][ \t]*$/, "", value)
    if (key == "name") { step = value; named = 1 }
    else if (!named) step = value
  }
}
kind != "yml" && match(line, /^[ \t]*(function[ \t]+)?[A-Za-z_][A-Za-z0-9_]*[ \t]*\(\)[ \t]*\{?/) {
  opened = gsub(/\{/, "{", line) - gsub(/\}/, "}", line)
  if (opened > 0 || line !~ /\{/) {
    fn = line; sub(/^[ \t]*(function[ \t]+)?/, "", fn); sub(/[ \t]*\(.*$/, "", fn)
  }
}

kind != "yml" && line ~ /^\}/ { fn = "" }

line ~ /^[ \t]*#/ { next }

{
  rest = line
  while (match(rest, /(^|[^A-Za-z0-9_.\/$-])gh[ \t]+[a-z][a-z-]*([ \t]|$)/)) {
    start = RSTART
    if (substr(rest, start, 1) != "g") start++
    rest = substr(rest, start)
    print FILENAME "\t" scope() "\t" verb(rest) (text ? "\t" rest : "")
    rest = substr(rest, 3)
  }
}
