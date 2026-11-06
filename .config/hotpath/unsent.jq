# The one `kind:ci` issue that holds main's hotpath reports not uploaded
# (#2641), read by `ci:hotpath-unsent`: `{issue, run}`, where `issue` is the
# open issue of that title, `{number, body}`, or null, and `run` the push's
# `{commit, url, benchmarks}`. Gives `{number, title, body}`: the issue's
# number (null to open one) and its body with the run's row added, its
# rows in the order they were filed. A run already filed adds nothing. A new
# issue opens with the sentence that says what it is, and its table follows
# a one-sentence lead (#3596).

def title: "ci: hotpath reports not uploaded on main";
def header: "| Commit | Run | Benchmarks |\n| --- | --- | --- |\n";
def prose:
  "This issue lists the pushes to `main` whose hotpath reports fail to upload to hotpath Cloud.\n\n"
  + "A failed upload is a report failure, never a red `main`. "
  + "The job passes with a warning and keeps the measurements in the `hotpath-<commit>` artifact of its run. "
  + "`mise run ci:hotpath-unsent` then adds the row of the run. "
  + "Remove a row once a fix for its cause lands. The issue closes with the last row.\n\n"
  + "The table gives each run and the benchmarks whose reports it does not upload.\n\n";
def row: "| \(.commit[0:9]) | [\(.url | split("/") | last)](\(.url)) | \(.benchmarks | map("`\(.)`") | join(", ")) |\n";

(.run | row) as $row
| if .issue == null then {number: null, title: title, body: (prose + header + $row)}
  else
    (.issue.body | gsub("\r"; "")) as $body
    | {number: .issue.number, title: title,
       body: (if $body | contains($row) then $body else ($body | sub("\n*$"; "\n")) + $row end)}
  end
