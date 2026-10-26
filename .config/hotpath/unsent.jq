# The one `kind:ci` issue that holds main's hotpath reports not uploaded
# (#2641), read by `ci:hotpath-unsent`: `{issue, run}`, where `issue` is the
# open issue of that title, `{number, body}`, or null, and `run` the push's
# `{commit, url, benchmarks}`. Gives `{number, title, body}`: the issue's
# number (null to open one) and its body with the run's row added, its
# rows in the order they were filed. A run already filed adds nothing.

def title: "ci: hotpath reports not uploaded on main";
def header: "| Commit | Run | Benchmarks |\n| --- | --- | --- |\n";
def prose:
  "Main's push runs the hotpath series and uploads each report to hotpath Cloud. "
  + "A failed upload is a report failure, never a red `main`: the job passes with a warning, "
  + "keeps the measurements in the run's `hotpath-<commit>` artifact, and `mise run ci:hotpath-unsent` "
  + "adds the run's row here. Remove a row once its cause is fixed; the issue closes with the last.\n\n";
def row: "| \(.commit[0:9]) | [\(.url | split("/") | last)](\(.url)) | \(.benchmarks | map("`\(.)`") | join(", ")) |\n";

(.run | row) as $row
| if .issue == null then {number: null, title: title, body: (prose + header + $row)}
  else
    (.issue.body | gsub("\r"; "")) as $body
    | {number: .issue.number, title: title,
       body: (if $body | contains($row) then $body else ($body | sub("\n*$"; "\n")) + $row end)}
  end
