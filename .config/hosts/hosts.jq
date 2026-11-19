# The hosts block (#6880). One row names a runner label class. The row
# counts the runners of that class that are online, and the ones that are
# busy. It names the newest scheduled run of the workflows on that class.
# A workflow's newest scheduled run pages the fixer when it failed or timed
# out. A class with no online runner for one hour pages too. A scheduled run
# that stays queued for one hour is that page when the runner list cannot
# be read. A workflow on our runners that the owner table does not name is
# a row.
#
# The input is one object in a file. `runners` is the REST list, or null
# when the read is refused. `runs` is the scheduled runs. `owners` maps a
# workflow name to the lane that owns it. `workflows` names the workflows
# whose jobs use a runner of ours. `now` is seconds. `offline` maps a class
# to the seconds it was first read with no online runner.
def classes:
  [
    {class: "integration", labels: ["integration"], workflows: ["nightly-sweeps", "nightly-riscv64-tests"]},
    {class: "factory", labels: ["factory"], workflows: []},
    {class: "RISCV64", labels: ["Linux", "RISCV64"], workflows: ["nightly-sweeps", "nightly-riscv64-tests"]}
  ];

def has_labels($need):
  . as $runner
  | all($need[]; . as $n | any($runner.labels[]?; .name == $n));

def clock:
  .[11:16] + "Z";

def newest_named($names):
  if $names == [] then null
  else [ .runs[]? | select(.name as $n | $names | index($n)) ] | sort_by(.created_at) | last // null
  end;

def newest_one($name):
  [ .runs[]? | select(.name == $name) ] | sort_by(.created_at) | last // null;

def failed:
  .conclusion == "failure" or .conclusion == "timed_out";

def verdict:
  if .conclusion == "failure" then "failed"
  elif .conclusion == "timed_out" then "timed out"
  elif .status == "queued" then "queued"
  else (.conclusion // .status)
  end;

def queued_long($now):
  .status == "queued" and (($now - (.created_at | fromdateiso8601)) >= 3600);

def count_cell($c):
  if .runners == null then {online: "unread", busy: "unread"}
  else
    [ .runners[]? | select(has_labels($c.labels)) ] as $rows
    | {online: ([$rows[] | select(.status == "online")] | length),
       busy: ([$rows[] | select(.busy == true)] | length)}
  end;

def run_cell($c):
  newest_named($c.workflows) as $run
  | if $run == null then "no scheduled run"
    else "run \($run.name) \($run | verdict) \($run.id) since \($run.created_at | clock)"
    end;

def page_line($run):
  "RUN \($run.name) \($run.id): a scheduled run on our runners \($run | verdict). Repair it ahead of your queue.";

def offline_mark($c; $now):
  if .runners == null then "clear"
  else
    [ .runners[]? | select(has_labels($c.labels)) ] as $rows
    | if ($rows == []) or any($rows[]; .status == "online") then "clear"
      else
        (.offline[$c.class] // null) as $since
        | if $since == null then "start"
          elif ($now - $since) >= 3600 then "page"
          else "keep"
          end
      end
  end;

. as $in
| ($in.now) as $now
| ($in.owners // {}) as $owners
| ($in.workflows // []) as $workflows
| [ classes[] as $c | ($in | count_cell($c)) as $n | ($in | run_cell($c)) as $run | "  \($c.class): online \($n.online), busy \($n.busy); \($run)" ] as $rows
| [ $workflows[] as $name | ($in | newest_one($name)) as $run | select($run != null and ($run | failed)) | {run: $run.id, line: page_line($run)} ] as $red_pages
| [ $workflows[] as $name | ($in | newest_one($name)) as $run | select($in.runners == null and $run != null and ($run | queued_long($now))) | {run: $run.id, line: page_line($run)} ] as $queue_pages
| [ classes[] as $c | ($in | offline_mark($c; $now)) as $mark | {class: $c.class, mark: $mark} ] as $marks
| [ $marks[] | select(.mark == "page") | {run: ("offline-" + .class), line: "RUN \(.class) offline: no runner of that class is online for one hour. Repair it ahead of your queue."} ] as $off_pages
| [ $workflows[] | select(. as $n | ($owners[$n] // "") == "") ] as $none
| {
    lines: (["hosts:"] + $rows + ["  unowned: \(if $none == [] then "none" else ($none | join(", ")) end)"]),
    pages: ($red_pages + $queue_pages + $off_pages),
    offline: (reduce $marks[] as $m ({}; if $m.mark == "start" then .[$m.class] = $now elif $m.mark == "keep" or $m.mark == "page" then .[$m.class] = $in.offline[$m.class] else . end))
  }
