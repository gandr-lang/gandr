# A body the unit form wrote, made a unit's body (#3113). GitHub writes each
# field of `.github/ISSUE_TEMPLATE/unit.yml` as `### <label>` and its answer,
# `_No response_` for an optional field left empty; a unit's sections are
# `## ` headings (`sections.jq`), under which a `### ` line would read as the
# section before's content. The Kind and Area answers become labels and
# leave the body, the Brief becomes the lead, every other field its `## `
# section, and a field left empty is dropped. A body opening otherwise is no
# form's and gives null: the issues workflow leaves it as filed.
#
# Input: the body, a string. Output: `{body, labels}`, or null.

def fields:
  ["Kind", "Area", "Brief", "Sources", "Readings", "Concerns", "Ledger", "The shape", "Try first",
   "Not in this slice", "After"];

split("\n") | map(sub("\r$"; ""))
| if (map(select(test("\\S"))) | first) != "### Kind" then null
  else
    reduce .[] as $line ({fields: [], at: null};
      ($line | capture("^### (?<name>.+?)\\s*$").name // null) as $name
      | if $name != null and (fields | index($name)) != null then
          .fields += [{name: $name, lines: []}] | .at = (.fields | length - 1)
        elif .at == null then .
        else .fields[.at].lines += [$line]
        end)
    | [.fields[] | {name, text: (.lines | join("\n") | sub("^\\s+"; "") | sub("\\s+$"; ""))}
        | select(.text != "" and .text != "_No response_")] as $answers
    | def answer($name): first($answers[] | select(.name == $name) | .text) // null;
      {body: ([answer("Brief") // empty]
              + [$answers[] | select(IN(.name; "Kind", "Area", "Brief") | not) | "## \(.name)\n\n\(.text)"]
              | join("\n\n") + "\n"),
       labels: ([answer("Kind"), answer("Area")] | map(values | split(",")[] | sub("^\\s+"; "") | sub("\\s+$"; ""))
                | map(select(test("^(kind|area):"))))}
  end
