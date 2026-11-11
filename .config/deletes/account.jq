# The reading of a `## Deletes` table (#6817): its rows and what a row
# covers. `deletes.jq` and `check.bash` include it.

include "sections";

# The acts a row takes.
def acts: ["deleted", "moved", "renamed", "merged", "narrowed", "restored"];

# The columns of the `## Deletes` table, by the header's words.
def columns: {item: "item", origin: "origin", act: "act", why: "why", future: "future use",
  instead: "in place of deletion", after: "after", witness: "witness", signoff: "sign-off"};

# Whether a cell holds an answer: text that is no dash and no blank.
def answered: (. // "") | gsub("^[\\s—–-]+|[\\s—–-]+$"; "") | length > 0;

# The rows of the `## Deletes` table, each keyed by the columns above, or
# null when the body has no such section. A section that says `none` and
# holds no table has no rows.
def deletes_rows:
  (section("Deletes")) as $section
  | if $section == null then null
    else [$section | rows] as $table
    | if ($table | length) == 0 then []
      else ($table[0].cells | map(ascii_downcase | gsub("\\*"; ""))) as $header
      | [$table[1:][]
          | .cells as $cells
          | columns
          | with_entries(.value as $word | ($header | index($word)) as $at | .value = (if $at == null then null else $cells[$at] end))
          | .act |= ((. // "") | ascii_downcase | gsub("`"; "") | gsub("^\\s+|\\s+$"; ""))]
      end
    end;

# Whether the thing `$thing` is the row item `$item` or under it: the same
# path, a path below it, the item of a trait implementation for it, or a
# spelling of its own.
def covers($item; $thing):
  any(($thing.names // [$thing.id])[];
    . == $item or startswith($item + "::") or contains("<" + $item + " ") or contains("<" + $item + ">"));

# The last segment of a path, without a trait implementation's brackets.
def segment: sub("^.*::"; "") | gsub("[<>]"; "");

# Whether the comment `$c` comes from a login of `architects.txt`, with the
# heading that the login's line asks of it.
def signer($c; $architects):
  $architects[$c.author] as $heading | $heading != null and ($c.body | contains($heading));

# Whether the comment `$c` signs the row item `$item` for the files `$files`:
# an architect's comment that names the item and a commit, says `signed`,
# and sees no later change of those files.
def signs($c; $item; $files; $architects):
  signer($c; $architects)
  and ($c.body | test("\\bsigned\\b"))
  and ($c.body | contains($item))
  and $c.sha != null and $c.changed != null
  and ([$files[] | IN($c.changed[])] | any | not);

