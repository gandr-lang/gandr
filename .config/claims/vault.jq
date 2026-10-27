# Vault pages named in a unit's `## Sources`, read against the vault (#2793):
# an issue names a page by its filename, as `units.md` allows, and the tree
# cites it as `vault:` and the page's `mint:`. `unit:check` shows each name's
# mint and refuses a name no page carries; `pr:open` writes the mint beside
# the name in `## Sources read` and asks the crates a change touches to cite
# each primary page (`opening.jq`).
#
# The pages are `vault_pages`'s (`.config/references/vault.bash`): each
# filename its pages' mints, `null` for a page with none. The tree's names are
# the filenames the checked-out tree carries, so `README.md` or a file named
# by its path is the tree's and no vault page.
#
# The module reads lines its caller hands it and calls no definition of
# `sections.jq`: jq 1.8 aborts compiling a module's definition with `$`
# parameters that calls another module's (`expand_call_arglist`).

# The bare filenames a line names: its backquoted spans that are a filename
# ending `.md`, with no directory.
def vault_names: [match("`([^`/\\s]+\\.md)`"; "g").captures[0].string] | unique;

# A filename read against the vault, or null for one the tree carries:
#   {name, verdict: "resolved", mint}   one page carries it, with its mint;
#   {name, verdict: "unminted"}         one page carries it, with no mint;
#   {name, verdict: "ambiguous", count} several pages carry it;
#   {name, verdict: "unknown"}          no page carries it.
def vault_reading($pages; $tree):
  . as $name
  | if $tree[$name] then null
    else ($pages[$name] // null) as $mints
    | if $mints == null then {name: $name, verdict: "unknown"}
      elif ($mints | length) > 1 then {name: $name, verdict: "ambiguous", count: ($mints | length)}
      elif $mints[0] == null then {name: $name, verdict: "unminted"}
      else {name: $name, verdict: "resolved", mint: $mints[0]}
      end
    end;

# The tree's filenames, from their newline-separated text, as a set.
def vault_tree: split("\n") | map(select(. != "") | {key: ., value: true}) | from_entries;

# Each vault page the lines of an issue's `## Sources` name, as its reading
# with the line naming it and whether the line marks the page primary.
def vault_sources($pages; $tree):
  .[]
  | select(test("^[-*] "))
  | . as $line
  | vault_names[]
  | vault_reading($pages; $tree)
  | select(. != null)
  | . + {line: $line, primary: ($line | test("\\bprimary\\b"; "i"))};

# What `unit:check` prints for a reading: a refusal for a name no page
# carries, otherwise a line showing what the name resolves to.
def vault_shown:
  if .verdict == "unknown" then "refuse\t`## Sources` line `\(.line)` names `\(.name)`, which no vault page carries: name the vault page by its filename, or the tree's file by its path"
  elif .verdict == "resolved" then "show\t`\(.name)` → `vault:\(.mint)`"
  elif .verdict == "ambiguous" then "show\t`\(.name)` → \(.count) vault pages carry it, so no one mint"
  else "show\t`\(.name)` → a vault page with no `mint:`"
  end;

# A body with `vault:<mint>` written after each resolved filename an item of
# its `## Sources read` keys and does not already carry, so the item's head
# holds the citation key a crate carries verbatim.
def vault_annotated($pages; $tree):
  split("\n") as $lines
  | ([range(0; $lines | length) | select($lines[.] | test("^## Sources read\\s*(:.*)?$"))] | first) as $start
  | if $start == null then .
    else ([range($start + 1; $lines | length) | select($lines[.] | test("^## "))] | first // ($lines | length)) as $end
    | [range(0; $lines | length) as $i
        | $lines[$i]
        | if $i > $start and $i < $end and test("^[-*] ") then
            . as $line
            | reduce ([vault_names[] | vault_reading($pages; $tree) | select(. != null and .verdict == "resolved")][]) as $page ($line;
                if contains("`vault:\($page.mint)`") then .
                else "`\($page.name)`" as $span
                | index($span) as $at
                | .[:$at] + $span + " `vault:\($page.mint)`" + .[$at + ($span | length):]
                end)
          else .
          end]
    | join("\n")
    end;
