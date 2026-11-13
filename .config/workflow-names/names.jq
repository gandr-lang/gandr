# The names of the workflows (#7099). Each workflow takes a name by its area
# and then its act, in lower case with hyphens, as a crate does. Its file
# takes the same name. GitHub keys a workflow on the path of its file, so a
# later rename leaves the old runs under an old entry.
#
# Input: an array of `{path, name}`, one for each file under
# `.github/workflows/`, with `name` null where the file sets none.
# Output: one line for each refusal, and none when each name holds.

# The areas that a name starts with. A new area joins this list in the pull
# request that needs it.
def areas: ["landing", "nightly", "report", "build", "tracker"];

def stem: split("/") | last | sub("\\.ya?ml$"; "");

.[]
| .path as $path
| ($path | stem) as $stem
| if .name == null then "\($path): it sets no `name:`; its name is `\($stem)`"
  else
    .name as $name
    | (if $name != $stem then "\($path): its name `\($name)` differs from the stem of its file, `\($stem)`" else empty end),
      (if $name | test("^[a-z0-9]+(-[a-z0-9]+)*$") then empty else "\($path): its name `\($name)` is not lower case with hyphens" end),
      (($name | split("-")) as $parts
        | if $parts[0] | IN(areas[]) | not then "\($path): its name `\($name)` starts with `\($parts[0])`, which is no area of \(areas | map("`\(.)`") | join(", "))"
          elif ($parts | length) < 2 then "\($path): its name `\($name)` is its area alone; an act follows the area"
          else empty end)
  end
