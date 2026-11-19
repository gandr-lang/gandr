# A `cfg` predicate read over a host's platform atoms (#4441), for the
# witness resolution `resolve.jq` makes: a witness test gated off this host
# resolves as the gate host's whose atoms it holds on.
#
# The platform atoms are the keys below and the names `unix` and `windows`.
# Any other atom (`feature = "…"`, `test`, a `--cfg` of the build's) reads as
# holding: the gate's hosts build one configuration, and only the platform
# separates them.

def platform_keys:
  ["target_arch", "target_endian", "target_env", "target_family", "target_os", "target_pointer_width", "target_vendor"];

def platform_names: ["unix", "windows"];

# `rustc --print cfg`'s text as a host's platform atoms: each key's values,
# and each name present as `true`.
def atoms:
  [split("\n")[]
   | select(length > 0)
   | capture("^(?<key>[a-z_]+)(=\"(?<value>[^\"]*)\")?$")
   | select((.value != null and (.key as $k | platform_keys | index($k)))
       or (.value == null and (.key as $k | platform_names | index($k))))]
  | reduce .[] as $atom ({};
      if $atom.value == null then .[$atom.key] = true
      else .[$atom.key] += [$atom.value] end);

# A predicate's parse from token `$i` of `$t`: `{ast, i}`, `i` past it.
def parse_at($t; $i):
  if $i >= ($t | length) then error("cfg: the predicate ends early")
  elif $t[$i + 1] == "=" then
    {ast: {key: $t[$i], value: ($t[$i + 2] | .[1:-1])}, i: ($i + 3)}
  elif $t[$i + 1] == "(" then
    {items: [], i: ($i + 2)}
    | until($t[.i] == ")";
        if .i >= ($t | length) then error("cfg: `\($t[$i])(` is never closed") else . end
        | . as $state
        | parse_at($t; $state.i) as $parsed
        | {items: ($state.items + [$parsed.ast]),
           i: (if $t[$parsed.i] == "," then $parsed.i + 1 else $parsed.i end)})
    | {ast: {op: $t[$i], args: .items}, i: (.i + 1)}
  else {ast: {name: $t[$i]}, i: ($i + 1)}
  end;

# The text inside `#[cfg(…)]` as a tree: `{name}`, `{key, value}` or
# `{op, args}`.
def predicate:
  [scan("[A-Za-z_][A-Za-z0-9_]*|\"[^\"]*\"|[(),=]")] as $t
  | parse_at($t; 0)
  | if .i == ($t | length) then .ast else error("cfg: text past the predicate") end;

# Whether a predicate tree holds on the host `$host`, its platform atoms.
def holds($host):
  if has("op") then
    if .op == "all" then all(.args[]; holds($host))
    elif .op == "any" then any(.args[]; holds($host))
    elif .op == "not" then (.args[0] | holds($host)) | not
    else error("cfg: no operator `\(.op)`")
    end
  elif has("key") then
    .key as $key | .value as $value
    | if platform_keys | index($key) then ($host[$key] // []) | index($value) != null
      else true
      end
  else
    .name as $name
    | if platform_names | index($name) then $host[$name] == true else true end
  end;
