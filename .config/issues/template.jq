# A filer's issue body (#3112): the template `.config/issues/templates/
# <filer>.md` it is applied to, every `{{field}}` filled from `$fields`, after
# the filer's observation `$observation` (its lead and `## Observation`). The
# template carries every other section of a unit, so the body passes
# `unit:check` as filed. A row whose answer turns on what the observation
# measures is itself a field the filer states, as the hotpath template's
# `descent` reading and `sharing` concern: what a budget protects differs by
# function. A field the template names that `$fields` lacks, or one `$fields`
# gives that the template never names, is refused: a misspelt field never
# files a body with a hole in it.

def placeholders: [scan("\\{\\{([a-z][a-z-]*)\\}\\}") | .[0]] | unique;

def render($fields; $observation):
  . as $template
  | placeholders as $names
  | ($names - ($fields | keys)) as $missing
  | (($fields | keys) - $names) as $unknown
  | if $missing != [] then
      error("the template names \($missing | map("`\(.)`") | join(", ")), which the fields do not give")
    elif $unknown != [] then
      error("the fields give \($unknown | map("`\(.)`") | join(", ")), which the template never names")
    else
      ($observation | sub("\\s+$"; "")) + "\n\n"
        + reduce $names[] as $name ($template; gsub("\\{\\{\($name)\\}\\}"; $fields[$name] | tostring))
    end;
