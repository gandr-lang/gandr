# `template.jq`'s `render` over one case (#3112), for `check:issues`:
# input `{template, fields, observation}`, output the body `issue:file
# --template` files.

include "template";

.fields as $fields | .observation as $observation | .template | render($fields; $observation)
