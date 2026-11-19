# The label set's calls (#2902), sourced by `issue:file`, `issue:labels` and
# `report:deps`; the tasks pin jq and yq.

labels_dir=$(dirname "${BASH_SOURCE[0]}")

# `.config/issues/defaults.toml` as JSON.
labels_defaults() {
  yq -p toml -o json -I0 '.' "$labels_dir/defaults.toml"
}

# The lines `labelled` gives for a label list given as a JSON array
# ($1), the defaults as JSON ($2): `add<TAB><label>` and `refuse<TAB><why>`.
labels_plan() {
  jq -n -r -L "$labels_dir" --argjson labels "$1" --argjson defaults "$2" \
    '{labels: $labels, defaults: $defaults}' | jq -r -L "$labels_dir" -f "$labels_dir/filed.jq"
}
