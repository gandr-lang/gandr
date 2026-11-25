# The pick in `next.jq`'s answer (#5178): the one line of the form
# `<number><TAB><bucket><TAB><title>`, sourced by `claim:next`. Every other
# line of the answer carries a prefix (`held:`, `blocked:`, `sections due:`
# and the rest), so the pick is read by its own form, never by a list of the
# prefixes it lacks.
claim_pick() {
  awk -F '\t' '/^[0-9]+\t/ { print; exit }'
}
