# One crate's boundary surface for the bootstrap census (`report:bootstrap-census`,
# #2896), read from the rustdoc JSON of its library built without private
# items, as `purposes:items` builds it. Prints one compact object:
#
#   {"types": n, "foreign": ["<crate>::<path>", …], "clauses": n, "witnesses": n}
#
# - `types`: the types the crate's own items mention, each counted once by the
#   item that defines it, wherever a signature, a field, a variant, an alias
#   or a constant names it. An implementation's own items are left out when
#   it implements a trait, whose signatures the trait fixes. Traits named in
#   bounds are not types and are not counted;
# - `foreign`: those of them another crate defines, by the path rustdoc
#   records for the definition, sorted;
# - `clauses`: the specification bullets (`- requires:`, `- ensures:`,
#   `- provides:`, `- fails:`, `- panics:`) in the documentation of the
#   crate's own items, a trait implementation's included;
# - `witnesses`: the `- witness:` bullets there, each naming a contract test.
#
# A `#[spec]` attribute does not reach rustdoc's JSON, which the attribute's
# macro has consumed, so the task counts those in the sources. The reading is
# rustdoc's JSON format 58; another format stops the program with an error
# naming it.

if .format_version != 58 then
  error("rustdoc JSON format \(.format_version): .config/census/surface.jq reads format 58; read its `index`, `paths` and type forms against the new format and move the version with it")
end
| .paths as $paths
| ([.index[] | select(.inner.impl? and .inner.impl.trait != null) | .inner.impl.items[] | tostring]) as $fixed
| [.index | to_entries[] | select(.value.crate_id == 0)] as $own
| [$own[]
   | select(.key as $key | $fixed | index($key) | not)
   | .value.inner
   | select(has("impl") | not)
   | ..
   | objects
   | select(has("resolved_path"))
   | .resolved_path.id
   | tostring]
| unique
| map($paths[.] // {crate_id: null, path: ["?"]}) as $types
| {
    types: ($types | length),
    foreign: [$types[] | select(.crate_id != 0) | .path | join("::")] | sort,
    clauses: [$own[] | .value.docs // "" | scan("(?m)^- (?:requires|ensures|provides|fails|panics):")] | length,
    witnesses: [$own[] | .value.docs // "" | scan("(?m)^- witness:")] | length
  }
