# The body of one static unwitnessed-mutants collector (#3211).
#
# Input: `{crate, mutants}`, where `mutants` has one name per static gap.
# Output: the collector body as raw text.

def escaped: gsub("\\|"; "\\|");

"This issue lists the mutants of `\(.crate)` that no witness names.\n\n"
+ "No build starts. Each row is a static coverage gap.\n\n"
+ "| mutant |\n| --- |\n"
+ (.mutants | map("| `\(. | escaped)` |") | join("\n"))
+ "\n\n\(.mutants | length) unwitnessed mutant(s)."
