def escaped: gsub("\\|"; "\\|");

"This issue lists the mutants in `\(.crate)` that the campaign leaves alive.\n\n"
+ "Each row needs a witness. A missing witness must name its function.\n\n"
+ "| mutant |\n| --- |\n"
+ (.mutants | map("| `\(. | escaped)` |") | join("\n"))
+ "\n\n\(.mutants | length) mutant(s) alive."
