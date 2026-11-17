include "accounted";

.kept as $kept
| .named as $named
| [.branches[] | . as $branch | {branch: $branch, accounted: ($branch | accounted($kept; $named))}]
