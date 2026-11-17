# The bytes of each frame of the kernel's checks (#7359), read from rustc's
# `-Zprint-type-sizes` over `gandr-kernel-core`. Each frame enum gives its
# size first, which each of its frames takes on its stack, whatever its
# variant. Then each variant gives its size, largest first, as rustc prints
# them.
#
# Input: the text that rustc prints, as one string. Output: one Markdown row
# for each enum and each of its variants, as `| Frame | each frame | 72 |`.
# A text that names no frame enum of the kernel's checks is refused.

# The frame enum that `$line` opens, as {frame, bytes}, or null.
def opened($line):
  [$line | capture("^print-type-size type: `check::(?<frame>Frame|TypeLevelFrame)`: (?<bytes>[0-9]+) bytes")]
  | first;

# The variant that `$line` sizes, as {variant, bytes}, or null.
def sized($line):
  [$line | capture("^print-type-size {5}variant `(?<variant>[A-Za-z0-9_]+)`: (?<bytes>[0-9]+) bytes")]
  | first;

reduce (split("\n")[]) as $line ({frame: null, rows: []};
  if $line | startswith("print-type-size type: ") then
    opened($line) as $enum
    | if $enum == null then
        .frame = null
      else
        .frame = $enum.frame | .rows += ["| \($enum.frame) | each frame | \($enum.bytes) |"]
      end
  elif .frame == null then
    .
  else
    sized($line) as $variant
    | if $variant == null then . else .rows += ["| \(.frame) | \($variant.variant) | \($variant.bytes) |"] end
  end)
| if .rows == [] then error("the type sizes name no frame of the kernel's checks") else .rows | join("\n") end
