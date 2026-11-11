#!/usr/bin/env bash
# The scope of a change of `//` comments alone (#6648), run by
# `check:gate-scope`. Each case builds a scratch repository whose trunk holds
# one crate source, edits it, and reads what `select.bash` selects for the
# landing's gate. A `//` edit selects neither `check:doc` nor `check:corpus`.
# A `///` edit, a blank line and one token of code beside a comment select
# both. A `.rs` edit selects no `check:prose`, and a `.gandr` comment edit
# selects it.
set -euo pipefail
here="$(cd "${BASH_SOURCE[0]%/*}" && pwd)"
select="$here/select.bash"
source "$here/../pr-stack/trunk.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
cases=0
tasks='["check:claims","check:corpus","check:doc","check:landing","check:prose","check:tests-enforcing"]'
light=$'check:claims\ncheck:landing\ncheck:tests-enforcing'
whole=$'check:claims\ncheck:corpus\ncheck:doc\ncheck:landing\ncheck:tests-enforcing'

fail() {
  echo "comments case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A repository at `$1` whose `origin/$trunk` holds one crate source and one
# corpus source, each with a comment above its code.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  git config user.email gate@example.invalid
  git config user.name gate
  git config commit.gpgsign false
  mkdir -p crates/core-term/src corpus/model
  printf '%s\n' '// The count.' 'pub const N: u8 = 1;' > crates/core-term/src/lib.rs
  printf '%s\n' '/// The count.' 'def n = 1 ;' > corpus/model/count.gandr
  git add . && git commit --quiet -m base
  git update-ref "refs/remotes/origin/$trunk" HEAD
}

# `$1` names the case, `$2` the file, `$3` its new text, `$4` the selection
# the landing's gate makes.
check() {
  local got
  cases=$((cases + 1))
  got=$(
    setup "$scratch/$cases"
    printf '%s\n' "$3" > "$2"
    GATE_TASKS=$tasks "$select" --landing 2>&1 || echo "exit $?"
  )
  [[ $got == "$4" ]] || fail "$1" "$got"
}

check "#6648: a \`//\` edit in a crate selects neither check:doc nor check:corpus" \
  crates/core-term/src/lib.rs $'// The count of items.\npub const N: u8 = 1;' "$light"
check "#6648: a \`///\` edit selects check:doc and check:corpus" \
  crates/core-term/src/lib.rs $'/// The count.\npub const N: u8 = 1;' "$whole"
check "#6648: one token of code beside a comment selects check:doc and check:corpus" \
  crates/core-term/src/lib.rs $'// The count.\npub const N: u8 = 2;' "$whole"
check "#6648: a blank line beside a comment reads as code" \
  crates/core-term/src/lib.rs $'// The count.\n\npub const N: u8 = 1;' "$whole"
check "#6648, #6725: a comment edit in a corpus source selects check:prose and the suite that reads the corpus" \
  corpus/model/count.gandr $'/// The count of items.\ndef n = 1 ;' $'check:claims\ncheck:corpus\ncheck:prose\ncheck:tests-enforcing'

# The change of a commit: `select.bash <commit>` reads the classifier over
# the commit's own change, as `passed.bash` reads a head (#5076).
cases=$((cases + 1))
got=$(
  setup "$scratch/$cases"
  printf '%s\n' '// The count of items.' 'pub const N: u8 = 1;' > crates/core-term/src/lib.rs
  git commit --quiet -am comment
  GATE_TASKS=$tasks "$select" --landing HEAD 2>&1 || echo "exit $?"
)
[[ $got == "$light" ]] || fail "#6648: a commit of a \`//\` edit selects neither check:doc nor check:corpus" "$got"

(( failed == 0 )) || exit 1
echo "gate comments OK: $cases changes select check:doc, check:corpus and check:prose by what they touch"
