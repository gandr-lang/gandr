#!/usr/bin/env bash
# The codemod of the containers. The task runs it over the crates it names.
# A second run over the same sources changes no file. The task prints each
# site that no rule moves, with its file and its line.
#
# The rule moves a test too. A changed signature does not compile against a
# `vec!` of the old type. The lint does not read a test. The compiler does.
#
# - see: #8182
# - see: .config/ast-grep/containers
set -euo pipefail
export LC_ALL=C

root=$(git rev-parse --show-toplevel)
cd "$root"
config=.config/ast-grep/containers/sgconfig.yml
# The import rules are not in this list. A prelude name has no `use` to
# replace, and a std crate imports `Global` from `std::alloc`. The task
# inserts the import after the rules run.
rules='vec-is-small-vec|vec-in-is-small-vec-in|vec-new-in-is-small-vec-new-in|vec-with-capacity-in-is-small-vec-with-capacity-in|vec-new-is-small-vec-new|vec-with-capacity-is-small-vec-with-capacity|vec-macro-empty-is-small-vec-new|vec-macro-repeat-is-small-vec-from-iter|vec-macro-list-is-small-vec-from-iter|to-vec-is-small-vec-from-iter|vec-from-is-small-vec-from-iter|arc-slice-is-thin-shared|arc-is-shared|arc-call-is-shared-call|string-is-small-string|string-path-is-small-string|string-new-is-small-string-new|string-from-str-is-small-string|rc-is-shared|rc-call-is-shared-call'

census=false
dry=false
names=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --census) census=true ;;
    --dry-run) dry=true ;;
    *) names+=("$1") ;;
  esac
  shift
done

# The directory of a package name or of a directory name.
crate_dir() {
  local name=${1#gandr-}
  if [[ -d crates/$name ]]; then
    printf 'crates/%s\n' "$name"
    return
  fi
  echo "codemod:containers: no crate $1" >&2
  return 1
}

# A text count of the forms the rules read, over the paths named.
census_of() {
  local path
  printf 'form\tcount\n'
  local -a forms=(
    'Vec<'
    'Vec::new'
    'Vec::with_capacity'
    'Vec::from'
    'vec!'
    '.to_vec()'
    'String'
    'String::new'
    'String::from'
    'String::with_capacity'
    'format!'
    '.to_string()'
    '.to_owned()'
    'Arc<'
    'Arc::new'
    'Arc::downgrade'
    'Rc<'
    'Rc::new'
    'Weak<'
  )
  for form in "${forms[@]}"; do
    local count=0
    for path in "$@"; do
      local found
      found=$(git grep -F -c -e "$form" -- "$path" '*.rs' 2> /dev/null | awk -F: '{ total += $2 } END { print total + 0 }')
      count=$((count + found))
    done
    printf '%s\t%s\n' "$form" "$count"
  done
}

if [[ $census == true ]]; then
  if (( ${#names[@]} == 0 )); then
    census_of crates
  else
    paths=()
    for name in "${names[@]}"; do paths+=("$(crate_dir "$name")"); done
    census_of "${paths[@]}"
  fi
  exit 0
fi

(( ${#names[@]} > 0 )) || { echo "codemod:containers: name at least one crate" >&2; exit 2; }

mapfile -t files < <(
  for name in "${names[@]}"; do
    dir=$(crate_dir "$name")
    git ls-files -- "$dir/*.rs"
  done
)
(( ${#files[@]} > 0 )) || { echo "codemod:containers: the crates hold no Rust source" >&2; exit 2; }

if [[ $dry == true ]]; then
  ast-grep scan --config "$config" --filter "^($rules)\$" "${files[@]}"
  exit 0
fi

before=$(git hash-object "${files[@]}" | git hash-object --stdin)
ast-grep scan --config "$config" --filter "^($rules)\$" --update-all "${files[@]}"

# The import a file needs, inserted once. rustfmt then groups the lines.
insert_use() {
  local file=$1 line=$2
  if grep -q -F -x "$line" "$file"; then
    return
  fi
  # After the crate's inner attributes, before the first item. A file with
  # no item takes the line at the end.
  local tmp
  tmp=$(mktemp)
  awk -v line="$line" '
    BEGIN { placed = 0 }
    !placed && /^(pub(\([^)]*\))? )?(fn |struct |enum |trait |impl |mod |const |static |type |use |extern crate )/ {
      print line
      placed = 1
    }
    { print }
    END { if (!placed) print line }
  ' "$file" > "$tmp"
  mv "$tmp" "$file"
}

# A child module does not see the parent's imports. A `mod tests` that uses
# a moved type takes the same imports.
insert_into_tests() {
  local file=$1 line=$2
  local indented="    $line"
  if grep -q -F -x "$indented" "$file"; then
    return
  fi
  local tmp
  tmp=$(mktemp)
  awk -v line="$indented" '
    BEGIN { armed = 0 }
    /mod tests/ { armed = 1 }
    armed && /\{/ {
      print
      print line
      armed = 0
      next
    }
    { print }
  ' "$file" > "$tmp"
  mv "$tmp" "$file"
}

for file in "${files[@]}"; do
  needs_global=false
  if grep -q -E 'SmallVec|SmallString|Shared<|ThinShared' "$file"; then
    needs_global=true
  fi
  no_std=false
  dir=${file%%/src/*}
  dir=${dir%%/tests/*}
  if grep -q -h '#!\[no_std\]' "$dir"/src/lib.rs "$dir"/src/main.rs 2> /dev/null; then
    no_std=true
  fi
  if [[ $needs_global == true ]]; then
    if [[ $no_std == true ]]; then
      insert_use "$file" 'use alloc::alloc::Global;'
    else
      insert_use "$file" 'use alloc::alloc::Global;'
    fi
  fi
  if grep -q -E '\bSmallVec\b' "$file"; then
    insert_use "$file" 'use gandr_kernel_data::SmallVec;'
  fi
  if grep -q -E '\bCount::' "$file"; then
    insert_use "$file" 'use gandr_kernel_data::Count;'
  fi
  if grep -q -E '(^|[^:])SmallString\b' "$file"; then
    insert_use "$file" 'use gandr_kernel_data::SmallString;'
  fi
  if grep -q -E '\bThinShared\b' "$file"; then
    insert_use "$file" 'use gandr_kernel_data::ThinShared;'
  fi
  if grep -q -E '\bShared\b' "$file" && ! grep -q 'use gandr_kernel_data::Shared;' "$file"; then
    insert_use "$file" 'use gandr_kernel_data::Shared;'
  fi
  if awk '/mod tests/,0' "$file" | grep -q -E '\bSmallVec\b'; then
    insert_into_tests "$file" 'use alloc::alloc::Global;'
    insert_into_tests "$file" 'use gandr_kernel_data::SmallVec;'
  fi
  if awk '/mod tests/,0' "$file" | grep -q -E '\bSmallString\b'; then
    insert_into_tests "$file" 'use gandr_kernel_data::SmallString;'
  fi
done

# The dependency, in the order rustfmt does not read. The lines of
# `[dependencies]` stay sorted by the key.
for name in "${names[@]}"; do
  dir=$(crate_dir "$name")
  toml=$dir/Cargo.toml
  [[ -f $toml ]] || continue
  if grep -q 'gandr-kernel-data' "$toml"; then
    continue
  fi
  if [[ $dir == crates/kernel-data ]]; then
    continue
  fi
  tmp=$(mktemp)
  awk '
    BEGIN { in_deps = 0; placed = 0 }
    /^\[/ && $0 != "[dependencies]" { in_deps = 0 }
    $0 == "[dependencies]" { in_deps = 1 }
    in_deps && !placed && /^[a-z].*=/ && $0 > "gandr-kernel-data" {
      print "gandr-kernel-data.workspace = true"
      placed = 1
    }
    { print }
    END { if (!placed) print "gandr-kernel-data.workspace = true" }
  ' "$toml" > "$tmp"
  mv "$tmp" "$toml"
done

packages=()
for name in "${names[@]}"; do
  dir=$(crate_dir "$name")
  pkg=$(awk -F'"' '/^name = / { print $2; exit }' "$dir/Cargo.toml")
  packages+=("$pkg")
done

cargo fmt -p "${packages[@]}"

# A site the rules leave. A line under an expect is a repair, not a stay.
stay='((^|[^A-Za-z])Vec<|(^|[^A-Za-z])Vec::|(^|[^A-Za-z])vec!|[^A-Za-z]String[^A-Za-z]|String::|format!|\.to_string\(\)|\.to_owned\(\)|Arc<|Arc::|Rc<|Rc::|Weak<)'
echo "codemod:containers: sites that stay"
stayed=0
for file in "${files[@]}"; do
  while IFS=: read -r line text; do
    [[ -n $line ]] || continue
    if [[ $text == *'expect(std_container'* ]]; then
      continue
    fi
    printf '%s:%s:%s\n' "$file" "$line" "$text"
    stayed=$((stayed + 1))
  done < <(grep -n -E "$stay" "$file" || true)
done
echo "codemod:containers: $stayed sites stay"

after=$(git hash-object "${files[@]}" | git hash-object --stdin)
if [[ $before == "$after" ]]; then
  echo "codemod:containers: a second run changes no file"
else
  echo "codemod:containers: files changed"
fi
