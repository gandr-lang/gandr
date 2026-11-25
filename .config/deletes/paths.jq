# The path in the tree of a file that the evidence records hold. A module
# that a `#[path]` attribute places records its file with `..`, for example
# `crates/kernel-core/src/path_universe/../higher_field/certificate_tests.rs`,
# and `git show <rev>:<path>` does not resolve `..` (#6844). `tree_path`
# drops each `.` and empty part, and each `..` takes the part before it. A
# relative path whose `..` leaves the tree is refused. An absolute path is a
# source that a build script writes under the target directory, such as
# `out/stencils.rs`: git holds no text of it, so its path in the tree is
# null, and its build script stands in the tree for it.
def tree_path:
  . as $path
  | if startswith("/") then null
    else
      reduce (split("/")[]) as $part ([];
        if $part == ".." then
          if length == 0 then error("the path \($path) leaves the tree") else .[:-1] end
        elif $part == "." or $part == "" then .
        else . + [$part] end)
      | join("/")
    end;
