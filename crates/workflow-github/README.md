# gandr-workflow-github

The workflow crates' one boundary to GitHub's `gh`: the runner every invocation goes through, and the error family its failures share. It sits in the workflow category, outside the language, and guards neither integrity nor validity.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-github` is a library the workflow binaries share. `run` starts a `gh` invocation, feeds it a body on standard input when asked, and returns what it wrote to standard output; `GitHubError` is the refusal when it does not start, exits unsuccessfully, or answers what its caller does not read.

**Why.** The lane budget, the hotpath guard, the coverage guard and the test timings each read GitHub through `gh`, and each meets the same three failures. One runner gives every binary the same refusal for the same failure: the invocation spelled as a shell types it, the exit status beside what `gh` wrote to standard error, the body written whole before the answer is read.

**How.** What each crate asks GitHub stays with that crate: the routes, the `--jq` queries and the issue-filing policy differ crate to crate, so each builds its own `Command` and hands it to `run`. A caller that cannot read an answer refuses it with `GitHubError::unread`, which names the invocation as the runner does. Each crate's own error carries `GitHubError` in one variant, converted with `From`.

## Provided features

- `run` starts a command with standard output and standard error piped, feeds it a `Feed::Body` when given one, and returns its standard output read as UTF-8 with any invalid sequence replaced.
- `GitHubError::Unstarted` names an invocation that did not start, could not be fed, or could not be waited for; `GitHubError::Exited` one that exited unsuccessfully, with its status and its standard error; `GitHubError::Unread` one whose answer the caller could not parse.
- `Invocation` spells a command as a shell does: the program and its arguments, separated by spaces.

## Expected features

`gh` on the path, authenticated for the repository each caller names; the library itself starts whatever program the caller's `Command` names.

## Examples

```sh
cargo nextest run -p gandr-workflow-github
```

## Dependencies

None beyond the standard library.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
