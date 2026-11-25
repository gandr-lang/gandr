# gandr-workflow-gate

A gate of a landing asks which of its long checks must run. A check must run when its inputs changed, so the gate needs the digest of the inputs of each check, at its head and at its base. A script that answers one check at one commit starts Cargo, mise and git again for each answer, and it starts some hundreds of small programs. This crate gives each answer of a gate in one run of the binary `gate`.

## The commands

| Command | What it prints |
| ------- | -------------- |
| `gate inputs list <commit> <scope> <check>` | the inputs of the check over the scope at the commit, one per line: a path, a tab and its object |
| `gate inputs digest --commit <commit>... --check <check>... <scope>` | one line for each commit and each check: the commit, the check and the SHA-256 of that list |
| `gate verdict key [--tree <tree>] <check>...` | the key of the verdict of each check, one line of JSON each |
| `gate verdict read <check>...` | to standard error, which check holds on the tree of `HEAD`, by the inputs of its base or by a signed record of a pass |
| `gate verdict write <tree> <check>...` | to standard error, the one signed record of the checks that a gate ran on the tree, which the ref of each check names |
| `gate verdict publish <commit>` | to standard error, the records of the tree of the commit that one push sends |
| `gate scope --base <commit> [--head <commit>] [--touched]` | one line: `workspace`, `none`, or `packages` and the name of each crate of the scope of the change. To standard error, the causes of a whole workspace. With no head, the head is the working tree |
| `gate scoped --base <commit> [--head <commit>] [--touched] -- <command>...` | the output of the command, which runs one time with the package arguments of the scope after it: `--workspace`, or `-p <name>` for each crate. For no crate, `no package in scope`, and nothing runs. The exit code is the command's |

`--tables <directory>` names the directory of `inputs.json` and `verdicts.json`. `--times` prints each part of the run to standard error: its time, the count of its calls and its name.

## The inputs of a check

| Input | How the list names it |
| ----- | --------------------- |
| each crate of the scope and of its dependency closure | the directory and its tree at the commit |
| the manifest of each crate of the workspace | the file and its object |
| each path of `workspace` in `inputs.json` | the path and its object |
| each path of `outside` in `inputs.json` for a crate of the closure | the path and its object |
| each path of the check's `inputs` in `verdicts.json` | the path and its object |
| the definition of the check's task | `task:<check>` and the digest of its `run`, `env`, `tools` and `depends` |
| each grep of the check in `verdicts.json` | `grep:<path>:<pattern>` and the digest of the files that hold the pattern |

A check that sets `table` in `verdicts.json` reads the paths of its row of `table.json` at the commit in place of the crates. Its list holds the line `table:<check>` with the digest of the row. A path that a commit does not hold has the object `absent`.

## The scope of a change

A gate must run only what a change can break. The scope of a change is each crate whose directory holds a changed path, and each crate that depends on one of them, through a dependency of each kind, until the set does not grow. The changed paths are those of `git diff --name-only <base> [<head>]`, and with no head also each untracked path that git does not ignore. One run reads `cargo metadata` one time, and it starts Cargo and git at the same time.

With `--touched`, the scope is the touched crates alone, with no dependent: each crate whose directory holds a changed path, and the readers of the corpus for a path of `corpus/` or `library/`. A workspace input and a path that nothing holds still give the whole workspace. A change of `kernel-term` then gives one crate, where the scope with dependents gives about half of the workspace.

The table `scope.json` of the crate maps each path that no crate holds. The first row that holds a path decides it. The binary carries the table.

| Changed path | Scope |
| ------------ | ----- |
| a path in the directory of a crate | that crate and its dependents |
| a source of `corpus/` or of `library/` | the crates of `readers`, whose tests read the corpus, and their dependents |
| a workspace input: the root `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml`, `clippy.toml`, `rustfmt.toml`, a path of `.cargo/` or of `.config/` | the whole workspace |
| a page, a licence, and the configuration of a tool that builds no crate | no crate |
| a path that no crate and no row holds | the whole workspace, and the cause names the path |
| a set that holds each crate | the whole workspace |

Before a pull request, the author runs each suite on the scope of the change against `origin/main`:

```console
$ cargo run --locked --quiet --package gandr-workflow-gate --bin gate -- scoped --base origin/main -- cargo nextest run --locked --no-fail-fast
gate: scope packages gandr-workflow-gate
...
```

## The work of one run

| Work | How many times |
| ---- | -------------- |
| `cargo metadata` | one time, and no time when each check reads the table |
| `mise tasks ls` | one time, and no time when `GATE_INPUTS_TASK` gives the task to a key or a read. A write lists the tasks one time, for the checks that each task depends on |
| `git cat-file --batch-check` | one time, with each `<commit>:<path>` one time |
| `git cat-file --batch` | one time, for the table of each commit |
| `git grep` | one time for each distinct tree that a grep reads |

The calls that do not wait for each other run at the same time. Eight digests of a gate take 0.17 s on the build host.

## The launcher

`.config/gate-scope/tool.bash` runs the binary for a script. A host keeps the binary under its cache directory, and the objects of the binary's source at the commit name it. So a new worktree starts no Cargo and pays no build.

## The tests

The cases of `tests/cli.rs` run the binary in a scratch repository, with a fake `cargo` and a fake `mise` and with the real `git`. Each expected list and digest is the answer of the script that this crate replaces, on the same trees.
