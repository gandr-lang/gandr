# gandr-workflow-gate

A gate of a landing asks which of its long checks must run. A check must run when its inputs changed, so the gate needs the digest of the inputs of each check, at its head and at its base. A script that answers one check at one commit starts Cargo, mise and git again for each answer, and it starts some hundreds of small programs. This crate gives each answer of a gate in one run of the binary `gate`.

## The commands

| Command | What it prints |
| ------- | -------------- |
| `gate inputs list <commit> <scope> <check>` | the inputs of the check over the scope at the commit, one per line: a path, a tab and its object |
| `gate inputs digest --commit <commit>... --check <check>... <scope>` | one line for each commit and each check: the commit, the check and the SHA-256 of that list |

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

## The work of one run

| Work | How many times |
| ---- | -------------- |
| `cargo metadata` | one time, and no time when each check reads the table |
| `mise tasks ls` | one time, and no time when `GATE_INPUTS_TASK` gives the task |
| `git cat-file --batch-check` | one time, with each `<commit>:<path>` one time |
| `git cat-file --batch` | one time, for the table of each commit |
| `git grep` | one time for each distinct tree that a grep reads |

The calls that do not wait for each other run at the same time. Eight digests of a gate take 0.17 s on the build host.

## The launcher

`.config/gate-scope/tool.bash` runs the binary for a script. A host keeps the binary under its cache directory, and the objects of the binary's source at the commit name it. So a new worktree starts no Cargo and pays no build.

## The tests

The cases of `tests/cli.rs` run the binary in a scratch repository, with a fake `cargo` and a fake `mise` and with the real `git`. Each expected list and digest is the answer of the script that this crate replaces, on the same trees.
