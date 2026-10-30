"""How `lldb.bash` launches the debugger on each system it meets.

On macOS it runs Homebrew's LLVM lldb, or refuses with the install line
(#3778). There it bounds no process: macOS has no systemd, and its kernel
refuses to lower `ulimit -v`, so a bound there refuses every run (#3863).
Elsewhere it runs the lldb on PATH bounded to 8 GiB, by a systemd scope's
`MemoryMax` or by `ulimit -v` (#3823).

Run as a script, the module checks the cases of a JSON file
(`.config/debug/launch.json`): `python3 launch.py <cases>`. Each case names
the system `uname` reports, whether an lldb is installed, and what the launch
gives: its exit status, a line its error holds, or the bound the debugger
runs under, `8 GiB` or `none`. Every case stubs `uname` to answer its system,
so a case runs alike on every host (#3867); a case naming a `host` puts a
`uname` answering that host behind the stubs, as a host's own stands on
`PATH`. The debugger is a stub that prints its arguments, its `ulimit -v`, its
cgroup and that cgroup's `memory.max`. On a stub macOS, `systemd-run` is a
stub that records its call and fails.

The 8 GiB bound is the host's own: a stub reads it but cannot set it. So a
case that records the bound runs only where the host bounds a process, by a
systemd scope or by `ulimit -v`, and elsewhere it is reported skipped, never
failed: a macOS host bounds none (#3894). A case with `bounds` false puts
such a host behind the stubs, a `systemd-run` that fails and a `ulimit` that
refuses to lower `-v`, as macOS's kernel does.

A host may run the check itself inside a bounded scope. The stub's cgroup is
then the caller's, and its `memory.max` is the host's bound, not one
`lldb.bash` set: the case reads `memory.max` only from a cgroup of the
debugger's own (#4040). A case with `within` true runs the launch inside such
a scope of the host's, bounded to 8 GiB, and is skipped where the host runs
no systemd scope.
"""

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

LLDB_BASH = pathlib.Path(__file__).with_name("lldb.bash")
BOUND_KIB = 8 * 1024 * 1024
STUB_LLDB = """#!/usr/bin/env bash
printf '%s\\n' "$*"
ulimit -v
group=$(cut -d: -f3 /proc/self/cgroup 2> /dev/null || true)
printf '%s\\n' "$group"
cat "/sys/fs/cgroup$group/memory.max" 2> /dev/null || true
"""


def stub(path: pathlib.Path, text: str) -> None:
    """Write an executable script."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)


def bound(lines: list[str], caller: tuple[str, str], scoped: bool) -> str:
    """The bound the stub debugger ran under: `8 GiB`, `none`, or what it read.

    `caller` is the checker's own `ulimit -v` and cgroup. A `memory.max` read
    in the caller's cgroup is the host's bound, and the reading leaves it out.
    """
    limit, group, memory = (lines[1:] + ["", "", ""])[:3]
    readings = [limit] if group == caller[1] else [limit, memory]
    if str(BOUND_KIB) in readings or str(BOUND_KIB * 1024) in readings:
        return "8 GiB"
    if not scoped and (limit, group) == caller:
        return "none"
    return " ".join(readings)


def can_bound(environment: dict) -> bool:
    """Whether the host under `environment` bounds a process to 8 GiB, as `lldb.bash` bounds lldb."""
    probe = (
        f"systemd-run --user --scope --quiet -p MemoryMax={BOUND_KIB}K -p MemorySwapMax=0 -- true 2> /dev/null"
        f" || {{ limit=$(ulimit -v); [[ $limit != unlimited ]] && ((limit <= {BOUND_KIB})); }}"
        f" || ulimit -v {BOUND_KIB} 2> /dev/null"
    )
    return subprocess.run(["bash", "-c", probe], env=environment, capture_output=True, check=False).returncode == 0


def launched(case: dict, scratch: pathlib.Path) -> tuple[str, str] | None:
    """Why `case` launches otherwise than it records, `FAILED` or `SKIPPED`, or nothing."""
    bin_dir = scratch / "bin"
    host_dir = scratch / "host"
    keg = scratch / "keg"
    marker = scratch / "scoped"
    stub(bin_dir / "uname", f"#!/usr/bin/env bash\necho {case['system']}\n")
    if "host" in case:
        stub(host_dir / "uname", f"#!/usr/bin/env bash\necho {case['host']}\n")
    if case["system"] == "Darwin":
        stub(bin_dir / "brew", f"#!/usr/bin/env bash\necho {keg}\n")
        stub(bin_dir / "systemd-run", f"#!/usr/bin/env bash\ntouch {marker}\nexit 1\n")
        if case["lldb"]:
            stub(keg / "bin" / "lldb", STUB_LLDB)
    elif case["lldb"]:
        stub(bin_dir / "lldb", STUB_LLDB)
    environment = dict(os.environ, PATH=f"{bin_dir}:{host_dir}:{os.environ['PATH']}")
    if not case.get("bounds", True):
        stub(host_dir / "systemd-run", "#!/usr/bin/env bash\nexit 1\n")
        environment["BASH_FUNC_ulimit%%"] = (
            '() { if [[ $1 == -v && $# == 2 ]]; then echo "ulimit: cannot modify limit" >&2; return 1; fi; builtin ulimit "$@"; }'
        )
    if case["system"] != "Darwin" and case.get("bound") == "8 GiB" and not can_bound(environment):
        return "SKIPPED", "this host bounds no process, by a systemd scope or by `ulimit -v`"
    # The caller's `ulimit -v` and cgroup, read where `lldb.bash` starts.
    launch = ["bash", "-c", 'ulimit -v; cut -d: -f3 /proc/self/cgroup 2> /dev/null || echo; exec "$@"', "bash"]
    if case.get("within"):
        host_scope = [
            shutil.which("systemd-run") or "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            "-p",
            f"MemoryMax={BOUND_KIB}K",
            "--",
        ]
        if subprocess.run([*host_scope, "true"], capture_output=True, check=False).returncode != 0:
            return "SKIPPED", "this host runs no systemd scope to hold the check"
        launch = host_scope + launch
    run = subprocess.run(
        [*launch, str(LLDB_BASH), "lldb", "--batch", "--", "program"],
        capture_output=True,
        text=True,
        env=environment,
        check=False,
    )
    caller_lines, lines = run.stdout.splitlines()[:2], run.stdout.splitlines()[2:]
    if run.returncode != case["exit"]:
        return "FAILED", f"exit {run.returncode}, wanted {case['exit']}: {run.stderr.strip()}"
    if "error" in case and case["error"] not in run.stderr:
        return "FAILED", f"error {run.stderr.strip()!r}, wanted one holding {case['error']!r}"
    if "bound" in case:
        if not lines or lines[0] != "--batch -- program":
            return "FAILED", f"ran with {lines[:1]}, wanted its arguments"
        limit, group = (caller_lines + ["", ""])[:2]
        got = bound(lines, (limit, group), marker.exists())
        if got != case["bound"]:
            return "FAILED", f"bound {got}, wanted {case['bound']}"
    return None


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    failed = 0
    for case in loaded:
        with tempfile.TemporaryDirectory() as scratch:
            why = launched(case, pathlib.Path(scratch))
        if why is not None:
            verdict, reason = why
            print(f"launch case {verdict}: {case['name']}\n  {reason}", file=sys.stderr)
            failed = int(failed or verdict == "FAILED")
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
