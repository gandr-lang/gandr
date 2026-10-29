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
`PATH`. The debugger is a stub that prints its arguments, its `ulimit -v` and
its cgroup's `memory.max`. On a stub macOS, `systemd-run` is a stub that
records its call and fails.
"""

import json
import os
import pathlib
import subprocess
import sys
import tempfile

LLDB_BASH = pathlib.Path(__file__).with_name("lldb.bash")
BOUND_KIB = 8 * 1024 * 1024
STUB_LLDB = """#!/usr/bin/env bash
printf '%s\\n' "$*"
ulimit -v
cat "/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup 2> /dev/null)/memory.max" 2> /dev/null || true
"""


def stub(path: pathlib.Path, text: str) -> None:
    """Write an executable script."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)


def bound(lines: list[str], caller: str, scoped: bool) -> str:
    """The bound the stub debugger ran under: `8 GiB`, `none`, or what it read."""
    if str(BOUND_KIB) in lines or str(BOUND_KIB * 1024) in lines:
        return "8 GiB"
    if not scoped and len(lines) > 1 and lines[1] == caller:
        return "none"
    return " ".join(lines[1:])


def launched(case: dict, scratch: pathlib.Path) -> str | None:
    """Why `case` launches otherwise than it records, or nothing."""
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
    caller = subprocess.run(["bash", "-c", "ulimit -v"], capture_output=True, text=True, check=True).stdout.strip()
    run = subprocess.run(
        [str(LLDB_BASH), "lldb", "--batch", "--", "program"],
        capture_output=True,
        text=True,
        env=environment,
        check=False,
    )
    if run.returncode != case["exit"]:
        return f"exit {run.returncode}, wanted {case['exit']}: {run.stderr.strip()}"
    if "error" in case and case["error"] not in run.stderr:
        return f"error {run.stderr.strip()!r}, wanted one holding {case['error']!r}"
    if "bound" in case:
        lines = run.stdout.splitlines()
        if not lines or lines[0] != "--batch -- program":
            return f"ran with {lines[:1]}, wanted its arguments"
        got = bound(lines, caller, marker.exists())
        if got != case["bound"]:
            return f"bound {got}, wanted {case['bound']}"
    return None


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    failed = 0
    for case in loaded:
        with tempfile.TemporaryDirectory() as scratch:
            why = launched(case, pathlib.Path(scratch))
        if why is not None:
            print(f"launch case FAILED: {case['name']}\n  {why}", file=sys.stderr)
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
