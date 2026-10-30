"""Run a command and report its wall time and peak resident set (#4191).

`python3 timed.py <report> <command>...` runs the command with this process's
standard streams, then writes two lines to `<report>`: `wall <seconds> s` and
`peak <bytes>`. It exits with the command's status, 127 when the command is
not found. The peak is the largest resident set of any child the command ran
as, read from `getrusage`, which Linux reports in KiB and macOS in bytes. It
replaces `/usr/bin/time`, which a Linux host may lack and whose flags and
output differ between the two systems.

Run as `python3 timed.py --cases <cases>`, the module checks the cases of a
JSON file (`.config/bench/timed.json`): each names a command, given to
`python3` as a script, and what its report must hold: the status, and the
peak resident set's least size in MiB.
"""

import json
import pathlib
import resource
import subprocess
import sys
import tempfile
import time

KIB_PEAK = sys.platform != "darwin"


def timed(report: pathlib.Path, command: list[str]) -> int:
    """Run `command`, write its wall time and peak resident set to `report`, and return its status."""
    start = time.monotonic()
    try:
        status = subprocess.run(command, check=False).returncode
    except FileNotFoundError:
        print(f"timed: no command {command[0]}", file=sys.stderr)
        status = 127
    wall = time.monotonic() - start
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if KIB_PEAK:
        peak *= 1024
    report.write_text(f"wall {wall:.2f} s\npeak {peak}\n", encoding="utf-8")
    return status


def checked(case: dict, scratch: pathlib.Path) -> str | None:
    """Why `case` reports otherwise than it records, or nothing."""
    report = scratch / "report"
    command = [sys.executable, "-c", case["script"]] if "script" in case else case["command"]
    run = subprocess.run([sys.executable, __file__, str(report), *command], capture_output=True, text=True, check=False)
    if run.returncode != case["status"]:
        return f"exits {run.returncode}, wanted {case['status']}: {run.stderr.strip()}"
    lines = report.read_text(encoding="utf-8").splitlines()
    if len(lines) != 2 or not lines[0].startswith("wall ") or not lines[0].endswith(" s") or not lines[1].startswith("peak "):
        return f"reports {lines}"
    peak = int(lines[1].removeprefix("peak "))
    if peak < case.get("peak_mib", 0) * 1024 * 1024:
        return f"reports a peak of {peak} bytes, below {case['peak_mib']} MiB"
    return None


def cases(path: str) -> int:
    with open(path, encoding="utf-8") as recorded:
        recorded_cases = json.load(recorded)
    failed = 0
    for case in recorded_cases:
        with tempfile.TemporaryDirectory() as scratch:
            why = checked(case, pathlib.Path(scratch))
        if why is not None:
            print(f"timed case FAILED: {case['name']}: {why}", file=sys.stderr)
            failed = 1
    return failed


def main(argv: list[str]) -> int:
    if argv[0] == "--cases":
        return cases(argv[1])
    return timed(pathlib.Path(argv[0]), argv[1:])


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
