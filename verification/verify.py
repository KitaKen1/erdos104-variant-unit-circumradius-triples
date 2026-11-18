"""Build, compare, and replay the two statements on unit-circumradius triples."""

from argparse import ArgumentParser
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
VERDICTS = (
    "nanoda kernel accepts the solution",
    "Lean default kernel accepts the solution",
    "Your solution is okay!",
)


def run(output, name, command):
    with (output / name).open("w", encoding="utf-8") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    print(f"{name} (exit {result.returncode})", flush=True)
    if result.returncode:
        print((output / name).read_text(encoding="utf-8")[-4000:], file=sys.stderr)
        result.check_returncode()
    return (output / name).read_text(encoding="utf-8")


def input_hashes():
    paths = [p for directory in ("FClikelean", "lean", "leanWithComparator", "vendor")
             for p in (ROOT / directory).rglob("*.lean")]
    paths.extend(ROOT / filename for filename in (
        "comparator.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "leanWithComparator/sync_definitions.py", "verification/Check.lean",
        "verification/verify.py", ".github/workflows/comparator.yml",
    ))
    return "".join(f"{sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT)}\n"
                   for p in sorted(paths))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--trusted-local", action="store_true",
                        help="Run this trusted checkout without Linux bubblewrap")
    parser.add_argument("--output", type=Path, default=ROOT / "verification" / "results",
                        help="new directory for logs and receipts (default: verification/results)")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True)
    commit = os.environ.get("GITHUB_SHA")
    if commit:
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if actual != commit or args.trusted_local:
            raise SystemExit("CI requires the tested commit and the comparator sandbox.")

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    hashes = input_hashes()
    (output / "inputs.sha256").write_text(hashes, encoding="utf-8")
    run(output, "sources.log", [sys.executable, "leanWithComparator/sync_definitions.py", "--check"])
    run(output, "build.log", ["lake", "--wfail", "build"])
    run(output, "statement.log", ["lake", "env", "lean", "-DwarningAsError=true", "verification/Check.lean"])

    command = ["lake", "env", "lake", "comparator"]
    if args.trusted_local:
        command.append("--inadvisably-no-sandbox")
    log = run(output, "fc-target.log", command)
    if not all(verdict in log for verdict in VERDICTS):
        raise SystemExit("Comparator did not report approval from both kernels.")

    run(output, "replay.log", ["lake", "env", "leanchecker", "--fresh", "--verbose",
                               config["solution_module"]])
    if input_hashes() != hashes:
        raise SystemExit("Verification inputs changed during the run.")
    (output / "replay-status.txt").write_text("PASS\n", encoding="utf-8")
    result = {
        "accepted": True,
        "commit": commit,
        "targets": config["theorem_names"],
        "challenge_module": config["challenge_module"],
        "solution_module": config["solution_module"],
        "kernels": ["Lean", "nanoda"],
        "lake_bubblewrap": not args.trusted_local,
        "fresh_replay": True,
        "platform": platform.system(),
        "verified_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }
    (output / "result.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
