"""Archive a successful GitHub comparator attempt before its artifact expires."""

from argparse import ArgumentParser
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import re
import subprocess
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = (
    "inputs.sha256", "sources.log", "build.log", "statement.log", "fc-target.log",
    "replay.log", "replay-status.txt", "result.json",
)
VERDICTS = (
    b"nanoda kernel accepts the solution",
    b"Lean default kernel accepts the solution",
    b"Your solution is okay!",
)


def github(repo, path):
    return subprocess.check_output(["gh", "api", "--method", "GET", f"repos/{repo}/{path}"])


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="OWNER/REPO")
    parser.add_argument("--run", type=int, required=True)
    parser.add_argument("--attempt", type=int, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("choose a new output directory")
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_commit):
        parser.error("--expected-commit must be a full commit SHA")

    run_path = f"actions/runs/{args.run}"
    attempt_path = f"{run_path}/attempts/{args.attempt}"
    attempt_data = github(args.repo, attempt_path)
    attempt = json.loads(attempt_data)
    if (attempt["conclusion"], attempt["run_attempt"], attempt["head_sha"]) != (
        "success", args.attempt, args.expected_commit,
    ):
        raise SystemExit("Expected a successful attempt on the specified commit.")

    listing_data = github(args.repo, f"{run_path}/artifacts?per_page=100")
    listing = json.loads(listing_data)
    name = f"comparator-{args.run}-{args.attempt}"
    matches = [item for item in listing["artifacts"] if item["name"] == name]
    if listing["total_count"] > 100 or len(matches) != 1 or matches[0]["expired"]:
        raise SystemExit(f"Expected one available artifact named {name}.")
    artifact = matches[0]
    proof_zip = github(args.repo, f'actions/artifacts/{artifact["id"]}/zip')
    if artifact.get("digest") != f"sha256:{sha256(proof_zip).hexdigest()}":
        raise SystemExit("Artifact ZIP does not match GitHub's SHA-256 digest.")

    with ZipFile(BytesIO(proof_zip)) as archive:
        if archive.testzip() is not None or any(archive.namelist().count(p) != 1 for p in EVIDENCE):
            raise SystemExit("The artifact ZIP is corrupt or does not contain the expected evidence.")
        files = {p: archive.read(p) for p in EVIDENCE}

    result = json.loads(files["result.json"])
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    if (
        result.get("commit") != args.expected_commit
        or result.get("accepted") is not True
        or result.get("lake_bubblewrap") is not True
        or result.get("fresh_replay") is not True
        or any(result.get(key) != config[key]
               for key in ("challenge_module", "solution_module"))
        or result.get("targets") != config["theorem_names"]
        or result.get("kernels") != ["Lean", "nanoda"]
        or files["replay-status.txt"] != b"PASS\n"
        or not all(verdict in files["fc-target.log"] for verdict in VERDICTS)
    ):
        raise SystemExit("Expected a sandboxed comparison and fresh replay of the configured targets.")

    workflow_zip = github(args.repo, f"{attempt_path}/logs")
    with ZipFile(BytesIO(workflow_zip)) as archive:
        if archive.testzip() is not None:
            raise SystemExit("The workflow logs ZIP failed its integrity check.")

    files.update({
        "attempt.json": attempt_data,
        "artifacts.json": listing_data,
        "comparator.zip": proof_zip,
        "workflow-logs.zip": workflow_zip,
    })
    args.output.mkdir(parents=True)
    for filename, data in files.items():
        (args.output / filename).write_bytes(data)
    checksums = "".join(f"{sha256(data).hexdigest()}  {name}\n"
                       for name, data in sorted(files.items()))
    (args.output / "SHA256SUMS").write_text(checksums, encoding="utf-8")
    print(f'Archived {attempt["html_url"]} to {args.output}')


if __name__ == "__main__":
    main()
