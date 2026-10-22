#!/usr/bin/env python3
"""Create a source-only GitHub archive after a successful remark and A–F audit."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import zipfile

from release_files import OMITTED, source_files


root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--verification-log", type=Path, required=True,
                    help="Log from the successful scripts/check.py --require-remarks run.")
parser.add_argument("--output-dir", type=Path, default=root / "dist")
args = parser.parse_args()

receipt_path = root / ".tools" / "verification.json"
if not receipt_path.exists():
    parser.error("First run python3 scripts/check.py --require-remarks.")
receipt = json.loads(receipt_path.read_text())
if receipt.get("remarksProvedWithoutCitedAxioms") != 9 or not receipt.get("requireRemarks"):
    parser.error("The verification receipt must certify all nine remarks.")

payload = {path.relative_to(root).as_posix(): path.read_bytes()
           for path in source_files(root)}
hashes = {name: hashlib.sha256(data).hexdigest() for name, data in payload.items()}
if hashes != receipt["sourceHashes"]:
    parser.error("Sources changed after verification. Run the checker again before packaging.")

for name, data in payload.items():
    if not name.endswith(".lean"):
        continue
    for module in re.findall(r"^import\s+(ConditionedStableLaws(?:\.[A-Za-z0-9_]+)*)\s*$",
                             data.decode("utf-8"), re.MULTILINE):
        target = module.replace(".", "/") + ".lean"
        if target not in payload:
            parser.error(name + " imports a missing source module: " + target)

log = args.verification_log.read_bytes()
log_text = log.decode("utf-8")
for marker in ("Axiom audit passed:",
               "Main result Public A–F: 6 mapped declarations, no cited axiom.",
               "Coverage declaration check passed:",
               "Remarks proved without cited axioms: 9/9."):
    if marker not in log_text:
        parser.error("Verification log is missing: " + marker)

version = re.search(r'^version\s*=\s*"([^"]+)"',
                    (root / "lakefile.toml").read_text(), re.MULTILINE).group(1)
coverage = json.loads(payload["coverage.json"])
payload["verification/latest.log"] = log
payload["verification/receipt.json"] = receipt_path.read_bytes()
release = {
    "version": version,
    "toolchain": payload["lean-toolchain"].decode().strip(),
    "provedScope": {"mainTheorems": ["A", "B", "C", "D", "E", "F"],
                    "remarks": 9,
                    "formulation": "Canonical path space under Hypothesis H"},
    "standardFoundations": ["propext", "Classical.choice", "Quot.sound"],
    "sourceSnapshot": coverage["sourceFiles"],
    "sourceAmendments": coverage.get("sourceAmendments", []),
    "finiteCountRemarkWording": "Finite-n counts need not be independent.",
    "manuscriptIncluded": False,
    "remainingWholePaperWork": [
        "General compact interpolation beyond the proved midpoint instance",
        "Stationary Q-process ergodicity still uses a registered cited axiom",
        "Five examples excluded from the requested scope"],
    "omittedUnusedSourceFiles": sorted(OMITTED),
    "omissionReason": "Unused standalone Keller–Liverani axiom stub; no packaged module imports it",
    "verifyCommand": "python3 scripts/check.py --require-remarks",
}
payload["RELEASE.json"] = (json.dumps(release, indent=2) + "\n").encode()
manifest = "".join(hashlib.sha256(data).hexdigest() + "  " + name + "\n"
                   for name, data in sorted(payload.items()))
payload["SOURCE_MANIFEST.sha256"] = manifest.encode()

args.output_dir.mkdir(parents=True, exist_ok=True)
archive = args.output_dir / ("conditioned-stable-laws-lean-v" + version + ".zip")
prefix = "conditioned-stable-laws-lean/"
with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as output:
    for name, data in sorted(payload.items()):
        info = zipfile.ZipInfo(prefix + name, date_time=(1980, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.create_system = 3
        info.external_attr = 0o100644 << 16
        output.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)

with zipfile.ZipFile(archive) as zipped:
    if zipped.testzip() is not None:
        raise RuntimeError("ZIP integrity check failed")
    if set(zipped.namelist()) != {prefix + name for name in payload}:
        raise RuntimeError("ZIP source list differs from the release payload")
    for name, expected in payload.items():
        if zipped.read(prefix + name) != expected:
            raise RuntimeError("ZIP content mismatch: " + name)
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
checksum = archive.with_suffix(archive.suffix + ".sha256")
checksum.write_text(digest + "  " + archive.name + "\n")
print(str(archive))
print("Files:", len(payload), "Bytes:", archive.stat().st_size)
print("SHA-256:", digest)
