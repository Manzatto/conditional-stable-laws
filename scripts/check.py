#!/usr/bin/env python3
"""Build proofs, check their axioms, and report manuscript coverage separately."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

from release_files import source_files

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--require-complete", action="store_true",
                    help="Fail if the coverage inventory has unfinished items.")
parser.add_argument("--require-axiom-free", action="store_true",
                    help="Fail if any mapped item relies on a cited axiom.")
parser.add_argument("--require-remarks", action="store_true",
                    help="Require every inventoried remark to be proved without cited axioms.")
parser.add_argument("--require-manuscript", action="store_true",
                    help="Require the external manuscript files and verify their hashes.")
parser.add_argument("--manuscript-dir", type=Path,
                    help="Read the manuscript files from this external directory.")
args = parser.parse_args()
initial_source_hashes = {path.relative_to(root).as_posix():
                         hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in source_files(root)}
env = os.environ.copy()
local_elan = root / ".tools" / "elan"
if (local_elan / "bin" / "lake").exists():
    lake = str(local_elan / "bin" / "lake")
    env["ELAN_HOME"] = str(local_elan)
else:
    lake = shutil.which("lake")
    if not lake:
        sys.exit("Lean/Lake is not installed. See README.md.")

coverage = json.loads((root / "coverage.json").read_text())
missing_sources = []
checked_sources = []
source_root = args.manuscript_dir if args.manuscript_dir is not None else root
for source in coverage["sourceFiles"]:
    path = source_root / source["path"]
    if not path.exists():
        path = source_root / Path(source["path"]).name
    if not path.exists():
        missing_sources.append(source["path"])
        continue
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != source["sha256"]:
        sys.exit(f"Manuscript changed: {path}. Update the inventory before reporting coverage.")
    checked_sources.append(source["path"])

if missing_sources and args.require_manuscript:
    sys.exit("External manuscript files required but missing: " + ", ".join(missing_sources))
if missing_sources:
    print("External manuscript files not bundled: " + ", ".join(missing_sources), flush=True)
    print("Their hashes are not checked; Lean proof and declaration audits still run.", flush=True)
if checked_sources:
    print(f"Manuscript hash check passed: {len(checked_sources)} files.", flush=True)

for command in ([lake, "build"],
                [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                [lake, "env", "lean", "-DwarningAsError=true", "AuditMainTheorems.lean"],
                [lake, "env", "lean", "-DwarningAsError=true", "AuditRemarks.lean"]):
    subprocess.run(command, cwd=root, env=env, check=True)

counts = {}
for item in coverage["results"]:
    status = item["status"]
    if status not in {"not_formalized", "partial", "proved", "defined", "excluded",
                      "cited_axiom", "proved_modulo_cited"}:
        sys.exit(f"Unknown coverage status: {status}")
    if status == "excluded" and (item["kind"] != "example" or not item.get("coverageNote")):
        sys.exit(f"Only explicitly excluded examples may be omitted: {item['id']}")
    if status not in {"not_formalized", "excluded"} and not item["leanDeclarations"]:
        sys.exit(f"Missing declaration mapping: {item['id']}")
    counts[status] = counts.get(status, 0) + 1

names = sorted({name for item in coverage["results"] for name in item["leanDeclarations"]})
for name in names:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name):
        sys.exit(f"Invalid declaration name in coverage: {name!r}")
scratch = root / ".tools"
scratch.mkdir(exist_ok=True)
declarations = scratch / "CoverageDeclarations.lean"
declarations.write_text(
    "import ConditionedStableLaws\nimport Lean.Util.CollectAxioms\n"
    "open Lean Elab Command in\nrun_cmd do\n"
    "  let standard := #[``propext, ``Classical.choice, ``Quot.sound]\n"
    "  for n in #[" + ", ".join(f"``{name}" for name in names) + "] do\n"
    "    let axs ← collectAxioms n\n"
    "    let cited := axs.filter (fun a => !standard.contains a)\n"
    "    IO.println s!\"DEP {n} {cited.toList}\"\n")
result = subprocess.run([lake, "env", "lean", "-DwarningAsError=true", str(declarations)],
                        cwd=root, env=env, capture_output=True, text=True)
(scratch / "coverage-declarations.log").write_text(result.stdout + result.stderr)
if result.returncode:
    print(result.stdout + result.stderr)
    sys.exit(result.returncode)
cited_by_decl = {}
for line in (result.stdout + result.stderr).splitlines():
    found = re.search(r"DEP (\S+) \[(.*)\]", line)
    if found:
        deps = [d.strip() for d in found.group(2).split(",") if d.strip()]
        cited_by_decl[found.group(1)] = set(deps)
missing = [name for name in names if name not in cited_by_decl]
if missing:
    sys.exit(f"Could not read axiom dependencies for: {missing}")
registered = set(coverage["citedAxioms"].keys())
for item in coverage["results"]:
    used = set().union(*(cited_by_decl[name] for name in item["leanDeclarations"]))
    if not used <= registered:
        sys.exit(f"{item['id']} uses unregistered axioms: {sorted(used - registered)}")
    declared = set(item.get("citedAxioms", []))
    if item["status"] in {"proved", "defined"} and used:
        sys.exit(f"{item['id']} is marked {item['status']} but uses cited axioms "
                 f"{sorted(used)}; mark it proved_modulo_cited.")
    if item["status"] in {"cited_axiom", "proved_modulo_cited"} and not used:
        sys.exit(f"{item['id']} is marked {item['status']} but uses no cited axiom.")
    if declared != used:
        sys.exit(f"{item['id']}: recorded citedAxioms {sorted(declared)} "
                 f"differ from actual dependencies {sorted(used)}.")
print(f"Coverage declaration check passed: {len(names)} declarations.", flush=True)
print("Manuscript coverage (independent of build success):", counts, flush=True)
remarks = [item for item in coverage["results"] if item["kind"] == "remark"]
unfinished_remarks = [item["id"] for item in remarks
                      if item["status"] != "proved" or item.get("citedAxioms")]
print(f"Remarks proved without cited axioms: {len(remarks) - len(unfinished_remarks)}/{len(remarks)}.",
      flush=True)
if args.require_remarks and unfinished_remarks:
    sys.exit("Remark verification incomplete: " + ", ".join(unfinished_remarks))
relying = sorted(item["id"] for item in coverage["results"] if item.get("citedAxioms"))
if relying:
    print(f"{len(relying)} items rely on cited axioms:", ", ".join(relying), flush=True)
incomplete = any(item["status"] in {"not_formalized", "partial"}
                 for item in coverage["results"])
if incomplete:
    print("FULL MANUSCRIPT COVERAGE IS INCOMPLETE (examples excluded).", flush=True)
    if args.require_complete:
        sys.exit(2)
if relying and args.require_axiom_free:
    print("Some results rely on cited axioms.", flush=True)
    sys.exit(3)

final_source_hashes = {path.relative_to(root).as_posix():
                       hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in source_files(root)}
if final_source_hashes != initial_source_hashes:
    sys.exit("Sources changed during verification. Run the checker again before packaging.")
receipt = {
    "verifiedAtUTC": datetime.now(timezone.utc).isoformat(),
    "requireRemarks": args.require_remarks,
    "remarksProvedWithoutCitedAxioms": len(remarks) - len(unfinished_remarks),
    "mappedDeclarations": len(names),
    "manuscriptHashesChecked": checked_sources,
    "coverageCounts": counts,
    "sourceHashes": final_source_hashes,
}
(scratch / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Verification receipt written: .tools/verification.json", flush=True)
