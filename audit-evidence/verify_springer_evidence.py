"""Check retained continuation evidence; optionally verify the local-only source.

Run from any directory:
  python3 audit-evidence/verify_springer_evidence.py
  python3 audit-evidence/verify_springer_evidence.py --local-source

This validates recorded outputs and inventories, not fresh compilation. The exact
commands to regenerate the logs are recorded in springer-checks.json.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
evidence = root / "audit-evidence"
parser = argparse.ArgumentParser()
parser.add_argument("--local-source", action="store_true")
args = parser.parse_args()
def read(name): return (evidence / name).read_text()
def obj(name): return json.loads(read(name))

allowed = {"propext", "Classical.choice", "Quot.sound"}
pattern = r"'([^']+)' depends on axioms: \[([^\]]*)\]"
rows = re.findall(pattern, read("consolidated-axioms-springer.log"))
assert len(rows) == 358 and len(dict(rows)) == 358
expected = obj("consolidated-axioms.json")
assert set(dict(rows)) == set(expected["declarations"])
for name, axioms in rows:
    assert {a.strip() for a in axioms.split(",") if a.strip()} <= allowed, name
assert len(obj("source-proof-inventory.json")["proofs"]) == 358
for log in ("consolidated-axioms-springer.log", "inspect-springer.log",
            "kernel-recheck-springer.log", "springer-specialization.log"):
    assert not re.search(r"(^|\n).*error:", read(log)), log
assert "Build completed successfully (5884 jobs)." in read("lake-build-springer.log")
assert "Static proof-hygiene scan passed" in read("hygiene-springer.log")
assert read("paper-hashes-springer.log").count(": OK") == 2
assert "All 86 tracked files match" in read("source-check-springer.log")
assert read("source-check-springer.log").count("clean pinned checkout") == 9
kernel = obj("kernel-recheck.json")
assert kernel["checked_bodies"] == 42703
assert kernel["checked_project_bodies"] == 579
assert kernel["total_transitive_constants"] == 44807
assert set(kernel["axioms"]) == allowed
assert len(kernel["bodyless_declarations"]) == 2104
deps = obj("dependencies.json")
assert set(deps["axioms"]) == allowed
assert deps["total_transitive_constants"] == 44807
assert len(deps["project_declarations"]) == 581
assert "ErdosMahlerLean.proposition21" in read("inspect-springer.log")
assert "IndependentAudit.threefold_coefficient" in read("springer-specialization.log")
frozen = obj("source-hashes.json")
assert len(frozen["files"]) == 86 and all(f["matches_frozen"] for f in frozen["files"])
for f in frozen["files"]:
    assert hashlib.sha256((root / f["path"]).read_bytes()).hexdigest() == f["sha256"], f["path"]
tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).decode().split("\0")
assert not any(p.startswith(".local-sources/") for p in tracked)
if args.local_source:
    source = obj("springer-source-inspection.json")
    path = root / source["local_pdf"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == source["pdf_sha256"]
    result = subprocess.run(["git", "check-ignore", "-v", str(path)], cwd=root,
                            check=True, capture_output=True, text=True)
    assert ".local-sources/" in result.stdout
    for artifact in source["local_only_artifacts"]:
        assert hashlib.sha256((root / artifact["path"]).read_bytes()).hexdigest() == artifact["sha256"]
    print("PASS: local PDF, extracted text and page-image hashes; local source ignored and untracked.")
print("PASS: retained build/probe outputs, 358 axiom results, kernel counts and all 86 frozen file hashes.")
print("External hypotheses remain unproved; this evidence verifier does not compile Lean or prove source geometry.")
