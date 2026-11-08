#!/usr/bin/env bash
# bash scripts/revised_gate.sh [--final]
set -euo pipefail
cd "$(dirname "$0")/.."

echo "[REVISED] Checking frozen manuscript and checksums"
test -s paper/revised/ERDOSrev.tex || { echo "[FAIL] Missing revised TeX"; exit 1; }
test -s paper/revised/ERDOSrev.pdf || { echo "[FAIL] Missing revised PDF"; exit 1; }
test -s paper/revised/SHA256SUMS || { echo "[FAIL] Missing source checksums"; exit 1; }
shasum -a 256 -c paper/revised/SHA256SUMS

echo "[REVISED] Checking actual revised Lean compilation target"
test -s ErdosMahlerLean/Revised.lean || { echo "[FAIL] No revised root module"; exit 1; }
grep -Fq 'import ErdosMahlerLean.Revised' ErdosMahlerLean.lean || {
  echo "[FAIL] Library root does not import the revised module"; exit 1;
}

echo "[REVISED] Compiling revised root and whole project"
lake build ErdosMahlerLean.Revised
lake build
bash scripts/audit.sh
git diff --check
echo "[PASS] Revised modules compile and pass basic hygiene."
echo "[NOTE] Compilation alone does NOT verify either revised main theorem."

if [[ "${1:-}" == "--final" ]]; then
  test -s audit-evidence/RevisedInspect.lean || {
    echo "[FAIL] Missing revised theorem inspection file"; exit 1;
  }
  echo "[REVISED] Inspecting theorem types and axioms"
  lake env lean audit-evidence/RevisedInspect.lean
  echo "[NOTE] Audit all explicit mathematical premises against the frozen TeX."
fi
