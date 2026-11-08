# Exact Mac commands for the revised Lean 4 work session

This repository is **public**. Pushing paper/revised/ERDOSrev.tex and ERDOSrev.pdf publishes those files. The GitHub branch and draft PR already exist.

## 0. Freeze the revised source and verify the old build (first 20 minutes)

```bash
cd "$HOME/Desktop/Auditoria ERDOSMAHLER" || exit 1
test -s ERDOSrev.tex && test -s ERDOSrev.pdf || exit 1
codex --version
lake --version
gh auth status || echo "Use gh auth login if push fails"

if [ ! -d ErdosMahlerLean/.git ]; then
  git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
fi
cd ErdosMahlerLean || exit 1
test -z "$(git status --porcelain)" || { echo "Review local changes before continuing"; exit 1; }
git fetch origin
if git show-ref --verify --quiet refs/heads/formalization/revised-twofold-nu4-2026-11-08; then
  git switch formalization/revised-twofold-nu4-2026-11-08
else
  git switch --track -c formalization/revised-twofold-nu4-2026-11-08 origin/formalization/revised-twofold-nu4-2026-11-08
fi
git pull --ff-only origin formalization/revised-twofold-nu4-2026-11-08

mkdir -p paper/revised .codex-logs
cp ../ERDOSrev.tex paper/revised/ERDOSrev.tex
cp ../ERDOSrev.pdf paper/revised/ERDOSrev.pdf
shasum -a 256 paper/revised/ERDOSrev.tex paper/revised/ERDOSrev.pdf > paper/revised/SHA256SUMS
shasum -a 256 -c paper/revised/SHA256SUMS
lake exe cache get
lake build
bash scripts/audit.sh
git add paper/revised/ERDOSrev.tex paper/revised/ERDOSrev.pdf paper/revised/SHA256SUMS
git diff --cached --check
git commit -m "chore: freeze revised manuscript with checksums"
git push -u origin formalization/revised-twofold-nu4-2026-11-08
```

## 1–4. Four focused Codex sessions (use the same Terminal)

Paste this function once:

```bash
run_revised_phase () {
  phase="$1"
  case "$phase" in
    01) prompt="01_DEFINITIONS.md" ;;
    02) prompt="02_FINITE.md" ;;
    03) prompt="03_DEEP.md" ;;
    04) prompt="04_ASSEMBLY.md" ;;
    *) echo "Choose 01, 02, 03 or 04"; return 2 ;;
  esac
  codex exec --sandbox workspace-write \
    -C "$PWD" \
    -c 'model_reasoning_effort="high"' \
    -o ".codex-logs/phase-$phase-last.md" \
    - < "docs/revised_phases/$prompt" \
    2>&1 | tee ".codex-logs/phase-$phase.log"
}
```

### Phase 01: definitions and rotation (0:20–1:05 elapsed)

```bash
run_revised_phase 01
bash scripts/revised_gate.sh
git add ErdosMahlerLean ErdosMahlerLean.lean docs/REVISED_STATUS.md
git diff --cached --check
git diff --cached --stat
git commit -m "feat(revised): add exact definitions and verified rotation facts"
git push
```

### Phase 02: small denominators and twofold combinatorics (1:05–1:55)

```bash
run_revised_phase 02
bash scripts/revised_gate.sh
git add ErdosMahlerLean ErdosMahlerLean.lean docs/REVISED_STATUS.md
git diff --cached --check
git diff --cached --stat
git commit -m "feat(revised): prove small-denominator and product-class bounds"
git push
```

### Phase 03: Subspace, weighted Matveev and blocks (1:55–3:00)

```bash
run_revised_phase 03
bash scripts/revised_gate.sh
git add ErdosMahlerLean ErdosMahlerLean.lean docs/REVISED_STATUS.md
git diff --cached --check
git diff --cached --stat
git commit -m "feat(revised): formalize proved height and block estimates"
git push
```

### Phase 04: exact Proposition 2.1 and the Cantor theorem (3:00–3:45)

```bash
run_revised_phase 04
bash scripts/revised_gate.sh
git add ErdosMahlerLean ErdosMahlerLean.lean docs/REVISED_STATUS.md
git diff --cached --check
git diff --cached --stat
git commit -m "feat(revised): assemble proved counting and Cantor deductions"
git push
```

**IMPORTANT:** each example commit message is conditional on that work actually being proved. If any phase is incomplete, change its commit message to accurately describe partial progress and mark remaining obligations OPEN in docs/REVISED_STATUS.md. Do not commit source with sorry/admit/new axiom as a purported verified proof. Skip git commit when there are no staged changes.

## 5. Final audit (3:45–4:00)

```bash
shasum -a 256 -c paper/revised/SHA256SUMS
lake build ErdosMahlerLean.Revised
lake build
bash scripts/audit.sh
git diff --check
git status --short
git log -6 --oneline
```

If the revised main theorems were actually proved, create audit-evidence/RevisedInspect.lean containing #check, #print and #print axioms for those declarations, then run:

```bash
bash scripts/revised_gate.sh --final
git add audit-evidence/RevisedInspect.lean docs/REVISED_STATUS.md
git diff --cached --check
git commit -m "docs: record revised theorem types and kernel inspection"
git push
```

Otherwise leave the PR in **draft** and record the exact proved subset and open obligations. This is a strict four-hour budget, not a guarantee of full formalization. Raw Codex session logs remain in ignored .codex-logs/ and are not pushed.

[Tracking issue #3](https://github.com/DiegoMarquesMath/ErdosMahlerLean/issues/3) · [Draft PR #4](https://github.com/DiegoMarquesMath/ErdosMahlerLean/pull/4).
