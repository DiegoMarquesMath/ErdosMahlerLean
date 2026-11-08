# Start here: revised Erdős–Mahler verification

This is the **revised** manuscript, not the 2026-11-06 frozen proof.

The author has two local files:
- ~/Desktop/Auditoria ERDOSMAHLER/ERDOSrev.tex
- ~/Desktop/Auditoria ERDOSMAHLER/ERDOSrev.pdf

Use the dedicated branch formalization/revised-twofold-nu4-2026-11-08. The repository is public; copying the manuscript into paper/revised/ and pushing it publishes that snapshot.

**Open [docs/COMMANDS_ON_MAC.md](docs/COMMANDS_ON_MAC.md) and execute it step by step.** It includes clone, source freeze, local Lake baseline, four focused Codex invocations, kernel/build audits, checkpoint commits and pushes.

Read [README.md](README.md), [docs/REVISED_VERIFICATION_4H.md](docs/REVISED_VERIFICATION_4H.md) and [docs/REVISED_STATUS.md](docs/REVISED_STATUS.md) for exact targets, assumptions and verification status. Issue #3 and draft PR #4 track the work.

There is a fixed four-hour limit. If the final theorem is not kernel checked within that budget, keep the PR draft, record exactly which revised lemmas compile and list all OPEN obligations. Do not declare the revised paper proved because the historical project still builds.