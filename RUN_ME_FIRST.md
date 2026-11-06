# First actions on the Mac

Your two files must already be at:

- `~/Desktop/Lean4 EM/Erdos_MahlerREV.tex`
- `~/Desktop/Lean4 EM/Erdos_MahlerREV.pdf`

1. Download this starter ZIP into `~/Downloads`.
2. In Terminal:

```bash
cd "$HOME/Desktop/Lean4 EM"
unzip -o "$HOME/Downloads/ErdosMahlerLean_Starter.zip"
bash "$HOME/Desktop/Lean4 EM/ErdosMahlerLean_Starter/bootstrap.sh"
```

The bootstrap uses `lake ... new ... math`, downloads Mathlib cache, builds the project, copies and hashes the source files, runs basic checks, and makes a first local commit. It does **not** claim the Proposition 2.1 proof is complete.

After it succeeds, create your remote repository from the project directory with the already authenticated GitHub CLI:

```bash
cd "$HOME/Desktop/Lean4 EM/ErdosMahlerLean"
gh auth status
gh repo create DiegoMarquesMath/ErdosMahlerLean --private --source=. --remote=origin --push --description "Lean 4 formal verification of Proposition 2.1 in a counterexample to the Erdős–Mahler conjecture"
```

If the repository already exists, set the existing remote instead; do not recreate it. Start private; make public only after the exact proof status and external dependency statement have been audited.

To start your local Codex agent:

```bash
cd "$HOME/Desktop/Lean4 EM/ErdosMahlerLean"
codex
```

Paste the complete contents of `docs/CODEX_AGENT_PROMPT.md` in the Codex session. Agents must edit disjoint modules and never claim success merely from a passing scaffold build.
