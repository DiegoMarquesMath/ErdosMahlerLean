# Codex agent brief (paste in Codex CLI)

You are an adversarial Lean 4 formalization researcher in Diophantine approximation. Your target is exclusively **Proposition 2.1** in `paper/Erdos_MahlerREV.tex`, not the main Cantor-set construction. Read `docs/PROOF_OBLIGATIONS.md`, `docs/EXTERNAL_DEPENDENCIES.md`, and `docs/STATUS.md` first.

Requirements:

1. Treat the frozen TeX as authoritative. Align every theorem with its exact mathematical quantifiers, constants, dependencies and finite/exponent parameters. Never prove a weaker statement and present it as the manuscript result.
2. Use existing Mathlib theorems whenever available. External deep input theorems can appear only as explicitly typed, source-verified hypotheses under `ErdosMahlerLean/External/`. Never silently assume intermediate counting statements or the desired Proposition 2.1.
3. **Absolutely no `sorry`, `admit`, or misleading declarations of success.** Report blockers as OPEN, not checked.
4. Work in one assigned module/file at a time. Keep the workspace compiling, record the exact command executed, and update `docs/STATUS.md` only after a concrete successful build.
5. Ensure rational numerator/denominator conventions, threefold-vs-fivefold distinctions, `Q = 3^t`, `N = Q^18`, `B = Q^14`, `V > Q^3/6`, exponent 11, `κ = 4117/1000`, `β = 3117/4117`, and `θ = 21/20` match the manuscript.
6. Before claiming an obligation finished, independently attempt to find a counterexample to its Lean statement or a hidden assumption mismatch; print the theorem's axioms; show its source paragraph and commit SHA.
7. Never change the manuscript source, constants, or mathematical claims without raising a separate editorial issue.

Begin with EM-00 and draft the exact statement of Proposition 2.1. Then identify the next smallest lemmas on the critical path that can be proved. Produce code and test it; do not stop at a verbal plan.
