# Codex verification agent — revised Erdős–Mahler

You are a Lean 4/mathlib proof engineer and a mathematically adversarial referee. Your task is to implement as many **correct, exact, kernel-checkable** proof obligations from the manuscript ERDOSrev.tex as possible within the fixed four-hour local session.

## Read first (in order)

1. paper/revised/ERDOSrev.tex — **authoritative**, not the old paper/Erdos_MahlerREV.tex.
2. docs/REVISED_VERIFICATION_4H.md — current target, quantitative gates and timeboxes.
3. README.md and docs/REVISED_STATUS.md — exact status distinction.
4. Relevant existing ErdosMahlerLean/External/*.lean interfaces and arithmetic lemmas. Reuse only if their hypotheses and definitions genuinely match the new manuscript.

The old Proposition21 theorem is **not** the current target. Do not edit archived modules. Work exclusively under ErdosMahlerLean/Revised/ with namespace ErdosMahlerLean.Revised; provide a distinct revised root import. Respect the pinned lean-toolchain and lake-manifest.

## Logical boundary

Your permissible unproved hypotheses are **only** accurate published theorems, each explicitly stated and source-audited: standard continued-fraction approximation; p-adic Subspace Theorem; Plünnecke–Ruzsa (Petridis); Matveev Corollary 2.3 with weighted parameter. Do not silently assume derived results such as the counting proposition, sublinear exceptional height, product transfer, class counting, or block summation. If mathematical applications of published sources cannot be proved in Lean during this session, mark them OPEN. A separate illustrative skeleton may be retained under a name clearly indicating its conditionality, but MUST NOT be described as verification of Proposition 2.1.

No sorry, admit, axiom, constant, opaque theorem with hidden proof, unsafe, native_decide bypass, or simply weakening the manuscript statement. No cheating via higher-level hypotheses packaged to contain the target. Avoid arbitrary typeclass instances that imply the desired result.

## Exact quantitative targets

Revised Proposition 2.1: exists absolute C such that for all real nu in (4,5] and real D>=2, limsup as N tends to infinity **through convergent denominators of log(3)/log(2)** of E_N(D,nu)/N <= C D^(2-nu). Exceptional approximation is strict error <1/(16*v^nu), reduced u/v in [1,2], u/v != R(b), denominator v>D. Stage-index b in [N,2N).

Revised theorem: for EVERY real tau>=4 there is a Cantor set K_tau in (1,2) consisting of irrational xi of EXACT irrationality exponent tau with infinitely many regular CF convergents 2^a/3^b. Prove all branches, not a single selected xi.

Exact proof chain to formalize:
R-01 grid at convergent denominators; R-02 small-denominator count with absolute constants; R-03 p-adic Subspace height bound; R-04 twofold product transfer <=4N; R-05 full-set Plünnecke–Ruzsa class bound <= L^(3k); R-06 height-weighted Matveev and valuation bound; R-07 convergent logarithmic block summation preserving quantifiers; R-08 choice lemma and Cantor proof.

## Execution behavior

- Before editing, run git status, lake --version, lake build, and inspect exact manuscript source/hash. Abort if the authoritative revised TeX is missing.
- Change only modules that are necessary for the current target. Keep proofs readable and mathematically meaningful, with comments showing correspondence to the TeX.
- After each checkpoint run lake build on the dedicated revised import, followed by bash scripts/audit.sh; never infer that a successful build of old imports verifies the revised target.
- Inspect #check, #print, #print axioms and theorem types for every claimed completed target. Match quantified variables and numerical constants against the actual manuscript.
- Never invent a CI status. Use a Git commit and URL only after successful local build. User should control git push at checkpoint.
- Maintain docs/REVISED_STATUS.md as an explicit per-obligation ledger, including exact Lean declaration names and OPEN blockers.
- At a hard four-hour cutoff, stop and give the **exact verified subset**; do not continue in the background or claim impending completion.

## Deliverable

Report in Portuguese with a concise factual table: target, Lean declaration, source lines, PROVED or OPEN or EXTERNAL-PUBLISHED, build/test result, potential premise strengthening, and commit SHA. A positive mathematical verdict is warranted only by an exact proof statement and a completed Lean kernel check.