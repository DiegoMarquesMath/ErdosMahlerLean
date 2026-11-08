# Revised theorem: four-hour Lean verification protocol

**Status: NOT YET VERIFIED.** Branch: formalization/revised-twofold-nu4-2026-11-08. Authoritative source: the author's local ERDOSrev.tex and ERDOSrev.pdf, to be copied to paper/revised/ and hashed before any Lean proof is declared checked. The archived conditional proof at tag prop21-conditional-2026-11-06 must remain intact.

This is a hard four-hour work budget, **not a promise** that both theorems can be completely formalized in that window. At the deadline, record the strongest kernel-checked statements and every unfinished obligation as OPEN.

## Scope

Formalize the manuscript-specific *deductions* from published inputs. External statements permitted as theorem parameters, subject to an exact source and hypotheses audit: continued-fraction convergent approximation; the p-adic Subspace Theorem; Petridis's Plünnecke–Ruzsa bound; and Matveev 2000 **Corollary 2.3 with weighted coefficient parameter**. Existing mathlib statements may be used. Do not take any manuscript-specific counting or construction claim as a hypothesis.

**Forbidden external shortcuts:** the revised grid count, Lemma 3.1, W_N=o(N), the twofold product transfer, the power-class counting lemma, Lemma 3.3, Proposition 2.1, the two-successor lemma, or the Cantor theorem. These are proof obligations.

## Session checkpoints

| Elapsed | Objective | Mandatory checkpoint |
| --- | --- | --- |
| 0:00–0:20 | Clone/checkout; copy revised TeX/PDF and record SHA-256; baseline build | Source snapshot committed, original history preserved |
| 0:20–1:05 | Exact definitions, exceptions, limsup and quantifier order | Definition module compiles |
| 1:05–1:55 | Rotation grid; small denominators; twofold products; finite power classes | Honest compile-and-commit of completed pieces |
| 1:55–3:00 | Subspace height deduction; weighted Matveev; valuation, block estimate and log-series tail | Published inputs separated from derived theorems; OPEN items explicit |
| 3:00–3:45 | Proposition 2.1 assembly; two-successor/Cantor theorem | Entire statements checked, or documented as incomplete |
| 3:45–4:00 | Hygiene, theorem types, axioms, CI, status and push | Verifiable final SHA and no unsupported PASS claim |

## Mathematical obligation ledger

**R-00 Source.** Check revised TeX identifiers and constants; record hash. Never overwrite paper/Erdos_MahlerREV.*.

**R-01 Rotation.** Define alpha=log(3)/log(2), a(b)=ceil(b alpha), R(b)=2^a(b)/3^b, and the convergent denominator set D. Prove the uniform O(1) grid count for indices [N,2N) when N is a convergent denominator, uniformly in the arc. It is *derived*, not a new external input.

**R-02 Small denominator bound.** Exception means reduced rational s=u/v in [1,2], s != R(b), error < 1/(16 v^nu), 4<nu<=5, v>D. Derive O(N D^(2-nu)+N^(2/3)) with absolute implied constant.

**R-03 Subspace.** Build U=Pv/d, W=Su/d, primitive pair; p-adic product at 2,3; apply the exact published theorem to prove Lemma 3.1 and W_N=o(N). No opaque height-contraction hypothesis.

**R-04 Twofold products.** Fixed b+c gives at most two possible a(b)+a(c). Prove cardinality <=4N of central products and transfer to XX using denominators H^2 and separation H^(-4), with 1<theta<nu/4. Control repeated approximants by the grid count.

**R-05 Classes.** Derive |A-A-A| <= L^3 |A| using the published full-set Plünnecke–Ruzsa statement, then use Ruzsa's triangle inequality and torsion-freeness to prove <=L^(3k) classes modulo q=2^k powers. The class-count result itself is NOT an assumption.

**R-06 Matveev.** Set x=log(N/w), x^2<=q<2x^2. From s_c/s_b=g^q deduce q h(g)<=3w. Check conditions of Matveev Corollary 2.3, notably weighted B and the nonzero form. Conclude Lambda=0, index spacing O(w) using the 3-adic valuation, and absolute block estimate exp[-c x/log(2+x)].

**R-07 Limsup.** Fix nu, then theta, then N along convergent denominators. Show the nonempty logarithmic ranges lie in the tail of a convergent series; the large-denominator contribution is o_nu(N). The coefficient on D^(2-nu) remains absolute. Prove the exact revised Proposition 2.1, not the archived triple-product statement.

**R-08 Cantor.** For each real tau>=4 use D_t=Q^(tau-1)/6 and nu_t=4+1/t. Prove two successors, strict nesting and disjointness, all binary branches, prescribed convergents by Legendre, and both inequalities mu(xi)>=tau, mu(xi)<=tau, covering every competing denominator between successive Q_j.

## Gates before any VERIFIED claim

1. Every claimed revised theorem is imported by a dedicated revised root module and is actually built; an old Lake build is not enough.
2. No sorry, admit, new axiom, constant, unsafe, or opaque theorem shortcut. Run bash scripts/audit.sh, and review theorem dependencies manually.
3. Print exact theorem types and #print axioms. Explicit external mathematical *arguments* do not appear in #print axioms: inspect both.
4. Record SHA-256 of manuscript, Lean/mathlib versions, commit SHA, CI run and a ledger with statuses PROVED / EXTERNAL-PUBLISHED / OPEN / MISMATCH.
5. If any obligation is OPEN, do not rename a target theorem or weaken its statement to manufacture success. Keep the PR draft.

## Commit sequence

- chore: freeze revised manuscript and checksums
- feat(revised): define exact exceptional-counting target
- feat(revised): prove elementary counts and twofold classes
- feat(revised): apply external height and logarithm bounds
- feat(revised): assemble revised Proposition 2.1 and main theorem
- docs: audit exact kernel statement and unfinished obligations

Only use messages corresponding to actual completed work. Prefer small reviewable commits.