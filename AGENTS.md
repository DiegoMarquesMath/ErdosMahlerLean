# Repository instructions for Codex agents

This repository contains TWO versions of a mathematical manuscript. The historical Lean proof (tag prop21-conditional-2026-11-06) concerns exponent 11 and **threefold** products. The current revised manuscript concerns \(\nu>4\), **twofold** products and all real \(\tau\ge4\). Never conflate them.

On branch formalization/revised-twofold-nu4-2026-11-08, read paper/revised/ERDOSrev.tex, README.md, docs/REVISED_VERIFICATION_4H.md, docs/REVISED_CODEX_PROMPT.md and docs/REVISED_STATUS.md before editing. If the revised TeX is missing, do not implement new theorem statements by guessing.

Keep new code under ErdosMahlerLean/Revised/ and namespace ErdosMahlerLean.Revised. Preserve old modules, frozen source files and citation history. Maintain a dedicated revised root import and ensure it is a real Lake build target before claiming verification.

Permitted external theorem arguments must correspond **only** to published mathematical inputs with checked source hypotheses. Do NOT pass the revised counting proposition, sublinear height bound, twofold product transfer, class bound, summability, choice lemma or Cantor construction as opaque arguments. Explicit theorem hypotheses are not automatically proved by a passing Lean kernel check.

No sorry, admit, new axiom, constant or unsafe workaround in claimed verified code. Run Lake, scripts/audit.sh, #check and #print axioms, and inspect hidden assumptions and typeclass hypotheses. Status words are PROVED, EXTERNAL-PUBLISHED, OPEN, or MISMATCH. Report all remaining gaps honestly.

Use small informative Git commits and never force-push to main. Keep the revised PR as draft until both the mathematical statement match and CI pass. If the time budget expires, stop with a truthful partial report.