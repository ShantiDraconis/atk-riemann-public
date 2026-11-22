# External AI formal-proof reconciliation (2026-11-22)

## Scope and provenance

This public record compares external OpenAI and Anthropic 2026 announcements with the exact eight terminal types in the private ATK/M-Core `StatusFinal.lean`. **External authors retain attribution.** Public announcements, formal Lean artifacts, and independent kernel replay are different evidence grades. No external code is copied into this repository.

## External results and ATK import gates

| ATK target | External source | Status of external claim | ATK promotion gate |
|---|---|---|---|
| O1 RH | Levent Alpöge + Claude RH claim announced Nov 21, 2026; AP reporting | Claimed Lean formalization; independent mathematical review pending | Retrieve original Lean artifact with license, pin commit, replay build, verify exact `RiemannHypothesis`, prove `RH.produtor` via `lacuna_rh_iff` |
| O3 NS | OpenAI, *On the Navier–Stokes Millennium Prize Problem*, Sep 8, 2026 | Claimed solution and Lean formalization; scope and accepted validity must be checked | Verify exact external PDE, smoothness/force hypotheses and `NS.produtorO3` model fidelity, replay Lean |
| B2 FLT | Anthropic, *Formalizing Fermat's Last Theorem*, Sep 4, 2026 | Anthropic reports complete computer-checked Lean formalization | Compare theorem `FermatLastTheorem`, imports, axioms, license, then build an exact local proof bridge; B2 is not terminal O1–O8 |
| O4 P≠NP | OpenAI, *Working with academic communities*, Oct 2026: ETH refutation | Claimed formalization of ETH-related result | ETH false does not prove SAT ∉ P; cannot promote O4 |
| O5/O6/O7/O8 | No matching exact external proof validated in this audit | Open or scope unresolved | Require exact proof and model-fidelity bridge |

Sources:
- https://www.anthropic.com/research/formalizing-fermats-last-theorem
- https://www.anthropic.com/research/riemann-zeta (earlier partial result, NOT full RH)
- https://apnews.com/article/4fe8b69a891f160f9e7f0c85af8c55c8
- https://openai.com/index/on-the-navier-stokes-millennium-prize-problem/
- https://openai.com/index/building-scientific-understanding-with-academic-communities/

## Formal certificate protocol

A terminal certificate requires:
1. The externally published source, immutable commit SHA, explicit license and original author attribution.
2. Reproducible pinned Lean 4/Mathlib build and source checks for `sorryAx`, untrusted axioms and definition changes.
3. A *kernel-checked theorem of the exact local ATK terminal proposition*, not merely a semantically related announcement.
4. Proof that the formalized proposition faithfully matches the original mathematical statement and its quantifiers.
5. An `itemT` promotion in the actual eight-item `obrigacoes` registry, with the complete CI logs and hashes.
6. Independent review for any claimed Millennium-level conclusion.

## Current certificate classification

- `EXTERNAL_CLAIM_FOUND`: RH, NS, FLT, ETH.
- `EXTERNAL_CERTIFICATE_REPLAYED_IN_ATK`: **none in this audit**.
- `EXACT_ATK_TERMINAL_WITNESS_VERIFIED`: **none in this audit**.
- `GLOBAL_CLOSED_MATH`: **NOT CERTIFIED**.
- `OPEN_MATH`: **true**, as presently computed by `StatusFinal.lean`.

The 2026 results make the older external-knowledge inventory incomplete, but do **not** license flipping the ATK flags without a validated import and exact theorem bridge.
