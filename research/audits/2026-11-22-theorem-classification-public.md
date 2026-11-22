# R01 — Public theorem classification and promotion criteria (2026-11-22)

**Public disclosure scope:** only exact mathematical types and classifications already present in publicly discussed audits; no private source code or proof terms copied. **OPEN_MATH=true / CLOSED_MATH=false.**

## What a theorem can prove without proving RH

| Candidate (M-Core source) | What its type establishes | What it does **not** establish |
|---|---|---|
| `ATK.FinalRoot.verde_fiel_iff` | `VerdeFiel ↔ IsEmpty ZeroFora ∧ ExclusaoResidualDescida`, as an equivalence with no theorem parameters | A witness for either side; RH or Beal |
| `ATK.FinalRoot.rotas_RH` | Sufficient implications `(⨅ N, DN N)=0 → RH`, `UniformLogBound → RH`, a contraction implication, and `RH ↔ IsEmpty ZeroFora` | Any of the antecedents or RH |
| `ATK.FinalRoot.raiz_de_produtores` | `PontesRestantes M → Produtores M → Raiz M` | A term of `PontesRestantes M`, `Produtores M`, or `Raiz M` by itself |
| `ATK.ClosedMathReal.closedMath_real` | `Lacunas H Y → ClosedMathRealAlvo H Y` | The independent construction of `Lacunas H Y` |
| `ATK.ClosedMathReal.lacuna_rh_iff` | `RH.produtor ↔ RiemannHypothesis` | `RH.produtor` or `RiemannHypothesis` |
| `ATK.ClosedMathReal.lacuna_pnp_iff` | A P≠NP producer is equivalent to the canonical project-level target | The producer or P≠NP |
| `ATK.CEZ.simetria_nao_basta` | Existence of a function with zeta-like symmetries and off-line zeros | Any zero of the Riemann zeta function |
| `ATK.StatusFinal.pontesProvadas` | A typed inventory carrying explicit proof terms for specific intermediate propositions (B1, B4, SAT∈NP, bounded FLT, etc.) | Seven completed Millennium problems |

**Key type-theoretic distinction:** a declaration `theorem assemble (h : P) : Q` gives a term `P → Q`, not a closed inhabitant of `Q`. Likewise, `P ↔ Q` does not construct `P` or `Q`. A `structure S : Prop` declares a proposition; only a fully constructed `s : S` inhabits it.

## Outstanding search for terminal inhabitants

The next source audit should look for *elaborated* declarations that directly inhabit:
- `ATK.FinalRoot.PontesRestantes M`
- `ATK.FinalRoot.Produtores M`
- `ATK.FinalRoot.Raiz M`
- `ATK.ClosedMathReal.Lacunas H Y`
- canonical Mathlib `RiemannHypothesis`
- R01 transfer and uniform witness obligations (`htransfer`, `hwitness`)

Candidates must be checked on their original branches for complete types, transitive dependencies, `#print axioms`, `sorryAx`, custom axioms, circularity, and reproducible Lake builds. An occurrence of `FINAL_ROOT` in a hash/certificate file is **not** a Lean inhabitant of a theorem. The project also distinguishes parametric toy models from faithful statements of classical conjectures.

## Build evidence (not proof closure)

Private M-Core PR #193 adds the nested `atk-kernel` build workflow. The first run failed in action setup because the action looked for a Lake manifest at repository root. The corrected run **44971385877** has passed action setup, environment printing, gap scanning and `lake update`; **Mathlib cache download is in progress** at the time of this entry. `lake build ATK` has **not yet completed**. Do not mark it green.

## Disclosure and integrity

The detailed source-level classification remains in **private** M-Core PR #194. This public report gives only theorem identifiers, type summaries and honest status. No private source, hidden branches, unpublished proofs, or inferred priority claims are disclosed. Do not close R01 or merge proof branches without reproducible kernel verification.

Related public tracker: [issue #5](https://github.com/ShantiDraconis/atk-riemann-public/issues/5), [R01 gap PR #8](https://github.com/ShantiDraconis/atk-riemann-public/pull/8).

## R01 gate checklist — status update, 2026-11-22

**Build:** corrected M-Core run [44971385877](https://github.com/ShantiDraconis/M-Core/actions/runs/44971385877) passed Lean action setup, pinned-environment print, explicit-gap scan, `lake update` and Mathlib cache retrieval. The `lake build ATK` step is **in progress** as of this update; this is not a successful complete build yet.

| R01 gate | Required evidence | Current status |
|---|---|---|
| Complete ATK build | `lake build ATK` exits 0 with archived logs | IN PROGRESS |
| Candidate type audit | `#check @declaration`, exact target correspondence | NOT RUN |
| Transitive axiom audit | `#print axioms` with no `sorryAx` or custom axioms | NOT RUN |
| R01 `hwitness` | Closed unconditional bound `∃ C ≥ 0, ∀ N ≥ 2, L_N * log (N+2) ≤ C` | OPEN; no inhabitant verified |
| R01 `htransfer` | Closed proof of `D_N ≤ L_N + 1/N` with the required Fin/integral discretization | OPEN; no inhabitant verified |
| Canonical zeta bridge | Exact bridge to Mathlib `riemannZeta` / `RiemannHypothesis` | OPEN |
| M1 / M2 | Full source-level and kernel-checked terminal dependencies | OPEN |
| Final root | Closed canonical theorem with no conjecture-equivalent premises | NOT VERIFIED |

**Fail-closed rule:** a green build or a `#print axioms` result alone is not a proof of RH; it must be a closed term of the correct canonical proposition. The exact source of `ConcreteClosure.lean` line 64 and any branch-only candidate must be inspected before assigning proof status. Do not assume this path or line exists on `main`.
