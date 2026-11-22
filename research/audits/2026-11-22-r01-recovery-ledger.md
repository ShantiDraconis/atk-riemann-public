# R01 — Public recovery and formalization ledger (2026-11-22)

**Status: OPEN_MATH / FINAL_FAIL.** This ledger is a recovery inventory, **not** a proof of the Riemann hypothesis. No theorem is promoted to unconditional status without an explicit proof term and a reproducible Lean build. The public links below do not imply permission to disclose any private repository content.

## Public conditional endpoint

Source: [ConcreteClosure.lean](../r01-rational-spectral-exclusion/ConcreteClosure.lean).

`R01.closure_of_modular_multipliers` accepts two mathematical premises:

- **htransfer**: for all `N ≥ 2`, `DN N ≤ multiplierLoss N (100*N^5) 1 (v N) + 1/N`.
- **hwitness**: there exist fixed `C ≥ 0` and a coefficient family `v` such that, for all `N ≥ 2`, `multiplierLoss N (100*N^5) 1 (v N) ≤ C / log(N+2)`.

The theorem derives `ConcreteLogRate`, `dInf = 0`, and `RiemannHypothesis` **conditional on those inputs**. Neither premise is discharged by the endpoint itself. In particular, an `#print axioms` result without `sorryAx` for a *conditional theorem* does not discharge its hypotheses.

## Recovery candidates, not yet verified against current main

| Repository / branch | Source module | Role | Outstanding checks |
|---|---|---|---|
| `m-core-riemann` / `audit/rh-log-majorant-materialized-20261001` | `lean/MCore/RH/R0/ConcreteLogMajorantLaws.lean` | Monotonicity and weakening of a **given** logarithmic certificate | Recover `ConcreteLogMajorant.lean` and its dependencies; build and axiom audit |
| `m-core-riemann` / `atk/rh-bcf-three-term-materializer-20261001` | `lean/MCore/RH/NB/BCFExplicitLogBounds.lean` | Combines **assumed** three-term estimates | Recover `BCFThreeTermMaterializer.lean`, `LogMajorantFinalProducer.lean` and dependencies; build and axiom audit |
| `M-Core` / `atk/global-closed-scope-20261007` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean` | Reuses existing partial P01 lemmas | Recover source imports, compare existing declarations, build and axiom audit |

The three modules above were observed in their respective branches and were not found at the same paths on their repositories' `main` during this review. Their complete import closure has **not** been compiled against current `main`. Do not cherry-pick an entire diverged branch blindly.

## Kernel integration work queue

1. Recover and compare the existing finite normalization, harmonic coefficient cancellation, and tail lemmas, preserving original statements and dependencies.
2. Formalize the coefficient map between the modular `λ` representation and the `Fin N` coefficients of the concrete ATK residual.
3. Formalize the integral-to-cell-sum identity on `(1/(j+1), 1/j]`, including endpoints, measurability, and tail.
4. Prove the required amplitude bound for the **actual minimizer**, or document the precise missing mathematical assumption; then derive `htransfer`.
5. Produce a genuinely unconditional uniform logarithmic witness, or keep `hwitness` open. This is an unsolved mathematical obligation, **not** an engineering task with a reliable completion estimate.
6. Check the final `riemannZeta` bridge and execute `lake build`, `#print axioms`, and a declaration-level audit.

## Separate global blockers

P vs NP: `P01ConstructionGap` (concrete verifier phase) and `G21Pointwise` (the hard separation statement) remain open in the reviewed materials. Even a valid P vs NP endpoint would not alone close the other global axes.

## Acceptance criteria for future PRs

- Start from the latest `main`; isolate minimal files and dependencies.
- Require successful Lean/Mathlib build on the repository's pinned toolchain; do not silently change versions.
- Reject `sorry`, `admit`, `sorryAx`, hidden new axioms, proof-by-status flags, and changes of target definitions.
- Publish the exact theorem statement, `#print axioms` output, test command, CI link, and commit SHA.
- Keep `OPEN_MATH=true` and `CLOSED_MATH=false` until all *unconditional* obligations are discharged and independently audited.

This is an **inventory and action plan**, not a claim that the candidates have passed compilation or have been merged.
