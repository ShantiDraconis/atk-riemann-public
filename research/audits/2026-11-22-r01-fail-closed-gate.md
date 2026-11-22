# R01 fail-closed integration gate — 2026-11-22

**Decision:** `OPEN_MATH=true`; `CLOSED_MATH=false`; `FINAL_FAIL` until the canonical terminal proposition is proven unconditionally. This is a review protocol, not a proof.

## Required evidence for each candidate theorem

1. Record repository, branch, original SHA, author/committer dates, source path, exact declaration name and complete elaborated type.
2. Check `#check @Candidate.theorem` to reveal implicit arguments, typeclass instances and hidden certificates.
3. In the **same Lean/Mathlib environment**, test `example : RiemannHypothesis := Candidate.theorem` against the actual canonical imported definition. If the theorem takes arguments, this test fails until they are discharged. Ensure `RiemannHypothesis` resolves to the intended Mathlib constant and not a shadowing local declaration.
4. Run `#print axioms Candidate.theorem`. Reject `sorryAx`, project axioms and unreviewed opaque assumptions. A standard-axiom footprint alone does **not** remove hypotheses in the theorem type.
5. Audit transitive imports, local `RiemannHypothesis` aliases, custom zeta/zero definitions and equivalence bridges.
6. Run the **actual pinned toolchain build**, not a hash or inventory-only CI check. Archive full logs, exact command, toolchain, dependency lock, SHA, and CI URL.
7. Recheck that every endpoint hypothesis is constructed, not merely assumed. Do not treat a theorem named `FINAL_ROOT`, `closed`, or `GREEN` as an unconditional canonical proof.

## R01 obligations currently unresolved in the reviewed public ledger

- `htransfer`: for every `N ≥ 2`, the concrete `DN N` is bounded by the modular multiplier loss plus `1/N`. Requires a checked coefficient map, integral/cell decomposition and minimizer amplitude estimate.
- `hwitness`: a **single uniform** logarithmic majorant witness with explicit nonnegative constant and coefficients for every `N ≥ 2`. A theorem assuming `LogMajorantCertificate`, `BCFExplicitLogBounds` or `ZeroResidueVanishing` does not establish this.
- Exact terminal bridge to canonical Mathlib `RiemannHypothesis`, with no circular import of RH or an equivalent statement.

## Merge rules

- Separate recovery-only lemmas and documentation from canonical terminal claims.
- Import the minimum source and transitive dependencies, preserve definitions, run the relevant Lake targets, and check axioms for **every** proposed terminal theorem.
- Prefer reviewed PRs; never cherry-pick a whole divergent branch merely because CI is green.
- Do not disclose private repository source in a public PR without explicit authorization.
- No change to the OPEN/CLOSED status flags without independently reproducible evidence of an unconditional theorem.

## Current scope and limits

The public MVEI certificate ledger reports 26 branches and 650 kernel-closed branch-only entries; those are certificate claims, **not** a new independent compilation performed by this audit. The reviewed `atk/terminal-parameter-law-20261003` certificate contains 292 closed of 680 listed declarations; `DISCOVER_terminal` remains `aberto-sorry`. The reviewed `atk/rh-rejection-zero-probe-20261006` certificate has 141 closed of 166 entries, with 20 conditional, 3 `sorry`-open and 2 errors. These do not warrant promoting the global status.

Tracking: [master audit #5](https://github.com/ShantiDraconis/atk-riemann-public/issues/5), [R01 recovery PR #6](https://github.com/ShantiDraconis/atk-riemann-public/pull/6).
