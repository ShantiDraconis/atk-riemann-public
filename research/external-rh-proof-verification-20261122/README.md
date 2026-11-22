# Riemann hypothesis — independently checked external Lean proof (2026-11-22)

## Public evidence

On 20 November 2026, Levent Alpöge announced a Lean proof of the Riemann hypothesis and Dirichlet analogues, developed with Claude. The Lean/Mathlib communities published a joint verification statement affirming that the correct Mathlib statement and proof have been checked, including independent proof checkers.

- Community verification: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- Reproducibility record: https://proveriemannhypothesis.github.io/
- Independent reading map and audit ledger: https://github.com/nasqret/riemann-rev

## Exact ATK integration boundary

This is **external work**, not an ATK-authored proof. Do not claim authorship, priority, or automatic compatibility with the ATK Lean toolchain.

The externally verified theorem has type Mathlib's `RiemannHypothesis`. To use it in ATK, pin the external source and dependencies, compile an import bridge, verify the imported theorem's exact type and transitive axioms, and prove that the ATK RH target is definitionally equal to or follows from that type. Do not assume the bridge without building it.

**Important:** RH alone does not establish the stronger quantitative ATK target `explicitGramRateTarget_real : ExplicitGramRateTarget`, asserting a uniform `D_N ≤ K / log(N+2)` for all N. That rate still needs an independent argument.

## Current certification status

- External RH theorem: verified by the Lean/Mathlib community, according to its published 2026-11-21 statement.
- ATK RH import/bridge: NOT BUILT OR CHECKED here.
- ATK quantitative Gram rate: OPEN.
- Global ATK eight-obligation registry: OPEN; do not toggle `OPEN_MATH` or `CLOSED_MATH` on this evidence alone.
- This file is a research evidence record, not a new mathematical proof or independent build certificate.
