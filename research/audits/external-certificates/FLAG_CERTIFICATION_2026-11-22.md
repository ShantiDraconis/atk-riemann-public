# Flag certification search — 2026-11-22

## Verdict (fail-closed)

- `OPEN_MATH=false`: **NOT CERTIFIED**
- `CLOSED_MATH=true`: **NOT CERTIFIED**
- `OPEN_MATH=true`, `CLOSED_MATH=false`: explicitly proved by reduction in `M-Core/atk-kernel/ATK/StatusFinal.lean` for its current all-`itemN` eight-obligation registry.
- `closedMath pontesProvadas = true`: **CERTIFIED BY SOURCE THEOREM**, but applies only to the separate list of six proven bridges, **not** to the eight terminal obligations.
- `closedMath_of_obligations`: **CONDITIONAL** on `Bridges M` and `OpenObligations M` in `ATK/ClosedMath.lean`. Does not inhabit either argument.
- `ClosedMathGate.lean.tpl`: template found, **not** a compiled terminal gate.
- `UnifiedOpenMathWitness`: required input to unified master assembler; no independent inhabitant found by this search.
- `ActualNS_to_SignedGainCertificate`: explicitly OPEN in the green producer-first Navier–Stokes certificate.
- `ConcreteUniformLogDNBound`: located as a required quantitative frontier in Riemann source and historical snapshots; no unconditional producer certified.

## Source-level verification

1. [StatusFinal.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/StatusFinal.lean): `obrigacoes C` consists of eight `itemN` values. `open_math_true` and `closed_math_false` have proof `rfl`. `itemT` requires a proof term of the exact `P`.
2. [ClosedMath.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/ClosedMath.lean): seven-statement theorem takes both bridges and open obligations as arguments; toy-model firewalls warn against nonfaithful models.
3. [Official observable audit](https://github.com/ShantiDraconis/axiomatic-millenium/blob/main/certificates/OFFICIAL_OBSERVABLE_NO_OPEN_MATH_20261001.json): explicitly reports zero positive and zero negative terminal endpoints closed.
4. [NS producer-first green certificate](https://github.com/ShantiDraconis/navier-stokes-critical-barrier-audit/blob/main/CERTIFICATES/NS_PRODUCER_FIRST_GREEN.md): build GREEN, but `FINAL_PROOF=FALSE` and terminal open.
5. [RH quantitative frontier](https://github.com/ShantiDraconis/atk-riemann-public/blob/main/research/r01-verified/README.md): concrete uniform estimate remains the target.

## Formal certification criteria

For each of the eight terminal obligations, produce `itemT name P proof` with a term of the *exact* official proposition, free of `sorryAx` and mathematical axioms, and confirm model fidelity. Rebuild the terminal registry without changing the mathematical meaning of its entries. Run the complete pinned Lean/Mathlib build, inspect elaborated types and `#print axioms`, archive CI logs and exact SHA. Only then certify both flags. A proof of `closedMath pontesProvadas = true` does **not** justify the terminal flags.

**Evidence scope:** GitHub indexed source and historical certificates; no clean full-repository kernel build was executed in this audit. This report does not assert exhaustive coverage of all historical branches or commits.
