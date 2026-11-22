# External certificates and claims — forensic release (2026-11-22)

**Status:** Evidence released for audit; NOT an external independent certification or proof of RH. **OPEN_MATH=true; CLOSED_MATH=false.** Not submitted for formal peer review.

## Claim classification

| ID | Claim | Source | Evidence status | Unconditional endpoint? |
|---|---|---|---|---|
| RH-C01 | A concrete coefficient approximant gives an upper bound on D_N | `CoefficientRealization.lean` / `DN_le_coefficient_error_sq` | Historical MVEI kernel record; inspect exact type | No |
| RH-C02 | Finite-span approximation is equivalent to D_N limit zero | `ZeroLimitFrontier.lean` / `finiteSpanApproximatesChi_iff_DNLimit_eq_zero` | Historical MVEI record | No |
| RH-C03 | Logarithmic majorant tends to zero | `LogMajorantFinalProducer.lean` / `logMajorant_tendsto_zero` | Historical MVEI record | No |
| RH-C04 | Given a log majorant for D_N, obtain zero limit | `FINAL_ROOT_of_logMajorant` | Historical MVEI record; premise required | No |
| RH-C05 | Weighted critical-line error rate implies terminal | `ForensicMaterialAssembly.lean` / `terminal_of_weightedCriticalLineRate` | Source-inspected conditional implication | No |
| RH-C06 | Explicit Gram rate implies terminal | `terminal_of_explicitGramRateTarget` | Source-inspected conditional implication | No |
| RH-C07 | Concrete Gram log rate implies terminal | `terminal_of_concreteGramLogRate` | Source-inspected conditional implication | No |
| RH-C08 | Unified evidence implies represented endpoints | `UnifiedOpenMathClosure.lean` / `unified_multistate_evidence_closes_all` | Source-inspected conditional implication; requires `UnifiedOpenMathWitness` | No |
| RH-C09 | Construct a uniform rate for the actual concrete D_N | `ExplicitGramRateTarget` or `ConcreteUniformLogDNBound` | **OPEN: independent witness not identified** | No |
| RH-C10 | Public rational-multiplier route | `ConcreteClosure.lean` | **OPEN: htransfer and hwitness** | No |
| GLOBAL-C01 | Seven material producers for the universal gate | `M-Core/atk-kernel/audits/status_calculado.json` | 2026-10-22 snapshot reports 0/7; stale until new CI | No |

**Rule:** a compiled conditional theorem is a valid theorem, not an unconditional inhabitant of its hypothesis. `#print axioms` can show only standard axioms while a theorem still has substantive arguments. `Classical.choose` requires an existing proof of existence; it does not establish existence.

## Original sources

- [Verified subset and limitations](../../r01-verified/README.md)
- [Public R01 closure](../../r01-rational-spectral-exclusion/ConcreteClosure.lean)
- [Historical forensic assembly](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/R0/ForensicMaterialAssembly.lean)
- [Historical material recovery](../../branches/m-core-riemann/atk_rh-material-recovery-20261007/lean/MCore/RH/R0/MaterialRecovery.lean)
- [Unified master witness (public mirror)](https://github.com/ShantiDraconis/atk-math-core-public/blob/main/branches/M-Core/attack_universal-multistate-signature/lean/MCore/FinalFail/UnifiedOpenMathClosure.lean)
- [M-Core historical status](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/audits/status_calculado.json)

## Publication boundary

Historical certificates and commit metadata are **project-generated evidence**, not endorsements by external auditors. No external reviewer, institution, or mathematical authority is claimed. Independent reproduction remains pending.
