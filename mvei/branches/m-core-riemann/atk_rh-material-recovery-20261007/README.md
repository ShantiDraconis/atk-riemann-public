# m-core-riemann — branch `atk/rh-material-recovery-20261007`

Lean sources from the branch `atk/rh-material-recovery-20261007` of the private repository `ShantiDraconis/m-core-riemann`, commit `fb8481724749868ed6badb3a8acb98df998c55a2` (2026-10-07T16:03:00+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 27 — closed 4, conditional 0, open 0, proof error 0, not reached 0, no result 23.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `4cd81528e4ae30e14fff79ae19b9a2666cc32cfdec775885d0edae89ce73793f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/atk_rh-material-recovery-20261007/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.RH.NB.NBHilbertData.BCFExplicitLogBounds.K_nonneg` | `lean/MCore/RH/NB/BCFExplicitLogBounds.lean`:47 | nao_checado |
| `MCore.RH.NB.NBHilbertData.DNLimit_eq_zero_of_bcfThreeTerm` | `lean/MCore/RH/NB/BCFThreeTermMaterializer.lean`:102 | nao_checado |
| `MCore.RH.NB.NBHilbertData.DNToZero_of_bcfThreeTerm` | `lean/MCore/RH/NB/BCFThreeTermMaterializer.lean`:90 | nao_checado |
| `MCore.RH.NB.NBHilbertData.FINAL_ROOT_of_explicit_bcf_bounds` | `lean/MCore/RH/NB/BCFExplicitLogBounds.lean`:102 | nao_checado |
| `MCore.RH.NB.NBHilbertData.bcf_three_term_materializer` | `lean/MCore/RH/NB/BCFThreeTermMaterializer.lean`:113 | nao_checado |
| `MCore.RH.NB.NBHilbertData.dn_le_combined_log_majorant` | `lean/MCore/RH/NB/BCFExplicitLogBounds.lean`:55 | nao_checado |
| `MCore.RH.R0.DISCOVER_D3_ZETA_FORM` | `open_math/lean/RHD3Decomposition.lean`:20 | nao_checado |
| `MCore.RH.R0.chi_mellinConvergent` | `lean/MCore/RH/Analytic/MellinStripConvergence.lean`:45 | nao_checado |
| `MCore.RH.R0.fract_mellinConvergent_neg` | `lean/MCore/RH/Analytic/MellinStripConvergence.lean`:7 | nao_checado |
| `MCore.RH.R0.mellin_residual_critical` | `lean/MCore/RH/Analytic/D3PlancherelReduction.lean`:37 | nao_checado |
| `MCore.RH.R0.recoveredAllNRate_iff_explicitGramRateTarget` | `lean/MCore/RH/R0/MaterialRecovery.lean`:61 | nao_checado |
| `MCore.RH.R0.recoveredAllNRate_to_terminal` | `lean/MCore/RH/R0/MaterialRecovery.lean`:65 | nao_checado |
| `MCore.RH.R0.recoveredMaterialFrontier_to_terminal` | `lean/MCore/RH/R0/MaterialRecovery.lean`:78 | nao_checado |
| `MCore.RH.R0.recovered_terminal_of_bcfExplicitLogBounds` | `lean/MCore/RH/R0/MaterialRecovery.lean`:22 | nao_checado |
| `MCore.RH.R0.recovered_terminal_of_coefficient_error_tendsto_zero` | `lean/MCore/RH/R0/MaterialRecovery.lean`:33 | nao_checado |
| `MCore.RH.R0.recovered_terminal_of_explicitGramRate` | `lean/MCore/RH/R0/MaterialRecovery.lean`:11 | nao_checado |
| `MCore.RH.R0.residualEnergy_eq_zeta_integral` | `lean/MCore/RH/Analytic/D3PlancherelReduction.lean`:50 | nao_checado |
| `MCore.RH.R0.rhoBase_mellinConvergent` | `lean/MCore/RH/Analytic/MellinStripConvergence.lean`:19 | nao_checado |
| `MCore.RH.R0.rho_mellinConvergent` | `lean/MCore/RH/Analytic/MellinStripConvergence.lean`:35 | nao_checado |
| `MCore.RH.R0.uniformLogDNBound_to_ConcreteCoefficientLogRate` | `lean/MCore/RH/R0/ExplicitCoefficientLogRate.lean`:36 | nao_checado |
| `MCore.RH.R0.uniformLogDNBound_to_ConcreteGramLogRate` | `lean/MCore/RH/R0/ConcreteGramLogRate.lean`:106 | nao_checado |
| `MCore.RH.R01.Audit.current_open_producer_iff_DNLimit_zero` | `audit/R01ConcreteAudit.lean`:17 | nao_checado |
| `MCore.RH.R01.Audit.current_open_producer_iff_DNToZero` | `audit/R01ConcreteAudit.lean`:22 | nao_checado |
| `MCore.RH.R01.DNLimit_eq_zero_of_weightedDecayBridge` | `lean/MCore/Frontier/R01Concrete.lean`:41 | fechado |
| `MCore.RH.R01.DNToZero_of_weightedDecayBridge` | `lean/MCore/Frontier/R01Concrete.lean`:49 | fechado |
| `MCore.RH.R01.concreteProducer_iff_DNLimit_eq_zero` | `lean/MCore/Frontier/R01Concrete.lean`:18 | fechado |
| `MCore.RH.R01.concreteProducer_iff_DNToZero` | `lean/MCore/Frontier/R01Concrete.lean`:25 | fechado |
