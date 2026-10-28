# m-core-riemann — branch `claude/atk-protocol-setup-wzeajl`

Lean sources from the branch `claude/atk-protocol-setup-wzeajl` of the private repository `ShantiDraconis/m-core-riemann`, commit `c21f9a9fb43489ff7f526f394392734e523cd98a` (2026-10-23T10:19:20+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: em andamento (not in the default branch).
* Theorems only on branches, in this branch: 46 — closed 46, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 11 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `294342322b4158e1fb467741c81f497dd1d5c051433c8a33a67fedba4c2faa71`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/claude_atk-protocol-setup-wzeajl/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.CrossingFamily.degenerate_at_zero` | `atk-kernel/ATK/CrossingFamily.lean`:37 | fechado |
| `ATK.CrossingFamily.factorization` | `atk-kernel/ATK/CrossingFamily.lean`:27 | fechado |
| `ATK.CrossingFamily.quarticG_nonneg` | `atk-kernel/ATK/CrossingFamily.lean`:45 | fechado |
| `ATK.Dichotomy.all_critical_iff_no_noncritical` | `atk-kernel/ATK/Dichotomy.lean`:56 | fechado |
| `ATK.Dichotomy.no_point_both_critical_and_external` | `atk-kernel/ATK/Dichotomy.lean`:42 | fechado |
| `ATK.Dichotomy.not_both` | `atk-kernel/ATK/Dichotomy.lean`:49 | fechado |
| `ATK.Dichotomy.pointwise_classification` | `atk-kernel/ATK/Dichotomy.lean`:32 | fechado |
| `ATK.Estimates.D_R_eq_neg_D` | `atk-kernel/ATK/Estimates.lean`:27 | fechado |
| `ATK.Estimates.R_involutive` | `atk-kernel/ATK/Estimates.lean`:32 | fechado |
| `ATK.Estimates.inv_sq_reciprocal` | `atk-kernel/ATK/Estimates.lean`:37 | fechado |
| `ATK.Estimates.nonzero_from_bounds` | `atk-kernel/ATK/Estimates.lean`:56 | fechado |
| `ATK.Estimates.reverse_triangle_bound` | `atk-kernel/ATK/Estimates.lean`:46 | fechado |
| `ATK.Hex.P5_eq_midpoint` | `atk-kernel/ATK/Hex.lean`:58 | fechado |
| `ATK.Hex.P6_eq_midpoint` | `atk-kernel/ATK/Hex.lean`:63 | fechado |
| `ATK.Hex.d_eq_half_diff` | `atk-kernel/ATK/Hex.lean`:48 | fechado |
| `ATK.Hex.horizontalEnergy_eq_zero_iff` | `atk-kernel/ATK/Hex.lean`:85 | fechado |
| `ATK.Hex.k6_energy` | `atk-kernel/ATK/Hex.lean`:68 | fechado |
| `ATK.Hex.t_eq_half_diff` | `atk-kernel/ATK/Hex.lean`:53 | fechado |
| `ATK.Involution.Pminus_idem` | `atk-kernel/ATK/Involution.lean`:63 | fechado |
| `ATK.Involution.Pplus_add_Pminus` | `atk-kernel/ATK/Involution.lean`:81 | fechado |
| `ATK.Involution.Pplus_idem` | `atk-kernel/ATK/Involution.lean`:54 | fechado |
| `ATK.Involution.Pplus_mul_Pminus` | `atk-kernel/ATK/Involution.lean`:72 | fechado |
| `ATK.Involution.doubled_idempotent_minus` | `atk-kernel/ATK/Involution.lean`:29 | fechado |
| `ATK.Involution.doubled_idempotent_plus` | `atk-kernel/ATK/Involution.lean`:21 | fechado |
| `ATK.Involution.product_zero` | `atk-kernel/ATK/Involution.lean`:36 | fechado |
| `ATK.Involution.sum_doubled` | `atk-kernel/ATK/Involution.lean`:43 | fechado |
| `ATK.JensenDegreeTwo.jensen_degree_two_has_real_root` | `atk-kernel/ATK/JensenDegreeTwo.lean`:46 | fechado |
| `ATK.JensenDegreeTwo.quadratic_has_real_root` | `atk-kernel/ATK/JensenDegreeTwo.lean`:19 | fechado |
| `ATK.Multiplicity.cofactor_nonzero` | `atk-kernel/ATK/Multiplicity.lean`:51 | fechado |
| `ATK.Multiplicity.factor_preserved` | `atk-kernel/ATK/Multiplicity.lean`:41 | fechado |
| `ATK.Multiplicity.removable_example` | `atk-kernel/ATK/Multiplicity.lean`:58 | fechado |
| `ATK.Multiplicity.zero_iff_of_nonzero_factor` | `atk-kernel/ATK/Multiplicity.lean`:26 | fechado |
| `ATK.PairSum.pair_sum_symmetric_three` | `atk-kernel/ATK/PairSum.lean`:36 | fechado |
| `ATK.PairSum.pair_sum_symmetric_three_doubled` | `atk-kernel/ATK/PairSum.lean`:21 | fechado |
| `ATK.RealZeta.riemannZeta_neg_four` | `atk-kernel/ATK/RealZeta.lean`:36 | fechado |
| `ATK.RealZeta.riemannZeta_neg_six` | `atk-kernel/ATK/RealZeta.lean`:42 | fechado |
| `ATK.RealZeta.riemannZeta_neg_two` | `atk-kernel/ATK/RealZeta.lean`:30 | fechado |
| `ATK.RealZeta.riemannZeta_zero_ne_riemannZeta_neg_two` | `atk-kernel/ATK/RealZeta.lean`:48 | fechado |
| `ATK.RealZeta.riemannZeta_zero_ne_zero` | `atk-kernel/ATK/RealZeta.lean`:25 | fechado |
| `ATK.SymmetryGroup.Conj_involutive` | `atk-kernel/ATK/SymmetryGroup.lean`:26 | fechado |
| `ATK.SymmetryGroup.ReflConj_involutive` | `atk-kernel/ATK/SymmetryGroup.lean`:37 | fechado |
| `ATK.SymmetryGroup.Refl_comm_Conj` | `atk-kernel/ATK/SymmetryGroup.lean`:31 | fechado |
| `ATK.SymmetryGroup.Refl_involutive` | `atk-kernel/ATK/SymmetryGroup.lean`:21 | fechado |
| `ATK.Transport.torus_identifies_half_and_three_half` | `atk-kernel/ATK/Transport.lean`:55 | fechado |
| `ATK.Transport.torus_sigma_periodicity_breaks_injectivity` | `atk-kernel/ATK/Transport.lean`:37 | fechado |
| `ATK.Transport.zero_at_point_preserved_by_transport` | `atk-kernel/ATK/Transport.lean`:27 | fechado |
