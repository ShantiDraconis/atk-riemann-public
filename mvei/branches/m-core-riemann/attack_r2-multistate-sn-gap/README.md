# m-core-riemann — branch `attack/r2-multistate-sn-gap`

Lean sources from the branch `attack/r2-multistate-sn-gap` of the private repository `ShantiDraconis/m-core-riemann`, commit `2d7dbc12eeab720c4b0fad5c22bfc19ffd35b01b` (2026-09-26T21:45:45+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 8 — closed 1, conditional 0, open 3, proof error 0, not reached 4, no result 0.
* History: 198 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `8c4bebfe887efb4e4a2e622af2dc177e715ce39b0276a41e3f336e147804854c`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/attack_r2-multistate-sn-gap/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.RH.R2.SN_eq_sum_roses` | `lean/MCore/RH/R2/MultiStateSNGap.lean`:104 | aberto-sorry |
| `MCore.RH.R2.SN_tendsto_zero_of_weighted_modular_bilinear_decay` | `lean/MCore/RH/R2/MultiStateSNGap.lean`:125 | aberto-sorry |
| `MCore.RH.R2.kfar_vanishes_of_weighted_modular_bilinear_decay` | `research/r2/MultistateSNGap.lean`:53 | nao_alcancado |
| `MCore.RH.R2.material_producer_gaps_eq_one` | `lean/MCore/RH/R2/MultiStateSNGap.lean`:162 | fechado |
| `MCore.RH.R2.openBridge_of_weighted_modular_bilinear_decay` | `research/r2/MultistateSNGap.lean`:71 | nao_alcancado |
| `MCore.RH.R2.tensioned_sn_certificate_closes_open_math` | `research/r2/MultistateSNGap.lean`:87 | nao_alcancado |
| `MCore.RH.R2.weighted_modular_bilinear_decay_iff_SN_tendsto_zero` | `lean/MCore/RH/R2/MultiStateSNGap.lean`:140 | aberto-sorry |
| `MCore.RH.R2.weighted_modular_bilinear_decay_still_open` | `research/r2/MultistateSNGap.lean`:97 | nao_alcancado |
