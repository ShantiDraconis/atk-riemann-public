# m-core-riemann — branch `atk-kernel-check`

Lean sources from the branch `atk-kernel-check` of the private repository `ShantiDraconis/m-core-riemann`, commit `a27833ada7d7438b9807ac1ad82c98eeedcab877` (2026-10-12T21:14:40+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 9 — closed 9, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 6 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `66c2f58b566ef50893cb17e7b829cd89746498c7d4b948e80d643497422c949f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/atk-kernel-check/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.RHConvergence.bdDistSq_antitone` | `atk-kernel/ATK/RHConvergence.lean`:30 | fechado |
| `ATK.RHConvergence.bdDistSq_converges` | `atk-kernel/ATK/RHConvergence.lean`:33 | fechado |
| `ATK.RHConvergence.bdDistSq_limit_nonneg` | `atk-kernel/ATK/RHConvergence.lean`:36 | fechado |
| `ATK.RHConvergence.bdDistSq_succ_le` | `atk-kernel/ATK/RHConvergence.lean`:18 | fechado |
| `ATK.RHConvergence.rh_iff_limit_zero_of_criterion` | `atk-kernel/ATK/RHConvergence.lean`:39 | fechado |
| `ATK.Riemann.abstract_bound_vacuous` | `atk-kernel/ATK/Riemann.lean`:65 | fechado |
| `ATK.Riemann.bdDistSq_nonneg` | `atk-kernel/ATK/Riemann.lean`:88 | fechado |
| `ATK.Riemann.bd_bound_tendsto` | `atk-kernel/ATK/Riemann.lean`:90 | fechado |
| `ATK.Riemann.rh_of_bd_bound` | `atk-kernel/ATK/Riemann.lean`:95 | fechado |
