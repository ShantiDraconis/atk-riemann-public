# m-core-riemann — branch `audit/r0-4-chi-memlp`

Lean sources from the branch `audit/r0-4-chi-memlp` of the private repository `ShantiDraconis/m-core-riemann`, commit `3ed0a35b4826453d0b2aff1a366d253a172826ee` (2026-09-17T20:57:37+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 1, conditional 0, open 0, proof error 0, not reached 3, no result 0.
* History: 122 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `ea812fec89ccc902aa972107e0cb7fc68121406018c5ffb0ab2709482b71df46`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/audit_r0-4-chi-memlp/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.RH.R0.abs_rhoRepresentative_le_one` | `lean/MCore/RH/R0/RhoConcrete.lean`:28 | nao_alcancado |
| `MCore.RH.R0.rhoRepresentative_eq_reciprocal_of_tail` | `lean/MCore/RH/R0/RhoConcrete.lean`:40 | nao_alcancado |
| `MCore.RH.R0.rhoRepresentative_zero` | `lean/MCore/RH/R0/RhoConcrete.lean`:34 | nao_alcancado |
| `MCore.endpoint_of_adapter` | `lean/MCore/K8.lean`:16 | fechado |
