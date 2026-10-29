# m-core-riemann — branch `audit/multistate-proof-refutation-v1`

Lean sources from the branch `audit/multistate-proof-refutation-v1` of the private repository `ShantiDraconis/m-core-riemann`, commit `5c9cf706ddb206aa57c45de8bab6f89ebbd779c3` (2026-09-19T10:39:28+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 7 — closed 6, conditional 0, open 0, proof error 0, not reached 1, no result 0.
* History: 14 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `b16c223c1cb5db59151751bd58d8964d86f8a680ce95d59d1825b2864899eb48`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/audit_multistate-proof-refutation-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Audit8x5.A_pending` | `lean/MCore/Audit8x5.lean`:32 | fechado |
| `MCore.Audit8x5.HC_pending` | `lean/MCore/Audit8x5.lean`:25 | fechado |
| `MCore.Audit8x5.K_pending` | `lean/MCore/Audit8x5.lean`:31 | fechado |
| `MCore.Audit8x5.Q_pending` | `lean/MCore/Audit8x5.lean`:29 | fechado |
| `MCore.Audit8x5.S_pending` | `lean/MCore/Audit8x5.lean`:30 | fechado |
| `MCore.Audit8x5.no_placebo_generic` | `lean/MCore/Audit8x5.lean`:21 | fechado |
| `MultistateAudit.Riemann.Gates.fullyAudited_elim` | `audit/20_BACKWARD_ELIMINATION/MassiveGateArchitecture.lean`:34 | nao_alcancado |
