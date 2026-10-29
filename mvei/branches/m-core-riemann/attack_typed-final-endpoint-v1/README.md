# m-core-riemann — branch `attack/typed-final-endpoint-v1`

Lean sources from the branch `attack/typed-final-endpoint-v1` of the private repository `ShantiDraconis/m-core-riemann`, commit `7f482b6e19fc73dffe319fa1e0716a9b634b5211` (2026-09-19T11:24:50+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 1, conditional 0, open 0, proof error 0, not reached 3, no result 0.
* History: 7 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `8adfaada1e3eb82da1d07fa9da40b5174b567acd4e7303a1c0ac0c9fcb5d6d65`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-riemann/attack_typed-final-endpoint-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.classical_semantic_adapter_still_open` | `lean/MCore/BackwardAudit/EndpointTypeResidue.lean`:18 | nao_alcancado |
| `MCore.BackwardAudit.cross_problem_endpoint_is_typed` | `lean/MCore/BackwardAudit/CrossProblemBridgeBoundary.lean`:54 | nao_alcancado |
| `MCore.BackwardAudit.endpoint_proposition_is_typed` | `lean/MCore/BackwardAudit/EndpointTypeResidue.lean`:15 | nao_alcancado |
| `MCore.RH.endpoint_transport` | `lean/MCore/BackwardAudit/FinalEndpoint.lean`:25 | fechado |
