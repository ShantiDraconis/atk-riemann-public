# Reproduction protocol and release boundary

The source and certificate records below are now available for **external inspection**, but no independent external verifier has yet certified the terminal conjectures.

## Reproduce from exact source revisions

1. Retrieve source repo `ShantiDraconis/m-core-riemann` at `c114452706e06317fbb46a46eda14747cfc0cf2d` and `fb8481724749868ed6badb3a8acb98df998c55a2`, or their public historical source snapshots.
2. Verify the `lean-toolchain` and `lake-manifest.json` of each snapshot. Do not silently update Mathlib.
3. Run `lake build` in each project's original working directory and preserve full stdout/stderr, exit code, platform, toolchain and source SHA.
4. Elaborate each claimed endpoint with `#check @theorem_name` and inspect the printed full theorem type. Run `#print axioms theorem_name`.
5. For every argument `h : P`, find a proof term of `P` with no unproved mathematical premise; traverse dependencies recursively.
6. For `Classical.choose`, identify the precise `∃ x, P x` theorem and verify that its proof does not depend on RH or a mathematically equivalent target.
7. Compare the actual endpoint to the canonical Mathlib or official problem formulation; audit all model bridges.
8. Publish independently reproducible logs and hashes before upgrading any claim.

## Critical path

`ExplicitCoefficientProducer → CoefficientGramEnergy / CoefficientPythagoras → ExplicitGramRateTarget → terminal_of_explicitGramRateTarget → RiemannTerminalCertifies → canonical RiemannHypothesis`.

This is a **candidate dependency path**; the missing independent inhabitant of `ExplicitGramRateTarget` and canonical endpoint bridge have not been certified. The alternative public path `hwitness + htransfer → closure_of_modular_multipliers` remains conditional.

## Status transition gate

Never set `OPEN_MATH=false` or `CLOSED_MATH=true` merely because a certificate JSON, source file, assembly theorem, or CI workflow exists. Require complete unconditional proofs for all eight registered obligations, fidelity gates, and a clean reproducible kernel build.

Historical commits of special interest: `466257b1ccf4d7817a28370a38dd44d1c8c4531f` (`Classical.choose` witness), `15e00b8b740d3a1646bee91b14eb3c01c95242fd` (critical integral rate), `c114452706e06317fbb46a46eda14747cfc0cf2d` (branch head).
