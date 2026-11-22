# R01 cross-branch audit — preliminary public status (2026-11-22)

This report publishes status and proof obligations only, not private M-Core source.

## Evidence
- M-Core ATK build run 44971385877 completed successfully.
- Private R01 audit PR #195 adds explicit Lean type and axiom probes.
- Audit run 44998593128 failed before checking declarations: unknown module prefix ATK.
- The workflow was corrected to build ATK before executing the probes; new execution is pending verification.

## Branch triage (not exhaustive)
- atk/closed-math-completo-20261022 and atk/pontes-rh-20261104 share matching FinalRoot.lean and ClosedMathReal.lean blobs; both describe conditional closure and FINAL_ROOT null.
- Older rh-certificates, open-math-scoped-final, and research/seven-certs-final-20260924 have not been exhaustively inventoried.

## Certification policy
- Unconditional equivalences involving RH are not unconditional proofs of RH.
- Conditional constructors do not supply the missing premise inhabitants.
- Certification requires exact elaborated type, successful kernel check, transitive axiom audit, and canonical target matching.
- OPEN_MATH remains true, CLOSED_MATH remains false, FINAL_ROOT is not certified.

No unverified claim of solving an open mathematical problem is made.