# R01 — Public mathematical gap register (2026-11-22)

**Status: OPEN_MATH=true; CLOSED_MATH=false; FINAL_FAIL.**

This is an evidence-backed **public register of outstanding obligations**, not a proof of the Riemann hypothesis (RH), a certification of any external announcement, or a disclosure of private source code. Entries must be marked CLOSED only after the actual canonical proposition is proved with reproducible kernel checks.

## A. Mathematical obligations

| ID | Obligation | Acceptance criterion | Current audit result |
|---|---|---|---|
| R01-W | **Uniform witness** (`hwitness`) | Construct a fixed `C ≥ 0` and coefficient family `v`, independent of `N`, such that for every `N ≥ 2`, `multiplierLoss N (100*N^5) 1 (v N) ≤ C / log(N+2)`, without RH or an equivalent as premise | **OPEN** — public endpoint accepts the witness as a hypothesis |
| R01-T | **Transfer** (`htransfer`) | Prove for all `N ≥ 2` the concrete `DN N ≤ multiplierLoss N (100*N^5) 1 (v N) + 1/N`; establish the exact coefficient map, cell-integral identity and bounds for the actual minimizer | **OPEN** — public endpoint accepts transfer as a hypothesis |
| R01-Z | **Canonical zeta bridge** | Prove the final theorem against the actual Mathlib `RiemannHypothesis` constant, with unchanged `riemannZeta` and strip-zero definitions | **NOT VERIFIED** end-to-end |
| R01-M1/M2 | **External/structural blockers** | Recover precise definitions, proof terms, dependencies and independent build results before declaring either closed | **UNRESOLVED** — exact current signatures not established by this audit |
| R01-CI | **Kernel/build gate** | Build all required Lake targets on pinned toolchain; inspect exact theorem types and `#print axioms`; archive logs, commit SHA, lockfile and CI run | **NOT RUN** in this audit |

**Logical warning:** `closure_of_modular_multipliers` is an implication from `htransfer` and `hwitness` to a closure result. A proof of that implication does not construct either premise. A theorem named `FINAL_ROOT` or a green CI job cannot replace them.

## B. Already-public certificate observations

- Public MVEI catalog lists **26 branches / 650 kernel-closed branch-only theorem entries**, as reported by its certificates; these numbers are not a fresh independent Lean build.
- Certificate for `atk/terminal-parameter-law-20261003`: **680 listed**, **292 closed**, **295 not reached**, **69 sorry-open**, **15 errors**, **9 unchecked**. `MCore.RH.R0.DISCOVER_terminal : RiemannTerminalCertifies` is **sorry-open**.
- Certificate for `atk/rh-rejection-zero-probe-20261006`: **166 listed**, **141 closed**, **20 conditional**, **3 sorry-open**, **2 errors**.
- `MCore.RH.NB.Final.FINAL_ROOT_of_logMajorant` requires `LogMajorantCertificate`. `MCore.RH.NB.NBHilbertData.DNLimit_eq_zero_of_bcfThreeTerm` requires `ZeroResidueVanishing`.
- The public Li-criterion certificate records `RiemannHypothesis ↔ ∀ T n, 0 ≤ (liTrunc T n).re`; an equivalence is **not** a proof of its left-hand side.

Evidence: [branch certificates](../../branches/README.md), [MVEI index](../../mvei/README.md), [master audit issue #5](https://github.com/ShantiDraconis/atk-riemann-public/issues/5), [recovery PR #6](https://github.com/ShantiDraconis/atk-riemann-public/pull/6), [fail-closed PR #7](https://github.com/ShantiDraconis/atk-riemann-public/pull/7).

## C. Reproducible review commands (run only after locating the actual Lean project and module)

```bash
# From the actual Lean/Lake project root, with its pinned toolchain and dependencies:
rg -n 'sorry|admit|sorryAx|^[[:space:]]*axiom\b|hwitness|htransfer|LogMajorantCertificate|ZeroResidueVanishing|M1|M2' .
lake build
# In an audit module importing the real candidate module:
#check @Candidate.theorem
#print axioms Candidate.theorem
-- example : RiemannHypothesis := Candidate.theorem
```

The `example` line above is **Lean syntax**, to be placed inside a `.lean` file, not typed as a shell command. Replace `Candidate.theorem` with the actual fully qualified declaration and confirm that `RiemannHypothesis` resolves to the intended Mathlib constant. Do not weaken the goal or supply missing hypotheses through `by assumption` without independently proving them.

## D. Publication and promotion policy

- Publicly record only material already public, or obtain specific permission before exposing private branches/source.
- Preserve original SHA, first-public timestamp, authorship and theorem statement separately. Commit history is not proof of novelty or first publication.
- Each CLOSED entry must link to source, full Lean type, axiom footprint, actual build log and a PR. No mass merge of diverged branches.
- External claims about a November 2026 RH/GRH announcement remain **unverified here**; they are not evidence of a gap or success in this project.

**Next gate:** first obtain the complete public definitions and proof obligations for R01-W and R01-T; then attempt independent Lean builds and a canonical terminal theorem check. Until then: **OPEN_MATH / FINAL_FAIL**.
