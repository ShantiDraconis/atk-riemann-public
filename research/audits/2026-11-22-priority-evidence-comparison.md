# Independent priority-evidence audit — 2026-11-22

## Findings and scope

This document records **dated antecedent work** in the ShantiDraconis Git history, not an assertion of priority over the later complete Millennium solutions. A dated Git commit, a public publication event, and the mathematical novelty of an argument are different kinds of evidence.

### Riemann chronology (UTC, from existing public audit)

| Date | Exact repository/commit | Proved or documented scope |
|---|---|---|
| 2026-09-21 16:57:48 | `m-core-riemann@5c66f8dca03834f24a61a9b1219e7af9d4892dd6` | Conditional majorant implies `DNToZero` and `DNLimit=0`; majorant remains assumed |
| 2026-09-21 18:56:36 | `m-core-riemann@d6a291b4563f9021f74ab63cc983d44f079472da` | Equivalence between finite-span approximation of chi and `DNLimit=0` |
| 2026-10-13 22:08:29 | `M-Core@9e27bb5feef04d0f9a8609b548eca2134b415010` | Baez-Duarte bridge from density to Mathlib RH |
| 2026-10-27 03:56:12 | `M-Core@f1d516f71653603a4b1b5c0e53a17e47a68fdce2` | Conditional von Koch direction |
| 2026-10-27 04:10:01 | `M-Core@7ccfb308bb31880be940eaf6502285d3e40ecf6a` | von Koch equivalence |
| 2026-11-10 04:38:10 | `atk-riemann-public` MVEI snapshot `c114452706e06317fbb46a46eda14747cfc0cf2d` | Five selected Lean declarations reported kernel-checked with standard axioms; historical certificate, not unconditional RH |

Sources: [R01 timeline](https://github.com/ShantiDraconis/atk-riemann-public/blob/main/research/r01-timeline/README.md); [five verified declarations](https://github.com/ShantiDraconis/atk-riemann-public/blob/main/research/r01-verified/README.md).

### External comparison

- **Anthropic / Levent Alpöge + Claude:** public claimed RH proof dated 2026-11-20; reporting on 2026-11-21 describes Lean/Mathlib independent verification. The announced route invokes finite-field analogies and iterated theta lifts. ShantiDraconis commits listed above predate the public announcement, but **no demonstrated match** to the external proof's distinctive theta-lift construction or unconditional RH theorem has been established.
- **OpenAI Navier–Stokes:** official OpenAI announcement dated 2026-09-08; announced proof involves finite-time blowup with smooth forcing. The ShantiDraconis [NS producer-first certificate](https://github.com/ShantiDraconis/navier-stokes-critical-barrier-audit/blob/main/CERTIFICATES/NS_PRODUCER_FIRST_GREEN.md) identifies missing `ActualNS_to_SignedGainCertificate` and expressly says `FINAL_PROOF=FALSE`. The NS certificate alone does not establish earlier solution, and the presently examined record does not show a dated prior complete NS counterexample.
- The September and October Riemann work is a different research path from the published theta-lift announcement. Equivalences and conditional implications can be genuine verified mathematical work without establishing priority over the final proof.
- Classical background (Baez-Duarte, von Koch, Littlewood) must be attributed to original mathematical authors. A new Lean formalization or independently discovered reduction may be a separate contribution, but does not confer priority over the underlying classical theorem.

### Evidence grades

- `DOCUMENTED_BEFORE_EXTERNAL_ANNOUNCEMENT`: YES, for listed RH commits.
- `HISTORICAL_KERNEL_CERTIFICATE_RECORDED`: YES, for selected RH reductions (Lean v4.19.0).
- `SAME_NOVEL_TECHNIQUE_AS_EXTERNAL_PROOF`: NOT ESTABLISHED.
- `UNCONDITIONAL_RH_PROOF_BEFORE_EXTERNAL`: NOT ESTABLISHED.
- `UNCONDITIONAL_NS_PROOF_BEFORE_OPENAI`: NOT ESTABLISHED.
- `PRIZE_PRIORITY_OR_ENTITLEMENT`: NOT ESTABLISHED.

### What would upgrade the claim

1. Preserve full Git objects, server-side commit and publication timestamps, earliest publicly reachable releases, archived artifacts, SHA256s, Lean/Mathlib pins, and reproducible CI logs.
2. Compare exact formal theorem statements, key nontrivial lemmas, dependency graphs and distinctive proof steps against the original external Lean archives, not merely the shared problem name.
3. Show a pre-announcement, independently verifiable proof of a **novel, material component** of the external construction, or an independent full solution.
4. Prepare an academically restrained claim citing exact source locations and original authors; seek specialist review.

This audit was based on existing GitHub source records and official external announcement/reporting, not a complete all-branches forensic replay. No source was copied from private repositories and no claim of authorship of OpenAI/Anthropic work is made.
