# Evidence-based state promotion — 2026-11-22

## Eligible now: six exact proven bridge items

Source: `ShantiDraconis/M-Core/atk-kernel/ATK/StatusFinal.lean`, definitions `pontesProvadas`, `pontesProvadas_validas`, `closed_pontes_true`.

| Item | Source proof | State in exact registry | Promotion |
|---|---|---|---|
| B1 Báez–Duarte sufficiency | `ATK.ObligationsClosed.B1` | `Quatro.T` | Already T; retain |
| B4 Cook–Levin | `ATK.ObligationsClosed.B4` | `Quatro.T` | Already T; retain |
| SAT ∈ NP | `ATK.SATemNP.sat_em_NP` | `Quatro.T` | Already T; retain |
| FLT for 3≤n≤22 | `ATK.FermatRegular.flt_tres_a_vinte_e_dois` | `Quatro.T` | Already T; retain |
| Finiteness of N(T) | `ATK.FechamentoO1.zerosAte_finito` | `Quatro.T` | Already T; retain |
| Littlewood ε>1/2 | `ATK.NecessidadeBD.entradaLittlewood_of_gt_half` | `Quatro.T` | Already T; retain |

**Already closed:** `closedMath pontesProvadas = true` is an explicit source theorem. No new promotion is needed for these six.

## Not eligible for promotion

- `obrigacoes C` contains eight `itemN`, so `openMath (obrigacoes C) = true` and `closedMath (obrigacoes C) = false` by source-level `rfl`.
- The five `lacunasMathlib` and five `pontesPublicadas` entries remain `itemN` in this registry, even where related results may exist in the literature or other repositories.
- An independently compiled proof of the **same exact proposition** is required before changing any `itemN` to `itemT`; mere resemblance or a stronger-looking theorem name is insufficient.
- The `closedMillennium` gate additionally requires fidelity, which remains unverified for O3/O5/O6/O7 and shadow-only for O8.
- The historical MVEI/CI certificates are not a new full kernel replay.

## Decision

**Six bridge items: certified T in the source registry. Eight terminal obligations: unchanged N.** Do not edit flags to a desired value or create a second misleading terminal registry. An implementation that promotes a specific obligation must include its exact proof term, `#check`, `#print axioms`, pinned build logs, source SHA, and model fidelity audit.

This report is an evidence classification, not a new kernel run or a claim of complete historical branch coverage.
