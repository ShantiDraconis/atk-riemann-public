# R01 — resultados com verificação Lean registrada

Seleção de cinco declarações do snapshot `c114452706e06317fbb46a46eda14747cfc0cf2d`. O [certificado MVEI](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json) registra o estado `fechado` de cada declaração e nenhuma dependência fora de `propext`, `Classical.choice` e `Quot.sound`. A verificação registrada usou Lean `v4.19.0`. Os links apontam para os fontes públicos desse snapshot.

| Declaração | Enunciado em resumo |
|---|---|
| [`DN_le_coefficient_error_sq`](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/CoefficientRealization.lean#L76) | O erro de qualquer aproximante por coeficientes dá uma cota superior para D_N. |
| [`finiteSpanApproximatesChi_iff_DNLimit_eq_zero`](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/ZeroLimitFrontier.lean#L103) | A aproximação de χ pelo span finito equivale a DNLimit = 0. |
| [`logMajorant_nonneg`](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L9) | O majorante logarítmico é não negativo quando K ≥ 0. |
| [`logMajorant_tendsto_zero`](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L19) | Para todo K real, o majorante logarítmico converge a zero. |
| [`FINAL_ROOT_of_logMajorant`](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L53) | Uma cota logarítmica fornecida como hipótese implica DNLimit = 0. |

O R01 permanece `OPEN_MATH`. Os lemas de não negatividade e convergência tratam do majorante em si. `FINAL_ROOT_of_logMajorant` exige uma cota para `DN` como hipótese. Para a família concreta, falta fornecer `explicitGramRateTarget_real : ExplicitGramRateTarget`, sem parâmetros, com um único K tal que D_N ≤ K / log(N+2) para todo N. Em N = 0, D_0 = 1 exige K ≥ log 2.

A certificação clássica sobre `riemannZeta` exige uma ponte verificada em Lean. Na rota E1, as provas de reprodução de Cauchy e de transporte do testemunho espectral ao L² real ainda estão pendentes. A [ponte direta de Mellin](https://github.com/ShantiDraconis/atk-riemann-public/blob/d76f04d1f7c3327784aa038c97088edc4f2ddc57/research/r01-mellin-bridge/README.md) é uma demonstração textual com testes numéricos e formalização Lean pendente.
