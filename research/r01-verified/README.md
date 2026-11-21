# R01 — resultados com verificação Lean registrada

Seleção de cinco declarações do snapshot `c114452706e06317fbb46a46eda14747cfc0cf2d`. O [certificado MVEI](../../mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json) registra o estado `fechado` de cada declaração e nenhuma dependência fora de `propext`, `Classical.choice` e `Quot.sound`. A verificação registrada usou Lean `v4.19.0`. Os links apontam para os fontes públicos desse snapshot.

| Declaração | Enunciado em resumo |
|---|---|
| [`DN_le_coefficient_error_sq`](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/CoefficientRealization.lean#L76) | O erro de qualquer aproximante por coeficientes dá uma cota superior para D_N. |
| [`finiteSpanApproximatesChi_iff_DNLimit_eq_zero`](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/ZeroLimitFrontier.lean#L103) | A aproximação de χ pelo span finito equivale a DNLimit = 0. |
| [`logMajorant_nonneg`](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L9) | O majorante logarítmico é não negativo quando K ≥ 0. |
| [`logMajorant_tendsto_zero`](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L19) | O majorante logarítmico converge a zero. |
| [`FINAL_ROOT_of_logMajorant`](../../branches/m-core-riemann/atk_terminal-parameter-law-20261003/lean/MCore/RH/NB/LogMajorantFinalProducer.lean#L53) | Uma cota logarítmica fornecida como hipótese implica DNLimit = 0. |

O R01 permanece `OPEN_MATH`. A prova da existência de um K uniforme ainda é necessária para aplicar o último teorema à família concreta e produzir o certificado de densidade. A demonstração textual da [ponte de Mellin](../r01-mellin-bridge/README.md) tem verificação numérica registrada e formalização Lean pendente.
