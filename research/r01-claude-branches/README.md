# R01 — auditoria das branches identificadas pelo nome Claude

Em 21/11/2026, a busca paginada por nomes contendo Claude retornou
`claude/atk-protocol-setup-wzeajl` em M-Core e m-core-riemann, e nenhuma
branch em clay-riemann-proof. O recorte cobre os três repositórios da
auditoria R01. Trabalhos do Claude em branches com outro nome ou em
outros repositórios ficam fora desta busca nominal.

O [certificado público MVEI](../../mvei/branches/m-core-riemann/claude_atk-protocol-setup-wzeajl/certificate.json)
fixa a revisão `c21f9a9fb43489ff7f526f394392734e523cd98a` de m-core-riemann
e registra 46 declarações fechadas. A verificação está datada de
10/11/2026 às 04:38:10 UTC. No ledger da branch, a densidade concreta
continua OPEN_MATH. A leitura do certificado não identificou um produtor
da taxa de Gram nesse grupo de 46 declarações.

| Declaração certificada | Alcance |
|---|---|
| `ATK.Dichotomy.all_critical_iff_no_noncritical` | Para uma função complexa arbitrária, todos os zeros são críticos exatamente quando inexiste zero não crítico. |
| `ATK.Multiplicity.zero_iff_of_nonzero_factor` | Multiplicar por um fator que é não nulo no ponto preserva a condição de zero naquele ponto. |
| `ATK.Transport.zero_at_point_preserved_by_transport` | Se Ftil ∘ Φ = F, os valores de Ftil em Φ(s) coincidem com os de F em s. |
| `ATK.Transport.torus_sigma_periodicity_breaks_injectivity` | A periodicidade de período 1 na coordenada σ impede a injetividade global de Φ. |

Esses resultados permitem conferir um transporte de zeros quando sua
hipótese de composição é fornecida. O certificado de periodicidade
delimita o que se pode concluir de uma parametrização toroidal.
Os enunciados auditados não contêm uma estimativa do resíduo de
Báez–Duarte. O elo material continua sendo demonstrar
`explicitGramRateTarget_real : ExplicitGramRateTarget`, ou seja, um K
uniforme com D_N ≤ K/log(N+2) para todo N. A passagem de uma prova
qualitativa de RH à taxa permanece em aberto.

Esta nota publica a evidência já pública e o resultado da inspeção.
Nenhum novo build Lean foi executado.
