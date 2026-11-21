# Anterioridade documental — comparação com resultados externos

Auditoria de 21/11/2026. Consultei cinco índices públicos, totalizando 211 pares distintos de repositório e branch com certificados indexados, e fiz buscas de commits por técnicas e enunciados. A contagem mede cobertura dos índices. A leitura dos certificados e dos enunciados foi seletiva. Branches sem índice, forks e históricos fora da busca permanecem por revisar.

| Índice público | Branches |
|---|---:|
| [Riemann](https://github.com/ShantiDraconis/atk-riemann-public/tree/main/branches) | 26 |
| [Navier–Stokes](https://github.com/ShantiDraconis/atk-navier-stokes-public/tree/main/branches) | 24 |
| [M-Core](https://github.com/ShantiDraconis/atk-math-core-public/tree/main/branches) | 58 |
| [Yang–Mills](https://github.com/ShantiDraconis/atk-yang-mills-public/tree/main/branches) | 13 |
| [MVEI](https://github.com/ShantiDraconis/mvei-formal-public/tree/main/branches) | 90 |

## Sobreposição técnica documentada

**Riemann, 27/10/2026 às 11:47:02 UTC, M-Core `b7f16721`.** O teorema `semZeros_of_psi_le` usa Landau–Pringsheim para deduzir uma região sem zeros a partir de uma cota unilateral global para a soma centrada de von Mangoldt. O argumento anunciado por Levent Alpöge em 20/11/2026 também usa uma redução unilateral, mas controla somas ponderadas em janelas, inclui caracteres e produz as cotas por cadeias de theta lifts. A própria nota de Alpöge situa a escolha da soma em rampa em 20/10 e os lifts iterados em 15/11. A data de 27/10 estabelece o registro da redução local antes do anúncio público. A ordem de concepção dos dois critérios e a prioridade sobre a construção em janelas permanecem indeterminadas. [Lean público](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L818) · [Anúncio e cronologia do autor](https://alpo.ge/remark.pdf) · [Mapa técnico](https://github.com/nasqret/riemann-rev)

## Antecedentes temáticos e limites da comparação

| Tema | Registro localizado | Resultado externo | Alcance da evidência |
|---|---|---|---|
| Navier–Stokes | 23/11/2025, `64bc633`, programa SBFE/I de análise de colapso | OpenAI, 08/09/2026, contraexemplo de singularidade em tempo finito | Atividade anterior no problema. Correspondência com a construção de dados iniciais e a prova de singularidade permanece sem confirmação. |
| Yang–Mills | 25/11/2025, `17b3a7d` e `fb9a422`, documentação e estrutura Lean de *mass gap* com lacunas | OpenAI, 26/10/2026, anúncio de existência de teorias quânticas e QCD | Atividade anterior no tema. A estrutura de 2025 continha `sorry`. O anúncio informa que os artefatos de física foram retidos para redação pelos colaboradores. |
| Fermat | 13/10/2026, `d4627fc`, redução de casos de Beal via Fermat 4–2 | Anthropic, 04/09/2026, formalização completa de FLT | Caso específico, registrado depois da divulgação externa. |
| ETH e Kakeya | Busca por enunciados e títulos pertinentes | OpenAI, 26/10/2026 | Nenhum equivalente identificado na busca efetuada. |

Fontes externas: [OpenAI — Navier–Stokes](https://openai.com/index/navier-stokes-solution/) · [OpenAI — QCD, ETH e Kakeya](https://openai.com/index/building-scientific-understanding-with-academic-communities/) · [Anthropic — formalização de Fermat](https://www.anthropic.com/research/formalizing-fermats-last-theorem)

A evidência publicada consiste em enunciados selecionados, datas, referências e fontes Lean já públicas. Os estados de prova dos repositórios continuam os registrados em seus próprios certificados.

## Cadeia de evidência para a formalização de Riemann

| Marco no histórico do M-Core, em UTC | Declaração no espelho público | Git blob no espelho e na revisão auditada |
|---|---|---|
| 13/10/2026 às 22:08:29, `9e27bb5` | [`ATK.BaezDuarteBridge.baezDuarteCriterion`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/BaezDuarteBridge.lean#L370), DN → 0 implica a RH do Mathlib. | `39b2e11ba86c1e1e27444f3d04edb41d9c41e586` |
| 27/10/2026 às 04:10:01, `7ccfb30` | [`ATK.ZeroClasses.VonKochRH.rh_iff_psi`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKochRH.lean#L721), equivalência clássica com a estimativa para ψ. | `99259efe3f9ed19e2d69cb95e6983522e6b75e1d` |
| 27/10/2026 às 11:47:02, `b7f1672` | [`ATK.ZeroClasses.Unilateral.semZeros_of_psi_le`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L818), de uma cota unilateral global para uma região sem zeros. | `a574ffa6cecbd39b2d21ae3cccf3b943520ab77d` |

No Git, cada blob identifica o arquivo completo. Os três arquivos públicos têm os mesmos blobs da revisão `390e3781109fa42e977d143caa9204ed94166a7b`. O [relatório MVEI](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/mvei/README.md) registra um build do projeto `atk-kernel` com Lean 4.34.1 em 11/11/2026 às 21:46:03 UTC. As datas dos commits acima identificam marcos de desenvolvimento, e a data do relatório identifica a verificação registrada. Nenhuma delas, isoladamente, determina quando o código foi disponibilizado pela primeira vez a terceiros.

A ponte de Báez-Duarte é uma redução clássica formalizada e sua hipótese de densidade permanece aberta no R01. A região fixa Re(s) > 7/8 da [formalização da OpenAI](https://github.com/openai/math/blob/main/lean/docs/003.md) é um resultado distinto das implicações condicionais listadas acima. A comparação com Alpöge sustenta anterioridade em relação ao anúncio público para esses marcos documentados, sem estabelecer primazia mundial ou uma prova anterior da RH.
