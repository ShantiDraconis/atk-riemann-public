# Cronologia pública — R01, densidade e Hipótese de Riemann

Esta cronologia registra os commits localizados, o escopo de cada resultado e a evidência disponível. Todas as horas são UTC. Datas de commits de desenvolvimento, de verificação e de publicação são registradas como eventos distintos.

| Data e hora UTC | Commit ou evidência | Resultado e estado |
|---|---|---|
| 21/09/2026 16:57:48 | `m-core-riemann@5c66f8dca03834f24a61a9b1219e7af9d4892dd6` | Argumento do confronto: um majorante que tende a zero fornece `DNToZero` e `DNLimit = 0`. O majorante entra como hipótese. |
| 21/09/2026 18:56:36 | `m-core-riemann@d6a291b4563f9021f74ab63cc983d44f079472da` | Equivalência entre a aproximação de χ pela família e `DNLimit = 0`. |
| 07/10/2026 18:05:35 | Snapshot `c114452706e06317fbb46a46eda14747cfc0cf2d` do `m-core-riemann` | Fontes das cinco declarações selecionadas no índice público. |
| 13/10/2026 22:08:29 | `M-Core@9e27bb5feef04d0f9a8609b548eca2134b415010` | Ponte de Báez–Duarte em Lean: densidade implica a RH do Mathlib. |
| 14/10/2026 02:26:52 | `M-Core@abc4226d8a281628d92259d41ab085b34e759712` | Fórmula espectral para o resíduo e reformulação do limite na reta crítica. |
| 27/10/2026 03:56:12 | `M-Core@f1d516f71653603a4b1b5c0e53a17e47a68fdce2` | Direção de von Koch: uma cota global sobre a soma centrada de von Mangoldt implica exclusão de zeros no semiplano correspondente. |
| 27/10/2026 04:10:01 | `M-Core@7ccfb308bb31880be940eaf6502285d3e40ecf6a` | Equivalência de von Koch. |
| 27/10/2026 11:47:02 | `M-Core@b7f16721db6fdcfb09f7303ab1e1d81e3f110c44` | Versão unilateral via Landau–Pringsheim, condicionada a uma cota global. |
| 10/11/2026 04:38:10 | [Certificado MVEI do branch](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json) | Verificação registrada com Lean 4.19.0. As cinco declarações do índice constam como fechadas e sem axiomas além dos três padrão. |
| 11/11/2026 21:46:03 | [Relatório MVEI do M-Core](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/mvei/README.md), revisão `390e378` | Build registrado do `atk-kernel` com Lean 4.34.1. A auditoria de anterioridade liga os blobs públicos da ponte, de von Koch e da versão unilateral a essa revisão. |
| 20/11/2026 | [Anúncio de Levent Alpöge](https://alpo.ge/remark.pdf) | A cronologia do autor situa a escolha da soma ponderada em 20/10 e os theta lifts iterados em 15/11. O critério utilizado na rota anunciada é localizado em janelas. |
| 21/11/2026 12:48:37 | `m-core-riemann@4e2d91ccb53105530ca21d9abe7bdb9ef9fe8ae2` | Gate passa a exigir relatórios de axiomas e aplicar lista de permissões. Validação do runner por simulação. |
| 21/11/2026 12:51:40 | `m-core-riemann@ca22606221531b4afbb36b26adc1bbbc87ea191d` | Build explícito antes da auditoria e status de candidato restrito ao certificado de densidade. Validação do runner por simulação. |
| 21/11/2026 13:00:35 | [Ponte direta de Mellin, `d071506`](https://github.com/ShantiDraconis/atk-riemann-public/commit/d0715064c9813cc4a240d18446e6b442e9b849e3) | Publicação do argumento em texto matemático. O script publicado passou em nove testes numéricos. A formalização desse argumento específico está pendente. |
| 21/11/2026 13:03:41 | [Índice de declarações Lean, `658ed8c`](https://github.com/ShantiDraconis/atk-riemann-public/commit/658ed8c3c8061b31d0675421d11baf6dd1f20ae6) | Publicação do índice das cinco reduções verificadas. |
| 21/11/2026 13:08:02 | [Experimento de Möbius suavizado, `1419c2e`](https://github.com/ShantiDraconis/atk-riemann-public/commit/1419c2ea71be55896cd031d60ddcb858dba0e270) | Publicação da decomposição do erro e de cálculos para cinco valores de N. Os pesos são de Bettin, Conrey e Farmer, preprint de 22/11/2012. |
| 21/11/2026 13:24:52 | [Auditoria de anterioridade, `5eda13a`](https://github.com/ShantiDraconis/atk-riemann-public/commit/5eda13a05c42112ec945bebf97b2f6644af76546) | Publicação dos hashes e da correspondência com a revisão auditada. |

## Fronteira matemática

O R01 segue em `OPEN_MATH`. O produtor `explicitGramRateTarget_real : ExplicitGramRateTarget` exige um K uniforme com D_N ≤ K/log(N+2) para todo N. Como D_0 = 1, segue K ≥ log 2. A redução formal de outubro no M-Core usa a hipótese de densidade, e a ponte textual de novembro usa um funcional direto. A cota uniforme do produtor e a integração do endpoint no gate do m-core-riemann continuam pendentes.

Os commits de outubro estabelecem anterioridade documental local em relação ao anúncio público de novembro. A prioridade sobre a construção em janelas e os theta lifts exigiria uma evidência anterior com essas peças concretas. Uma data de commit por si só identifica o registro no histórico Git. A primeira disponibilização pública, a data de concepção e a primazia sobre uma construção específica exigem evidência própria.
