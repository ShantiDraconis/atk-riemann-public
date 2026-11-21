# R01 — critério completo em Lean e busca por produtor da taxa

## Resultado encontrado na expansão do histórico

| Commit em UTC | Conteúdo público |
|---|---|
| 13/10/2026 22:08:29, `9e27bb5` | [Suficiência de Báez–Duarte](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/BaezDuarteBridge.lean#L370). A convergência de DN a zero implica a RH do Mathlib. |
| 15/10/2026 20:14:00, `f81c6ef` | [Recíproca e equivalência no M-Core](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/NecessidadeRH.lean). `necessidade` demonstra RH → DN → 0. `rh_iff_DN` combina as duas implicações. |
| 29/10/2026 21:51:39, `ee8a04e` | [Port público em clay-riemann-proof](https://github.com/ShantiDraconis/clay-riemann-proof/commit/ee8a04e3a7487e542f62e61de870dea082604ce7), com a [fonte da prova](https://github.com/ShantiDraconis/clay-riemann-proof/blob/ee8a04e3a7487e542f62e61de870dea082604ce7/ClayRiemannProof/BaezDuarte/Necessity.lean) e [auditoria via guard_msgs](https://github.com/ShantiDraconis/clay-riemann-proof/blob/ee8a04e3a7487e542f62e61de870dea082604ce7/ClayRiemannProof/Audit.lean). A auditoria especifica propext, Classical.choice e Quot.sound para `rh_iff_DN` e `target_iff_gap`. |

O registro adiciona a recíproca qualitativa que faltava na [cronologia anterior](https://github.com/ShantiDraconis/atk-riemann-public/blob/5cd7633f605175486456eb2c5dbb0221546d3d8e/research/r01-timeline/README.md). A formalização do critério completo precede o anúncio público de 20/11/2026. O critério é clássico e tem como referência [Báez–Duarte](https://arxiv.org/abs/math/0202141). A cronologia documenta os commits localizados.

## Cobertura e fronteira

A enumeração paginada retornou 181 branches em m-core-riemann, 424 em M-Core e 52 em clay-riemann-proof. A leitura de conteúdo foi dirigida. Em 27 branches de m-core-riemann que correspondem a rotas de materialização, limite zero ou majorante logarítmico, a consulta pelo caminho canônico `lean/MCore/RH/R0/HardFrontierReal.lean` retornou ausência. A busca de commits por `explicitGramRateTarget_real` também não retornou ocorrências. Isso deixa em aberto possíveis provas sob outros nomes ou em branches fora da inspeção de conteúdo.

A equivalência qualitativa prova RH ↔ DN → 0. O produtor do R01 exige adicionalmente a cota quantitativa uniforme DN ≤ K/log(N+2) para todo N. O estado do produtor permanece `OPEN_MATH`. Esta publicação liga as provas e auditorias já presentes em fontes públicas. Nenhum novo build foi executado nesta rodada.
