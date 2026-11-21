# R01 · Da perda mínima ao teorema concreto

## Decisão final da rodada de 21/11/2026

**Gate R01 desta rodada: `FINAL_FAIL`. Alvo matemático: `OPEN_MATH`.**

O critério de aprovação exigia uma prova incondicional compilada para o resíduo concreto. Na revisão avaliada, o teorema de fechamento recebe duas hipóteses. A transferência do sanduíche para o resíduo concreto ainda requer prova no kernel. A limitação de $L_N\log(N+2)$ por uma constante independente de $N$ ainda requer demonstração. A decisão encerra a avaliação desta revisão por insuficiência de prova. A validade da estimativa permanece em aberto.

[Revisão avaliada](https://github.com/ShantiDraconis/atk-riemann-public/commit/c963adf8642ef2999dd2737fa07d50efa154f1a4).

**Estado em 21/11/2026.** O fechamento condicional passou pelo kernel. A estimativa uniforme para o mínimo modular permanece em OPEN_MATH.

## Como usar uma família de teste

Para cada N ≥ 2, fixe M = 100N⁵. Denote por Q_N(λ) a soma de (1 + Σ_{k=2}^N λ_k (j mod k))²/[j(j+1)] para 1 ≤ j ≤ M, e por L_N seu mínimo. O mínimo existe porque os vetores de resíduos geram um subespaço de dimensão finita e a perda é o quadrado da distância ponderada ao vetor constante.

A comparação escrita no projeto usa o minimizador para mostrar D_N ≤ L_N + 1/N. Daí, para **qualquer** vetor de teste λ, a minimalidade dá

    D_N ≤ L_N + 1/N ≤ Q_N(λ) + 1/N.

Isso permite usar o controle de amplitude do minimizador mesmo quando os coeficientes de teste são grandes. A cauda estimada nessa comparação é a do minimizador. O texto usa B ≤ 10N² e a soma telescópica dos pesos, dando B²/(100N⁵+1) ≤ 1/N. A transferência desta comparação para o D_N concreto no kernel continua pendente. [Demonstração escrita da comparação](https://github.com/ShantiDraconis/atk-riemann-public/blob/cc7c4edf1ca7f686df198cf47431de03e9b25223/research/r01-fixed-rational-bridge/README.md).

Se existir C ≥ 0 e, para cada N ≥ 2, um vetor com Q_N(λ) log(N+2) ≤ C, então D_N log(N+2) ≤ C + log(N+2)/N ≤ C+1. A última desigualdade segue de log(N+2) = log 4 + log(1+(N−2)/4) ≤ log 4 + (N−2)/4 ≤ N. Nos índices 0 e 1, D_N ≤ 1 dá D_N log(N+2) ≤ log 3. Assim K = max(log 3,C+1) serve para todo N. A existência de C equivale à limitação superior do conjunto {L_N log(N+2) | N ≥ 2}, pois podemos escolher os minimizadores. Essa limitação segue aberta.

## Checklist das verificações

- [x] Emparelhamento modular, desigualdade dual de energia e implicação das duas premissas para ConcreteLogRate, dInf = 0 e RiemannHypothesis. A auditoria de 19:09:34 UTC lista propext, Classical.choice e Quot.sound. [Declarações e execução](https://github.com/ShantiDraconis/atk-riemann-public/blob/38f24c4d7ad273a8232c7092360fcf005d5860f2/research/audits/2026-11-21-modular-multipliers.md).
- [x] Vínculos nos múltiplos, energia e mínimo em seis células. A auditoria de 19:20:27 UTC registra 233/3682 com os dois coeficientes livres e 101/420 na fatia de um coeficiente. [Declarações e execução](https://github.com/ShantiDraconis/atk-riemann-public/blob/2a5785aaf0dffc94fe6c8a9eea20532d98f0bcae/research/audits/2026-11-21-multiple-links.md).
- [ ] Transferência concreta da comparação por truncagem em Lean.
- [ ] Prova incondicional do majorante uniforme e composição auditada sem hipóteses extras.

## Busca de um produtor

A enumeração das branches de m-core-riemann encontrou 181 referências. A leitura de conteúdo foi dirigida. Na revisão b7517526d4a70018580c06f4946c946dd20be3ce da rota de Pitágoras, o módulo de energia de Gram identifica a distância quadrática entre dois aproximantes com a energia de Gram da diferença de seus coeficientes. Essa identidade permite calcular o custo de corrigir uma candidata. Para obter a taxa ainda seria preciso estimar o erro resultante uniformemente em N. A auditoria anterior descreve cinco outras candidatas e explicita as hipóteses recebidas pela rota de três termos. [Auditoria das candidatas](../r01-material-branch-audit/README.md).

Esta nota consolida relatórios anteriores e uma dedução em texto. A rodada não executou novo build Lean.