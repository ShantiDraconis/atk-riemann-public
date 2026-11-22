# ATK — Prioridade técnica para OPEN_MATH=false / CLOSED_MATH=true

**Data:** 2026-11-22. **Estado desta auditoria:** NÃO CERTIFICADO; manter `OPEN_MATH=true`, `CLOSED_MATH=false`. Pesquisa independente ainda não submetida a revisão por pares.

## 1. Significado formal das flags (fonte primária)

Em [M-Core/atk-kernel/ATK/StatusFinal.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/StatusFinal.lean), `itemT nome P p` exige um termo `p : P`, enquanto `itemN` não contém tal prova. `closedMath` exige que cada item esteja em `Quatro.T`, e `closedMath_correto` garante que todos os enunciados da lista sejam provados. `open_math_true` e `closed_math_false` computam o estado atual de `obrigacoes` (O1–O8). **Alterar manualmente uma string, comentário ou JSON não satisfaz o portão.**

A fidelidade é outro requisito: `closedMillennium` exige prova **e** correspondência com o enunciado Millennium. O8 está marcado `sombra`; O3/O5/O6/O7 têm fidelidade `naoConferida`. Mesmo uma prova de O8 tal como atualmente codificado não fecha automaticamente Yang–Mills do Clay.

## 2. Evidências verificadas por inspeção de fontes públicas e registros existentes

| Prioridade | Evidência / localização | O que já entrega | O que impede promover |
|---|---|---|---|
| P0 | [StatusFinal.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/StatusFinal.lean) — `itemT`, `closedMath_correto`, `obrigacoes`, `closedMillennium` | Critério formal fail-closed | Falta prova de cada O1–O8 e fidelidade dos enunciados |
| P0 | [FinalRoot.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/FinalRoot.lean) — `raiz_de_produtores` | `PontesRestantes M → Produtores M → Raiz M` | Não há construção incondicional de `PontesRestantes` e `Produtores` |
| P0 | [ClosedMathReal.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/ClosedMathReal.lean) — `closedMath_real` | Montagem formal a partir de `Lacunas` | `Lacunas` contém obrigações substantivas; não é testemunha terminal |
| P1 | [ConcreteClosure.lean](../r01-rational-spectral-exclusion/ConcreteClosure.lean) — `closure_of_modular_multipliers` | `htransfer + hwitness → ConcreteLogRate → dInf=0 → RiemannHypothesis` | Provas incondicionais de `htransfer` e `hwitness` |
| P1 | [MaterialRecovery.lean](../branches/m-core-riemann/atk_rh-material-recovery-20261007/lean/MCore/RH/R0/MaterialRecovery.lean) | Três rotas alternativas para o certificado de RH | Construir `ExplicitGramRateTarget`, `BCFExplicitLogBounds` ou convergência L² |
| P1 | [BCFExplicitLogBounds.lean](../branches/m-core-riemann/atk_rh-material-recovery-20261007/lean/MCore/RH/NB/BCFExplicitLogBounds.lean) | Soma três majorantes para taxa logarítmica | A estrutura `BCFExplicitLogBounds` recebe as três estimativas |
| P2 | [StatusFinal.lean](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/ATK/StatusFinal.lean) — `pontesProvadas` | B1 Báez-Duarte, B4 Cook–Levin, SAT∈NP e resultados parciais | Revalidar contra HEAD, sem confundir pontes com O1/O4 |
| P2 | [status_calculado.md](https://github.com/ShantiDraconis/M-Core/blob/main/atk-kernel/audits/status_calculado.md) | Inventário histórico: 0/7 produtores materiais; B1/B3/B4 e L1/L2 listados como provados | Relatório de 2026-10-22, não compilação nova |
| P3 | [RELATORIO_HONESTO.md](https://github.com/ShantiDraconis/M-Core/blob/main/RELATORIO_HONESTO.md) | Descreve lacunas de necessidade RH, pontes e fidelidade | Histórico de congelamentos não certifica as obrigações terminais |

## 3. Portões matemáticos por problema

- **O1 / RH:** obter termo incondicional de `RiemannHypothesis` canônico. Caminhos conhecidos: prova da taxa uniforme de `DN`; `hwitness+htransfer`; ou testemunha BCF/Gram/coefficient L². Equivalência com RH **não é prova** de RH.
- **O2 / Beal:** fechar o produtor residual com suas pontes legítimas, sem tomar Beal como campo assumido.
- **O3 / Navier–Stokes:** demonstrar a estimativa a priori e verificar a fidelidade da ligação ao PDE físico; B3, por si, não fecha O3.
- **O4 / P ≠ NP:** construir `SATNotInP` no modelo genuíno. Cook–Levin e SAT∈NP não bastam.
- **O5 / Hodge:** demonstrar o produtor de codimensão intermediária e formalizar as construções de analitificação, decomposição de Hodge e classe de ciclo.
- **O6 e O7 / BSD:** fechar posto e fórmula refinada para o alvo geral, não somente exemplos numéricos.
- **O8 / Yang–Mills:** antes da promoção, substituir/verificar o alvo-sombra por um enunciado fiel ao problema Clay; então construir o produtor correspondente.

## 4. Ordem operacional de integração

1. **P0 — auditoria do gate:** gerar `#check @` e `#print axioms` para todos os candidatos e seus produtores, com SHA e logs reproduzíveis.
2. **P1 — recuperação mínima:** inspecionar branches e módulos históricos, confrontar assinaturas e dependências; portar apenas lemas realmente novos e úteis, com testes de regressão.
3. **P1 — RH concreto:** primeiro a ponte de normalização/coeficientes e integral celular para `htransfer`; em paralelo, buscar testemunha quantitativa incondicional para `hwitness`. Sem a última, a rota permanece aberta.
4. **P2 — demais obrigações:** isolar um produtor material por O2–O8, com requisitos de fidelidade, sem misturar teoremas paramétricos e conjecturas canônicas.
5. **P3 — certificação:** só após build do alvo completo, sem `sorryAx`/axiomas novos, com termos incondicionais para cada obrigação e revisão do enunciado, atualizar as flags por cálculo do gate.

## 5. Evidência que ainda NÃO existe nesta publicação

Este documento **não** executou uma compilação Lean nova nem encontrou uma prova terminal incondicional de RH, Beal, P ≠ NP ou das outras obrigações. O levantamento é baseado na leitura de código e relatórios versionados; `#print axioms` de teoremas condicionais não demonstra seus parâmetros. **Não alterar as flags antes de satisfazer todos os portões.**

Relacionado: [mapa de pontes públicas](2026-11-22-r01-public-bridges.md) e [registro de lacunas R01](2026-11-22-r01-public-gap-register.md).
