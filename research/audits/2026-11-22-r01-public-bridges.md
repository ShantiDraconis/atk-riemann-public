# R01 — Pontes públicas verificáveis (2026-11-22)

**Status:** OPEN_MATH=true; CLOSED_MATH=false. **Submissão:** ainda não submetido à revisão por pares. Este documento é um mapa de interfaces matemáticas já publicadas, não uma certificação de RH.

## Fonte canônica do endpoint público

- [ConcreteClosure.lean](../r01-rational-spectral-exclusion/ConcreteClosure.lean): `R01.closure_of_modular_multipliers` recebe `htransfer` e `hwitness` e deduz `ConcreteLogRate ∧ dInf = 0 ∧ RiemannHypothesis`.
- [Closure.lean](../r01-rational-spectral-exclusion/Closure.lean): verificar o caminho importado de `rh_of_dInf_eq_zero` no projeto reproduzível.
- [DualMultipliers.lean](../r01-rational-spectral-exclusion/DualMultipliers.lean): `multiplierLoss` e restrições aritméticas.

### Interfaces a construir, sem pressupor sua existência

Para um coeficiente `v : ℕ → ℕ → ℝ` e constante `C : ℝ`, é necessário obter **termos independentes** das duas declarações abaixo, preservando as definições públicas:

```lean
-- Esquema de assinatura; não é uma prova nem um módulo compilado.
-- (htransfer : ∀ N : ℕ, 2 ≤ N →
--   DN N ≤ multiplierLoss N (100*N^5) 1 (v N) + 1/(N : ℝ))
-- (hwitness : ∀ N : ℕ, 2 ≤ N →
--   multiplierLoss N (100*N^5) 1 (v N) ≤ C / Real.log ((N : ℝ)+2))
-- (hC : 0 ≤ C)
-- R01.closure_of_modular_multipliers C hC v htransfer hwitness
```

A linha de aplicação é **condicional** até existirem termos fechados para os dois argumentos. Não transformar estas interfaces em axiomas ou campos de estruturas supostamente preenchidas.

## Pontes para os módulos recuperados

| Fonte pública | Declaração | Premissa efetiva | Próximo teste |
|---|---|---|---|
| [MaterialRecovery.lean](../branches/m-core-riemann/atk_rh-material-recovery-20261007/lean/MCore/RH/R0/MaterialRecovery.lean) | `recovered_terminal_of_explicitGramRate` | `ExplicitGramRateTarget` | Localizar termo incondicional deste alvo |
| Mesmo módulo | `recovered_terminal_of_bcfExplicitLogBounds` | `BCFExplicitLogBounds` | Construir constantes e provar as três desigualdades |
| Mesmo módulo | `recovered_terminal_of_coefficient_error_tendsto_zero` | Convergência de erro L² | Localizar coeficientes concretos e prova de convergência |
| [BCFExplicitLogBounds.lean](../branches/m-core-riemann/atk_rh-material-recovery-20261007/lean/MCore/RH/NB/BCFExplicitLogBounds.lean) | `dn_le_combined_log_majorant` | `H : BCFExplicitLogBounds D B` | Não confundir a combinação com a produção de `H` |
| Mesmo módulo | `FINAL_ROOT_of_explicit_bcf_bounds` | `H : BCFExplicitLogBounds D B` | Inspecionar tipo completo e axiomas |

**Atenção:** os símbolos `DN` e `explicitGramResidual` vivem em formalizações diferentes. Uma ponte entre eles exige uma igualdade ou estimativa formalizada, com o mesmo espaço de Hilbert, geradores, índices, normalização e definição da distância. Nomes semelhantes não autorizam substituição.

## Cadeia pública de auditoria

1. Recuperar as dependências mínimas de cada módulo e construir no Lean/Mathlib fixado no projeto de origem.
2. Executar `#check @...` e `#print axioms ...` para cada produtor, sem esconder parâmetros implícitos.
3. Exigir uma declaração **sem argumentos equivalentes a RH** que forneça a testemunha quantitativa ou o limite de erro.
4. Provar, se possível, a comparação de coeficientes `Fin N`, integral celular e estimativa de truncamento necessária para `htransfer`.
5. Conferir que o resultado final usa `RiemannHypothesis` canônico e `riemannZeta` sem redefinições locais.
6. Não promover status terminal até a compilação reproduzível e inspeção de dependências transitivas.

## Estado editorial

**Independent research / preprint / work in progress. Not yet submitted for formal peer review.**

Esta auditoria registra pontos de conexão verificáveis entre artefatos já públicos. Não representa revisão por pares, nova compilação de todos os módulos ou prova incondicional da hipótese de Riemann.
