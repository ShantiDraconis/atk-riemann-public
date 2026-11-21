# R01 · Localização das duas obrigações

Na main pública, a revisão a6da72c registra exatamente onde o fechamento recebe seus argumentos. O alvo quantitativo permanece OPEN_MATH. A decisão FINAL_FAIL refere-se à revisão avaliada.

| Peça | Localização pública | O que entrega |
|---|---|---|
| Transferência | [ConcreteClosure.lean, linhas 62–63](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-rational-spectral-exclusion/ConcreteClosure.lean#L62-L63) | Recebe DN N ≤ perda + 1/N. A comparação pelo minimizador e o controle de amplitude 10N² estão na [prova escrita](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-fixed-rational-bridge/README.md#L16-L40). |
| Estimativa uniforme | [ConcreteClosure.lean, linhas 64–66](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-rational-spectral-exclusion/ConcreteClosure.lean#L64-L66) | Recebe uma família com perda ≤ C/log(N+2), usando o mesmo C em todo N ≥ 2. A formulação pelo mínimo L_N está na [redução quantitativa](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-fixed-rational-bridge/README.md#L42-L56). |
| Uso das premissas | [ConcreteClosure.lean, linhas 84–86](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-rational-spectral-exclusion/ConcreteClosure.lean#L84-L86) | Combina as duas desigualdades para obter a taxa. [Auditoria do endpoint](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/audits/2026-11-21-modular-multipliers.md). |

## Onde procurar no checkout autorizado

Na revisão ATK 751835c6e1aa915d261828e5a120345bc5d2462c, sob `imports/M-Core/atk-kernel/ATK/`, os pontos de entrada são `RiemannConcrete.lean:29` (DN_le_residualSq), `BaezDuarteBridge.lean:58` (residualSq_eq_res) e `BaezDuarteBridge.lean:137` (integral_tail_sq). O primeiro limita DN pelo erro de qualquer aproximante. Os outros identificam a integral do erro e a sua parcela em x>1. Para λ modular, a escolha c₁=Σλₖ e cₖ=−kλₖ (k≥2) zera essa parcela. Falta compor no kernel a integração celular e a estimativa do erro omitido para o minimizador.

## Branches de m-core-riemann

A enumeração desta rodada retornou 181 branches. A leitura de código foi dirigida. Os links levam à [auditoria pública das candidatas](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-material-branch-audit/README.md#L7-L36).

- `atk/rh-bcf-three-term-materializer-20261001`, 2cd5c886fdc41945c381808b37c21904f61a07f2. Em `lean/MCore/RH/NB/BCFExplicitLogBounds.lean:16` a estrutura exige as estimativas. Na linha 34 entra a cota do termo de resíduos. A linha 60 combina os majorantes e a linha 107 fecha sob essas hipóteses.
- `audit/rh-log-majorant-materialized-20261001`, d029195cfe8ed76cad38b55b019db1b93e58ca83. Em `lean/MCore/RH/R0/ConcreteLogMajorantLaws.lean:9,35,50`, as declarações transportam uma cota disponível para constantes maiores.
- `atk/rh-r01-material-20261004`, 357ed7b5c06f1db5bd79ee60b8d98aeda0480a8b. O [ledger descrito na auditoria](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-material-branch-audit/README.md#L12) registra READY_CONDITIONAL.
- Na branch Claude, o [certificado e a revisão identificada](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-claude-branches/README.md#L8-L15) documentam 46 declarações fechadas. A inspeção registrada não localizou uma testemunha da taxa nesse conjunto.

## Restrições sobre uma candidata

O kernel verificou a [obstrução por múltiplo comum](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-rational-spectral-exclusion/DualMultipliers.lean#L166) e a [restrição do coeficiente do módulo 2](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-rational-spectral-exclusion/DualMultipliers.lean#L203). A nota sobre [limites dos coeficientes](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/r01-modular-coefficient-limits/README.md) deduz em texto que Σλₖ tende a −1 e kλₖ tende a μ(k) para cada k fixo se a perda tende a zero. O controle coletivo uniforme continua pendente.

[Decisão da revisão e checklist](https://github.com/ShantiDraconis/atk-riemann-public/blob/a6da72c37ca9fa345ebea40f51e9c3d3c33edb07/research/audits/2026-11-21-minimum-to-endpoint.md#L3-L9). Esta publicação localiza declarações e provas existentes, sem nova compilação Lean ou alteração de visibilidade dos repositórios de origem.
