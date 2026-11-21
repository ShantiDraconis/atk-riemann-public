# Registro público de anterioridade documental — Riemann

Autor do projeto: Tiago Paschoalatto Fagliari (ShantiDraconis). Este registro reúne a lógica matemática, as revisões de desenvolvimento e as evidências públicas disponíveis. As datas abaixo são UTC. A data deste registro é a do commit público que adicionou este arquivo.

| Registro de desenvolvimento | Lógica materializada | Evidência pública |
|---|---|---|
| 13/10/2026 22:08:29, `9e27bb5` | A densidade de Báez–Duarte, expressa por D_N → 0, implica a RH do Mathlib. | [Declaração Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/BaezDuarteBridge.lean#L370) |
| 15/10/2026 20:14:00, `f81c6ef` | A recíproca e a equivalência RH ↔ D_N → 0. | [Código Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/NecessidadeRH.lean) |
| 27/10/2026 03:31:04, `c8f12c7` | Formalização da soma suavizada S(x) = Σ Λ(n)(1−n/x), da inversão de Mellin e de uma cota na escala clássica do teorema dos números primos. | [Código Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/ChebyshevSuave.lean) |
| 27/10/2026 03:56:12, `f1d516f` | Uma cota global de von Koch para ψ implica RH. | [Declaração Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKoch.lean#L328) |
| 27/10/2026 04:10:01, `7ccfb30` | Equivalência de von Koch entre RH e a estimativa para ψ. | [Declaração Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKochRH.lean#L721) |
| 27/10/2026 11:47:02, `b7f1672` | Uma cota unilateral global sobre ψ(N)−N implica exclusão de zeros em Re(s)>θ via Landau–Pringsheim. | [Declaração Lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L818) |
| 29/10/2026 21:51:39, `ee8a04e` | Port público do critério de Báez–Duarte com auditoria de axiomas. | [Commit público](https://github.com/ShantiDraconis/clay-riemann-proof/commit/ee8a04e3a7487e542f62e61de870dea082604ce7) · [Auditoria](https://github.com/ShantiDraconis/clay-riemann-proof/blob/ee8a04e3a7487e542f62e61de870dea082604ce7/ClayRiemannProof/Audit.lean) |

## Correspondência matemática

A soma bruta da rota anunciada por Alpöge é R(x) = Σ Λ(n)(x/n−1). Para x ≥ 1, somação e integração por partes dão

```text
x S(x) = ∫₁ˣ ψ(t) dt
R(x) = x ∫₁ˣ ψ(t)/t² dt
     = S(x) + 2x ∫₁ˣ S(t)/t² dt.
```

A relação integral foi documentada em 21/11/2026. A [demonstração termo a termo e o código algébrico Lean](https://github.com/ShantiDraconis/atk-riemann-public/blob/6c1fb1d4d900754a21d4ba1defe3724af1169f00/research/branch-inventory-and-ramp/README.md) incluem o estado da verificação. O arquivo algébrico ainda aguarda uma compilação Lean registrada.

## Alcance da anterioridade

O histórico documenta que as formalizações locais da suavização, de von Koch e da redução unilateral antecedem o anúncio público de Alpöge em 20/11/2026. Na [cronologia do próprio anúncio](https://alpo.ge/remark.pdf), a escolha da rampa data de 20/10 e os theta lifts iterados de 15/11. A sobreposição demonstrável envolve somas ponderadas relacionadas por uma identidade integral e exclusão de zeros a partir de cotas. A primazia mundial, a primeira publicação de cada arquivo e a prioridade sobre a construção por janelas, caracteres ou theta lifts permanecem indeterminadas. O critério de Báez–Duarte e a equivalência de von Koch são resultados clássicos.

O R01 quantitativo permanece OPEN_MATH. A prova de que algum K uniforme satisfaz D_N ≤ K/log(N+2) para todo N continua pendente. O presente registro usa as verificações existentes, sem novo build.

## Evidência complementar

- [Índice geral dos certificados públicos do kernel](https://github.com/ShantiDraconis/atk-riemann-public/blob/a43d2bbaf3c80af4a0bf2c5f65657c97f1288461/research/kernel-verified-index/README.md)
- [Cronologia do R01](https://github.com/ShantiDraconis/atk-riemann-public/blob/5cd7633f605175486456eb2c5dbb0221546d3d8e/research/r01-timeline/README.md)
- [Hashes das declarações no espelho e na revisão auditada](https://github.com/ShantiDraconis/atk-riemann-public/blob/5eda13a05c42112ec945bebf97b2f6644af76546/research/branch-priority-audit/README.md)
- [Cadeia estrutural e hipóteses](https://github.com/ShantiDraconis/atk-riemann-public/blob/d2632f5c1b40430fe76b92f2eab69af29d6221c2/research/riemann-structural-chain/README.md)
