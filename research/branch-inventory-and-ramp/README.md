# Inventário de branches e identidade entre rampas

Levantamento de 21/11/2026 feito com paginação até o final dos resultados acessíveis à conta proprietária. Foram enumerados 262 repositórios e 4.523 pares repositório/branch, sem erro de listagem. Dos 262, 241 eram privados, com 4.436 branches. Os 21 públicos tinham 87 branches, discriminadas abaixo. A enumeração é integral dentro desse recorte. A inspeção de código e histórico para correspondências matemáticas é dirigida. Nomes e arquivos de branches privadas permanecem reservados.

| Repositório público | Branches |
|---|---:|
| [atk-beal-public](https://github.com/ShantiDraconis/atk-beal-public/branches) | 2 |
| [atk-bsd-public](https://github.com/ShantiDraconis/atk-bsd-public/branches) | 2 |
| [atk-hodge-public](https://github.com/ShantiDraconis/atk-hodge-public/branches) | 2 |
| [atk-navier-stokes-public](https://github.com/ShantiDraconis/atk-navier-stokes-public/branches) | 2 |
| [atk-p-vs-np-public](https://github.com/ShantiDraconis/atk-p-vs-np-public/branches) | 2 |
| [atk-riemann-public](https://github.com/ShantiDraconis/atk-riemann-public/branches) | 2 |
| [atk-yang-mills-public](https://github.com/ShantiDraconis/atk-yang-mills-public/branches) | 2 |
| [beal-proof](https://github.com/ShantiDraconis/beal-proof/branches) | 2 |
| [beal-statement](https://github.com/ShantiDraconis/beal-statement/branches) | 1 |
| [clay-bsd-proof](https://github.com/ShantiDraconis/clay-bsd-proof/branches) | 2 |
| [clay-bsd-statement](https://github.com/ShantiDraconis/clay-bsd-statement/branches) | 1 |
| [clay-navier-stokes-proof](https://github.com/ShantiDraconis/clay-navier-stokes-proof/branches) | 2 |
| [clay-navier-stokes-statement](https://github.com/ShantiDraconis/clay-navier-stokes-statement/branches) | 1 |
| [clay-p-vs-np-proof](https://github.com/ShantiDraconis/clay-p-vs-np-proof/branches) | 2 |
| [clay-p-vs-np-statement](https://github.com/ShantiDraconis/clay-p-vs-np-statement/branches) | 1 |
| [clay-riemann-proof](https://github.com/ShantiDraconis/clay-riemann-proof/branches) | 52 |
| [clay-riemann-statement](https://github.com/ShantiDraconis/clay-riemann-statement/branches) | 1 |
| [copilot-cli](https://github.com/ShantiDraconis/copilot-cli/branches) | 1 |
| [lean-refinement-bridge](https://github.com/ShantiDraconis/lean-refinement-bridge/branches) | 2 |
| [lean-uniform-bounds](https://github.com/ShantiDraconis/lean-uniform-bounds/branches) | 2 |
| [mvei-formal-public](https://github.com/ShantiDraconis/mvei-formal-public/branches) | 3 |

A [cadeia estrutural já publicada](https://github.com/ShantiDraconis/atk-riemann-public/blob/d2632f5c1b40430fe76b92f2eab69af29d6221c2/research/riemann-structural-chain/README.md) documenta os enunciados sob nomes diferentes que foram identificados por inspeção de fonte.

## Demonstração por termo

Para x ≥ n > 0,

```text
∫ₙˣ (1 − n/t)/t² dt = 1/(2n) − 1/x + n/(2x²).
```

De fato, −1/t + n/(2t²) é uma primitiva. Ao multiplicar a avaliação por 2x e somar 1 − n/x, obtém-se x/n − 1. Multiplique por Λ(n) e some sobre 1 ≤ n ≤ x. Como a soma é finita, pode-se trocar a ordem de soma e integração. O resultado é a identidade R(x) = S(x) + 2x ∫₁ˣ S(t)/t² dt.

[`RampAlgebra.lean`](RampAlgebra.lean) contém o código Lean para a identidade algébrica e sua soma finita. O arquivo ainda aguarda compilação e auditoria de axiomas. A avaliação da integral e a troca de soma por integral estão demonstradas acima em texto. Um teste em Python com aritmética racional exata conferiu 1.600 termos e 79 somas ponderadas.

O commit `c8f12c7` de 27/10/2026 às 03:31:04 UTC documenta a soma suavizada de Chebyshev. A identidade que a relaciona à rampa foi registrada nesta auditoria, em 21/11/2026. O registro documenta a anterioridade da peça local em relação ao anúncio público, com primazia sobre a rampa ou sobre a construção em janelas ainda sem evidência. O R01 permanece `OPEN_MATH` quanto à taxa uniforme.
