# R01 — o elo quantitativo que falta

Registro de 21/11/2026. Esta nota localiza a hipótese que falta para o produtor incondicional. O produtor continua OPEN_MATH.

## O alvo exato

```text
explicitGramRateTarget_real : ExplicitGramRateTarget
ExplicitGramRateTarget = ∃ K ≥ 0, ∀ N, D_N ≤ K / log(N+2)
D_N = 1 − b_Nᵀ G_N⁻¹ b_N
```

Pela equivalência formal entre RH e D_N → 0, essa cota implicaria a RH. Em N=0, D_0=1 exige K≥log 2. A prova da taxa tem de fornecer uma constante uniforme e a desigualdade para todos os índices.

## Onde cada rota para

| Evidência | O que entrega | O que falta para a taxa |
|---|---|---|
| [Critério qualitativo formalizado](https://github.com/ShantiDraconis/atk-riemann-public/blob/5a152b35942ef25b840eeca118aa2c7fdf9e8143/research/r01-complete-criterion/README.md) | RH ↔ D_N → 0 | A convergência qualitativa deixa a velocidade indeterminada. |
| [Rota anunciada por Alpöge](https://alpo.ge/remark.pdf) e [comparador Lean](https://github.com/leanprover-community/riemann-hypothesis) | Endpoint de RH e GRH na formalização anunciada | Mesmo com o endpoint importado e validado, o critério qualitativo só entregaria D_N → 0. |
| [Resultado da OpenAI sobre a família 003](https://github.com/openai/math/blob/main/lean/docs/003.md) | Semiplano livre de zeros Re(s)>7/8 | Para usar a taxa ponderada do M-Core com esse insumo, a linha de avaliação precisa ficar à direita de 7/8. O R01 usa 1/2. |
| [Taxa ponderada do M-Core](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/BDTaxa.lean), commit de desenvolvimento 690a976, 27/10/2026 às 08:44:08 UTC | Sob SemZeros θ, taxa K·N^(−2δ) para 0<δ<σ−θ | No ponto θ=σ=1/2, o intervalo admissível para δ é vazio. |
| [Bettin–Conrey–Farmer](https://arxiv.org/abs/1211.5191) | Taxa 1/log N com pesos suavizados de Möbius | O teorema usa RH e um momento negativo de ζ′ nos zeros, Σ 1/|ζ′(ρ)|² ≪ T^(3/2−δ). A importação de RH por si só deixaria a hipótese do momento em aberto. |

## Obstrução à passagem informal para a borda

A passagem σ↓1/2 em cotas pontuais fora da reta crítica é insuficiente mesmo num modelo com constante 1. Para N≥2 e h≥0, tome F_N(h)=N^(−2h). Para todo h>0 e 0<δ<h vale F_N(h)≤N^(−2δ). No entanto F_N(0)=1 para todo N. Escolher h=1/log N também deixa F_N(h)=e^(−2), uma constante. A lacuna compreende o encolhimento do expoente e o controle da transferência para a reta crítica.

Separadamente, a sequência decrescente 1/√log(N+2) tende a zero, embora seu produto por log(N+2) seja ilimitado. Logo, monotonicidade e densidade qualitativa também são insuficientes.

## Um enunciado suficiente com todos os quantificadores

Pela fórmula espectral do resíduo, basta construir polinômios de Dirichlet P_N de comprimento N e coeficientes compatíveis com os geradores, e provar sem premissas abertas que, para algum C e N₀ e todo N≥N₀,

```text
(1/2π) ∫_{ℝ} |1 − ζ(1/2+it) P_N(1/2+it)|² /(1/4+t²) dt ≤ C/log(N+2).
```

A convenção do sinal de P_N pode ser absorvida nos coeficientes. A variacionalidade transfere a estimativa a D_N. Para N<N₀, o aproximante zero dá D_N≤1 e K=max(C,log(N₀+2)) completa o majorante. A parte pendente é a estimativa da integral sobre toda a reta, com a mesma constante para todo N≥N₀.

Esta publicação é uma análise das hipóteses e uma prova da insuficiência das passagens acima. Não houve novo build Lean nem importação de uma prova externa do endpoint.
