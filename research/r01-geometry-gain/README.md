# R01 — comparação de geometrias e critério exato de ganho

## Resultados mais próximos localizados

| Geometria | Evidência | Distância até o R01 |
|---|---|---|
| Gram e coeficientes finitos | O resíduo ótimo é D_N = 1 − b_Nᵀ G_N⁻¹ b_N. Por minimalidade, qualquer família de coeficientes com taxa logarítmica fornece a do ótimo. | Falta a cota uniforme para alguma família concreta ou para o ótimo. |
| Hilbert e ganhos sucessivos | [LeisDeGanho.lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/LeisDeGanho.lean), commit de desenvolvimento a91190f. A lei logarítmica por passo implica densidade; sob PisoLog, uma lei com constante c>1 é incompatível com o piso. | A hipótese de ganho permanece sem prova. Um ganho por passo com c=1 é suficiente para a taxa, conforme a demonstração abaixo. |
| Mellin na reta crítica | A expressão integral do erro dá a mesma norma quadrática. | Falta um majorante na linha 1/2 com constante uniforme. |
| Mellin ponderado fora da reta | [BDTaxa.lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/BDTaxa.lean) fornece taxa em potência sob SemZeros θ e 0<δ<σ−θ. | O expoente admissível desaparece no ponto θ=σ=1/2. |
| Piso de Burnol na classe restrita | [BDBurnolL1.lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/BDBurnolL1.lean), commit f1717be. A classe com norma ℓ¹ dos coeficientes ≤N^A tem piso de ordem logarítmica. | Um piso controla a distância por baixo. A cota superior ainda é necessária. |
| Parametrizações geométricas | Uma geometria que produz coeficientes alimenta a mesma norma do resíduo. Uma mudança unitária preserva a distância ao subespaço. | A parametrização deve produzir uma desigualdade nova para esses coeficientes. |

## Demonstração do critério de ganho acumulado

Seja V_N o espaço dos N primeiros geradores e r_N=χ−P_{V_N}χ. Para o próximo gerador φ, ponha u_N=φ−P_{V_N}φ. Se u_N≠0, então V_(N+1)=V_N⊕span(u_N). Pela identidade de Pitágoras,

```text
D_N − D_(N+1) = |⟨r_N,u_N⟩|²/||u_N||².
```

Se u_N=0, o ganho é zero. Se D_N chega a zero, todos os resíduos posteriores são zero e uma constante finita cobre os índices anteriores. Caso contrário, defina η_N=(D_N−D_(N+1))/D_N, com 0≤η_N<1. Para N≥N₀, iterar D_(j+1)=(1−η_j)D_j dá

```text
−log(D_N/D_N₀)=Σ_{j=N₀}^{N−1} −log(1−η_j).
```

Assim, a taxa do R01 equivale a existir C tal que, para todo N≥N₀,

```text
Σ_{j=N₀}^{N−1} −log(1−η_j) ≥ log log(N+2) − C.
```

A equivalência segue ao exponenciar. Os índices finitos iniciais podem ser cobertos aumentando K. Essa forma permite grandes variações dos ganhos individuais.

Uma condição suficiente mais forte é η_j ≥ 1/((j+2)log(j+2)) a partir de N₀. Com −log(1−η)≥η e a comparação da soma com a integral da função decrescente 1/(x log x), obtém-se

```text
D_N ≤ D_N₀·log(N₀+2)/log(N+2).
```

A condição acumulada é o alvo exato. Ela ainda precisa ser demonstrada para os geradores concretos. O critério acima foi demonstrado em texto. O gate quantitativo permanece OPEN_MATH.

## Cobertura

A busca examinou mensagens de commits e módulos selecionados de Gram, coeficientes, erro ponderado, piso e ganho entre as branches já enumeradas. Esta rodada amplia a comparação matemática, com inspeção seletiva de conteúdo. Nenhum novo build foi executado. A publicação vincula fontes já públicas e mantém os repositórios privados fechados.
