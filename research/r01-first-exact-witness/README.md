# R01 — testemunho concreto para o primeiro bloco

Registro de 21/11/2026. Demonstração incondicional em texto para o ganho
do primeiro gerador. A taxa uniforme do R01 permanece OPEN_MATH.

No espaço L²((0,∞),dx), escreva χ=1_(0,1] e φ(x)={1/x}. Para
I_m=(1/(m+1),1/m], φ(x)=1/x−m quase sempre. Integração direta dá

```text
∫_(I_m) φ dx   = log((m+1)/m) − 1/(m+1),
∫_(I_m) φ² dx  = 2 − 1/(m+1) − 2m log((m+1)/m).
```

Ao somar até M, a primeira expressão vale log(M+1)−H_(M+1)+1,
com limite 1−γ. A segunda vale

```text
2M + 1 − H_(M+1) − 2M log(M+1) + 2 log(M!).
```

Pelas expansões de Stirling e dos números harmônicos, seu limite é
log(2π)−γ−1. De fato, 2 log(M!)=(2M+1)log M−2M+log(2π)+o(1),
2M log(1+1/M)→2 e H_(M+1)−log M→γ. Na cauda x>1,
φ(x)=1/x, cuja contribuição quadrática é 1. Portanto

```text
⟨χ,φ⟩ = 1−γ
||φ||² = log(2π)−γ
c₁ = (1−γ)/(log(2π)−γ)
D₁ = ||χ−c₁φ||² = 1−(1−γ)²/(log(2π)−γ).
```

A última identidade segue da minimização do quadrático
1−2c⟨χ,φ⟩+c²||φ||². O produto interno é estritamente positivo,
por exemplo na célula (1/2,1), e ||φ||²>0. Logo D₁<1,
numericamente D₁≈0,8582120514. Usar o mesmo aproximante em cada
espaço maior dá D_N≤D₁ para todo N≥1.

Este testemunho materializa um ganho concreto em um estágio.
Para repetir o ganho na escala logarítmica, é necessário controlar
o produto interno com o resíduo projetado de cada bloco novo, como
na [proposta por blocos](https://github.com/ShantiDraconis/atk-riemann-public/blob/85c9d2f753422568cf9aec1e37b8c13ef24c2aa2/research/r01-block-closure-proposal/README.md).
O ganho inicial fornece uma cota constante para D_N. A prova do
decaimento uniforme ainda está pendente. Não houve novo build Lean.
