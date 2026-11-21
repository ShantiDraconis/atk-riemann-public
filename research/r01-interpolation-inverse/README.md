# R01 — inversão da interpolação e obstrução de rigidez

Registro de 21/11/2026. A cota uniforme do R01 permanece OPEN_MATH.

Para N≥2, seja g=Σ_(k≤N) a_k φ_k, com φ_k(x)={1/(kx)}.
A condição de cauda nula é Σ a_k/k=0. Na célula m≥1, o erro é
E_m=1+Σ_(k≤N) a_k floor(m/k). Ponha E_0=0 para esta álgebra.

## Operador inverso

Para 1≤m<N, subtrair células consecutivas dá

    Σ_(k|m) a_k = E_m−E_(m−1)−1_{m=1}.

Por inversão de Möbius, os erros prescritos E_1,...,E_(N−1)
determinam de maneira única os coeficientes:

    a_k = −μ(k) + Σ_(j|k) μ(k/j)(E_j−E_(j−1)),  1≤k<N,
    a_N = −N Σ_(k<N) a_k/k.

Reciprocamente, essas fórmulas realizam os erros prescritos, pois
a convolução de μ com a função constante 1 é a identidade para
convolução de Dirichlet. Assim, é uma bijeção afim entre o espaço de
coeficientes com cauda nula e o vetor de erros das primeiras N−1
células.

Em particular, impor E_j=0 para todo j<N força
a_k=−μ(k) para k<N e a_N=N S_(N−1). O interpolante é exatamente
−B_N da equação (1.18) de Báez–Duarte, *New versions of the
Nyman–Beurling criterion* (2002), e a Proposição 4.13 do artigo
demonstra a divergência em L² da sequência completa B_N.
Portanto, uma família com cauda nula e taxa logarítmica precisa
relaxar a interpolação exata em algum dos primeiros N−1 índices
para infinitos N. A liberdade pode ser parametrizada diretamente
pelo erro celular e balanceada com a energia das células restantes.

## Cronologia verificável

| Publicação em UTC | Escopo |
|---|---|
| 21/11/2026 14:10:06, [c4c7f62](https://github.com/ShantiDraconis/atk-riemann-public/commit/c4c7f62c4252e5d563e30e330856e845f3bf09ff) | Testemunho dual e positividade finita. |
| 21/11/2026 14:15:51, [d0d099a](https://github.com/ShantiDraconis/atk-riemann-public/commit/d0d099a3da49f8a29e047793ea2529261851f2ba) | Integral modular por período, cauda e equações normais. |
| 21/11/2026 14:17:38, [aa7be54](https://github.com/ShantiDraconis/atk-riemann-public/commit/aa7be543f8a25d0af9041649208ff6ea4e0ce162) | Auditoria de possíveis produtores e premissas restantes. |
| 21/11/2026 14:21:37, [e889496](https://github.com/ShantiDraconis/atk-riemann-public/commit/e889496ed472ead5bfd22881235e04b1a990d538) | Identificação com −B_N e referência correta ao resultado de divergência. |

A inversão acima foi demonstrada em texto nesta nota. O artigo
original já descreve a unicidade do interpolante em (1.18).
O registro público deste projeto documenta seu desenvolvimento
e a formulação em termos dos erros prescritos, sem afirmar
prioridade sobre o resultado clássico. A pesquisa não encontrou
um commit que prove o produtor sem premissas. Nenhum novo build
Lean foi executado. [Artigo original](https://doi.org/10.1155/S0161171202013248).
