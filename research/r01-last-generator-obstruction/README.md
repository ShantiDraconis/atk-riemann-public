# R01 — correção no último gerador e obstrução conhecida

Para N≥2, escreva S_N=Σ_{k≤N} μ(k)/k e φ_k(x)={1/(kx)}.
O interpolante com correção no último gerador é

    g_N = −Σ_{k<N} μ(k)φ_k + N S_(N−1)φ_N
        = −Σ_{k≤N} μ(k)φ_k + N S_N φ_N
        = −B_N.

A igualdade intermediária segue de N S_N = N S_(N−1)+μ(N).
B_N é exatamente a sequência definida na equação (1.18) de
[L. Báez–Duarte, New versions of the Nyman–Beurling criterion (2002)](https://doi.org/10.1155/S0161171202013248).
A [cópia do artigo](https://www2.math.ethz.ch/EMIS/journals/HOA/IJMMS/Volume31_7/242719.pdf)
contém a Proposição 4.13, que demonstra que B_N não converge em L².
Portanto não há K global que dê taxa 1/log(N+2) para o erro de g_N.

## Parâmetro visível após a isometria

Na notação do artigo, Uφ_k(x)={kx}/(kx) e Uχ(x)=sin(2πx)/(πx).
Em 0<x<1/N, todos os Uφ_k valem 1. Portanto Ug_N é constante
nesse intervalo, com valor A_N=N S_(N−1)−M(N−1), onde
M(t)=Σ_{k≤t} μ(k). Pela isometria e |Uχ|≤2,

    ||χ−g_N||² ≥ (max(|A_N|−2,0))²/N.

Uma taxa K/log(N+2) para esta família exigiria
|A_N|≤2+sqrt(K N/log(N+2)). A proposição citada descarta a
convergência de toda a sequência, independentemente da RH.

## Experimento

Erro na soma até m=1.000.000, calculado em ponto flutuante.
O limite do restante é analítico, avaliado numericamente.
O primeiro bloco é N≤m<2N.

| N | Primeiro bloco | Soma parcial | Teto do restante |
|---:|---:|---:|---:|
| 16 | 0.01969032 | 0.03717695 | 0.00016827 |
| 32 | 0.01887687 | 0.03920965 | 0.00052935 |
| 64 | 0.02286964 | 0.03628763 | 0.00168288 |
| 128 | 0.02150753 | 0.03966208 | 0.00625251 |
| 256 | 0.01533517 | 0.03667566 | 0.02533341 |

O teto usa |χ−g_N|≤1+Σ_{k<N}|μ(k)|+|N S_(N−1)| e a soma
telescópica dos pesos 1/[m(m+1)]. O erro ótimo D_N pode ser menor.
O parâmetro ainda faltante para o R01 é uma constante uniforme
para outra família de coeficientes, com prova em todos os N.
O gate permanece OPEN_MATH. Nenhum build Lean foi executado.
