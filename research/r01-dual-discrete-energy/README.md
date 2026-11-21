# R01 por uma desigualdade de energia discreta

## Resultado finito

Fixe N ≥ 2 e M ≥ N−1. Denote por L(N,M) o mínimo de
Σ_{m=1}^M w_m (1−Σ_{k=2}^N b_k (m mod k))², com w_m=1/[m(m+1)].
Para um vetor real F de comprimento M+1 com F_{M+1}=0, defina

    E(F) = Σ_{m=1}^M m(m+1)(F_m−F_{m+1})².

Imponha os vínculos lineares

    Σ_{m=1}^M F_m = k Σ_{j=1}^{⌊M/k⌋} F_{kj},    2 ≤ k ≤ N.

Então L(N,M) é a menor constante H ≥ 0 tal que F_1² ≤ H E(F)
para todo F que satisfaça esses vínculos. A identidade vale também
quando L(N,M)=0.

## Demonstração

Escreva X_{mk}=m mod k, W=diag(w_m), e escolha um minimizador b.
Ele existe por projeção sobre a imagem de X em dimensão finita.
O resíduo r=1−Xb satisfaz XᵀWr=0 e rᵀWr=L(N,M).
Para todo z com Xᵀz=0, vale Σ z_m=rᵀz. Cauchy–Schwarz dá

    (Σ z_m)² ≤ L(N,M) Σ z_m²/w_m.

Se L(N,M)>0, z=Wr realiza a igualdade e tem energia positiva,
pois Σ z_m=L(N,M). Se L(N,M)=0, a soma de z é zero para todo vetor admissível.
Em ambos os casos a constante é ótima.

A mudança inversível F_m=Σ_{i=m}^M z_i dá z_m=F_m−F_{m+1}.
Para x_m=m mod k e x_0=0, somação por partes fornece

    Σ x_m z_m = Σ (x_m−x_{m−1}) F_m
               = Σ F_m − k Σ_j F_{kj}.

Isso prova a identidade e identifica a energia, incluindo o termo de borda em m=M.

## Proposta de fechamento quantitativo

Adote M=100N⁵ e a comparação já demonstrada em texto na
[redução racional](https://github.com/ShantiDraconis/atk-riemann-public/commit/cc7c4edf1ca7f686df198cf47431de03e9b25223).
A estimativa aritmética a provar é: existe c>0 independente de N tal que
para todo N≥2 e todo F admissível com F₁=1,

    E(F) ≥ c log(N+2).

Por homogeneidade e pelo resultado finito, isso equivale a
L(N,M) ≤ 1/[c log(N+2)]. O sanduíche D_N ≤ L(N,M)+1/N e log(N+2)≤N
dão a constante global K=max(log 3,1+1/c), incluindo N=0,1 por D_N≤1.
Na direção inversa, L(N,M)≤(log(2π)−γ)D_N transfere qualquer cota R01
para a desigualdade de energia. A existência de c permanece aberta.

Um cálculo delimita o papel dos vínculos. A condição F₁=1 sozinha
permite energia (M+1)/M: tome F_m=(1/m−1/(M+1))/(1−1/(M+1)).
Logo o crescimento logarítmico precisa vir das igualdades nas classes
de múltiplos. Um caminho de investigação é decompor os incrementos
de F em intervalos diádicos e usar esses vínculos para obter uma
contribuição total proporcional a log N. Exigir uma contribuição
positiva em cada intervalo seria uma hipótese adicional.

## Controle de sinais em frações exatas

Para N=2, M=4, o minimizador é b₂=1 e L=13/60. Os valores de F
obtidos de z=Wr são (13/60,13/60,1/20,1/20,0). A energia é 13/60
e F₁²/E=13/60. Este exemplo testa índices e pesos com um corte curto.

A prova da identidade dual é matemática escrita. Este arquivo não
contém um certificado Lean para a identidade nem para a desigualdade
uniforme. O alvo quantitativo mantém o estado OPEN_MATH.
