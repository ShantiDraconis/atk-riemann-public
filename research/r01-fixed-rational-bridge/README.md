# R01 — ponte quantitativa com um único mínimo racional

## Enunciado

Para N≥2, fixe M_N=100N⁵ e defina L_N como o menor erro quadrático
sobre as primeiras M_N células, usando os geradores modulares de
cauda nula r_k(m)=m mod k, 2≤k≤N, e pesos 1/[m(m+1)].
Seja A=log(2π)−γ. Vale incondicionalmente

    L_N ≤ D_N^(0) ≤ L_N + 1/N,
    L_N/A ≤ D_N ≤ L_N + 1/N.

Portanto o alvo quantitativo do R01 equivale a L_N=O(1/log(N+2)).
A matriz é inteiramente racional e o corte é determinado por N.

## Prova

O erro do minimizador truncado é menor ou igual ao erro da
escolha zero, que é menor que 1. Nas primeiras N−1 células,
isso implica |E_j|≤√(j(j+1))≤j+1 e
|E_j−E_(j−1)|≤3j, com E_0=0.

A inversão de Möbius de faa42c0 dá
|a_k|≤1+3Σ_{j|k} j para k<N. Somando por divisores,

    Σ_{k<N}|a_k| ≤ (N−1)+3(N−1)² ≤ 3N²,
    Σ_{k<N}|a_k|/k ≤ (N−1)+3(N−1)Σ_{d≥1}1/d² ≤ 7(N−1).

O último coeficiente é imposto pela cauda nula:
a_N=−NΣ_{k<N}a_k/k. Logo, na parametrização b_k=a_k/k,
a amplitude do erro fica limitada por

    B = 1+Σ_{k=2}^N |b_k|(k−1)
      ≤ 1+3N²+7N(N−1) ≤ 10N².

O erro omitido após M_N células é ≤ B²/(M_N+1) ≤ 1/N.
O limite inferior L_N≤D_N^(0) segue pela truncagem de uma soma
de termos não negativos. O outro lado usa o minimizador truncado
como candidato para a soma inteira. Finalmente, aplique
D_N≤D_N^(0)≤A D_N.

## O elo único e sua composição

- Se o R01 valer com K, então L_N≤A K/log(N+2).
- Se L_N≤C/log(N+2) para todo N≥2, então
  D_N≤(C+1)/log(N+2), pois log(N+2)≤N para N≥2.
  A escolha K=max(C+1,log 3) cobre N=0 e N=1.
- A hipótese material pode ser formulada apenas como
  sup_{N≥2} L_N log(N+2)<∞. O controle da amplitude já foi
  demonstrado e não precisa entrar como hipótese adicional.

Em Lean, a cadeia a auditar é: inversão celular e limite dos
coeficientes → truncagem e estimativa de cauda → equivalência
da cota de L_N com o produtor explícito → DNLimit=0.
O critério de Báez–Duarte fornece separadamente a implicação
qualitativa para riemannZeta. A identidade das rampas e a rota
direta de Mellin têm escopos próprios.

## Evidência e status

- [Inversão celular](../r01-interpolation-inverse/README.md)
- [Certificados racionais bilaterais](../r01-rational-certificates/README.md)
- [Custo de impor cauda nula](../r01-exact-tail-penalty/README.md)
- [Critério qualitativo formalizado](../r01-complete-criterion/README.md)
- [Operadores e passagens entre formulações](../r01-operator-thesis/README.md)

A demonstração acima é em texto. Ainda não foi executada em Lean.
OPEN_MATH permanece verdadeiro para o R01, pois falta a estimativa
uniforme de L_N. CLOSED_MATH para esse alvo exige a prova dessa
estimativa, a composição compilada e a auditoria transitiva de axiomas.
