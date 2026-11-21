# R01 — certificados racionais de duas faces e estado do kernel

## O que o kernel já aceitou

| Snapshot | Resultado registrado no MVEI |
|---|---|
| [Terminal parameter, c114452](https://github.com/ShantiDraconis/atk-riemann-public/blob/84db032c93e85fdd512d2b1645612c9fa563fe02/mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json) | Aceitos: DN_le_coefficient_error_sq, finiteSpanApproximatesChi_iff_DNLimit_eq_zero, logMajorant_tendsto_zero e FINAL_ROOT_of_logMajorant. O último usa o majorante como hipótese. |
| [Terminal parameter, c114452](https://github.com/ShantiDraconis/atk-riemann-public/blob/84db032c93e85fdd512d2b1645612c9fa563fe02/mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json) | Nesse snapshot, explicitGramRateTarget_iff_uniformLogDNBound consta como aberto-sorry e concreteDN_eq_explicitGramResidual como não alcançado. Esses estados referem-se à revisão certificada. |
| [Material recovery, fb84817](https://github.com/ShantiDraconis/atk-riemann-public/blob/84db032c93e85fdd512d2b1645612c9fa563fe02/mvei/branches/m-core-riemann/atk_rh-material-recovery-20261007/certificate.json) | recoveredAllNRate_iff_explicitGramRateTarget consta como não alcançado. |
| [Log majorant split, 4804a6e](https://github.com/ShantiDraconis/atk-riemann-public/blob/84db032c93e85fdd512d2b1645612c9fa563fe02/mvei/branches/m-core-riemann/atk_rh-log-majorant-split-20261001/certificate.json) | logMajorant_add consta como fechado. |

Os certificados referem-se à verificação de 10/11/2026 às 04:38:10 UTC.
A [auditoria BCF](https://github.com/ShantiDraconis/atk-riemann-public/blob/aa7be543f8a25d0af9041649208ff6ea4e0ce162/research/r01-material-branch-audit/README.md)
mostra como as três cotas alimentariam o majorante. Ela não contém uma
prova incondicional dessas cotas.

## Nova ponte demonstrada em texto

Fixe N≥2 e escreva E_N(b) para o erro quadrático do aproximante modular
de cauda nula. Para M≥N−1, minimize apenas a soma sobre as primeiras M
células e chame o mínimo de L_(N,M). Denote os coeficientes ótimos do
problema truncado por b_(N,M). Todos os dados são racionais. A matriz
cujas colunas são m mod k, 2≤k≤N, tem posto N−1 já nas primeiras N−1
linhas, pela [inversão da interpolação com cauda nula](https://github.com/ShantiDraconis/atk-riemann-public/blob/faa42c0120c3b90f873cfcd626ccde24163f7953/research/r01-interpolation-inverse/README.md).
Logo as equações normais racionais têm solução única.
Defina B_(N,M)=1+Σ_{k=2}^N |b_(N,M,k)|(k−1). Então

```text
L_(N,M) ≤ D_N^(0) ≤ L_(N,M) + B_(N,M)^2/(M+1).
```

A desigualdade inferior segue porque cada erro truncado é no máximo
o erro completo. A superior vem de testar b_(N,M) no problema
completo, majorar a amplitude por B_(N,M) e somar a cauda telescópica.

Para cada N fixo, os coeficientes b_(N,M) são uniformemente limitados
em M. Com efeito, o erro parcial de b_(N,M) é no máximo o erro da
escolha b=0, que é no máximo 1. Seu erro nas primeiras N−1 células
também é no máximo 1. Como a matriz quadrada dessas células é
invertível e todos os pesos são positivos, essa restrição é um
elipsoide limitado em b. Assim, a largura do intervalo acima tende
a zero quando M→∞, com N fixo. Como L_(N,M) é não decrescente em M,
L_(N,M) converge para D_N^(0).

A mesma estimativa fornece um intervalo para o resíduo sem restrição.
Com A=log(2π)−γ e D_N≤D_N^(0)≤A D_N,

```text
L_(N,M)/A ≤ D_N ≤ L_(N,M) + B_(N,M)^2/(M+1).
```

Para obter o R01, basta demonstrar que uma escolha M=M(N) e um K
uniforme satisfazem
L_(N,M(N)) + B_(N,M(N))²/(M(N)+1) ≤ K/log(N+2).
A prova acima garante precisão para cada N, mas não fornece essa
estimativa em N variável. Esse é o elo que permanece OPEN_MATH.

A ponte é uma demonstração matemática em texto. Nenhum novo build
Lean foi executado. Os links identificam fontes já públicas.
