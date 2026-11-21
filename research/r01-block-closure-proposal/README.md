# R01 — proposta de fechamento por um testemunho de bloco

O alvo é a cota incondicional D_N ≤ K/log(N+2) para a família concreta de Báez–Duarte. O estado permanece OPEN_MATH.

## O que construir

Use N_k=2^(2^k), L_k=log(N_k+2) e r_k=χ−P_(V_Nk)χ. Para cada k suficientemente grande, escolha coeficientes reais c_(k,i) para N_k<i≤N_(k+1) e forme

```text
w_k = (I − P_(V_Nk)) Σ_i c_(k,i) φ_i.
```

Defina A_k como a gramiana do bloco projetado, e d_k como o vetor de produtos internos desses geradores projetados com r_k. Para a combinação acima, ponha B_k=c_kᵀ A_k c_k e a_k=c_kᵀ d_k. Logo B_k=||w_k||² e a_k=⟨r_k,w_k⟩.

O lema a provar para a família concreta é que se podem escolher c_k com B_k>0 e erros ε_k≥0 somáveis de modo que, a partir de algum k₀,

```text
a_k²/B_k ≥ D_(N_k)·(1 − L_k/L_(k+1)) − ε_k/L_(k+1).
```

Há uma via suficiente com ε_k=0. Ganhos irregulares também podem ser tratados pelo [critério de déficits assinados](https://github.com/ShantiDraconis/atk-riemann-public/blob/b01ac4e83625d4cdff722f2f52f591232b1fa033/research/r01-signed-block-deficits/README.md). Se o resíduo já chegar a zero, a cauda fica zero e os índices finitos anteriores são cobertos por uma constante.

## Demonstração da implicação

Somar ao aproximante antigo o vetor (a_k/B_k)w_k dá um elemento de V_(N_(k+1)). A expansão exata da norma do erro fornece

```text
||r_k − (a_k/B_k)w_k||² = D_(N_k) − a_k²/B_k.
```

Pela minimalidade, D_(N_(k+1)) é no máximo esse erro. Multiplicando por L_(k+1) e usando a desigualdade do testemunho,

```text
L_(k+1) D_(N_(k+1)) ≤ L_k D_(N_k) + ε_k.
```

Se B = L_k₀ D_(N_k₀)+Σ_(k≥k₀) ε_k, então L_k D_(N_k)≤B. Para N_k≤N<N_(k+1), a monotonicidade de D e L_(k+1)≤2L_k dão D_N log(N+2)≤2B. Para os índices iniciais, D_N≤1. Assim, K=max(2B, log(N_k₀+2)) é uma constante admissível.

## Como avaliar a proposta

- Usar a [decomposição de Gram por blocos](https://github.com/ShantiDraconis/atk-riemann-public/blob/e797387accbb99301a6cf3ede10e4a332170c56f/research/r01-block-gram-bound/README.md) para obter A_k e d_k por complemento de Schur. Uma família explícita c_k permite provar a desigualdade em produtos escalares sem inverter A_k. A escolha ótima c_k=A_k⁻¹d_k pode servir de referência.
- Os testes finitos podem comparar candidatos e limitar a energia e o produto interno nesses blocos. A obrigação que fecha o gate é analítica e vale para todo k≥k₀ com controle uniforme ou somável do erro.
- Depois de demonstrado o lema material, transportar o majorante pelo lema existente `explicitGramRateTarget_iff_uniformLogDNBound` e auditar o produtor sem parâmetros e o certificado de densidade em Lean. As declarações da [branch Claude já auditada](https://github.com/ShantiDraconis/atk-riemann-public/blob/cc848f56029f099a770bddc334fb711a712eb67b/research/r01-claude-branches/README.md) são auxiliares para transporte e simetria. Ainda falta uma estimativa que as conecte a A_k e d_k.

A implicação do testemunho à cota uniforme está demonstrada em texto. A existência de tais testemunhos para os geradores concretos segue em aberto. Não houve novo build Lean.
