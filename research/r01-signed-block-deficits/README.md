# R01 — balanço exato dos déficits em blocos

Registro de 21/11/2026. O produtor incondicional permanece OPEN_MATH.

Sejam N_k=2^(2^k), L_k=log(N_k+2) e Q_k=L_k D_(N_k). Para o ganho
Δ_k=D_(N_k)−D_(N_(k+1)), defina o déficit assinado

```text
e_k = (L_(k+1)−L_k) D_(N_k) − L_(k+1) Δ_k.
```

Então e_k=Q_(k+1)−Q_k. Logo, para todo j≥k₀,

```text
Q_j = Q_(k₀) + Σ_{k=k₀}^{j−1} e_k.
```

A cota uniforme do R01 equivale a haver um teto uniforme para as somas
parciais assinadas. Para a implicação à cota global, se
N_j≤N<N_(j+1), use monotonicidade de D e
L_(j+1)≤2L_j, que segue de N_(j+1)=N_j². Isso dá
D_N log(N+2)≤2Q_j. Os índices iniciais são finitos.
A implicação inversa decorre da cota nos próprios N_j.

Somar apenas as partes positivas é suficiente e pode perder cancelamentos.
Por exemplo, no modelo abstrato Q_j alternando entre 1 e 3/2 a partir
de j=1, D_(N_j)=Q_j/L_j é decrescente, pois L_(j+1)>(3/2)L_j
para N_j≥4. A cota logarítmica vale, mas Σ max(e_j,0) diverge.
Esse modelo ilustra a diferença lógica entre as duas condições.

No problema concreto, substitui-se Δ_k pela energia de projeção do
[bloco de Gram](https://github.com/ShantiDraconis/atk-riemann-public/blob/e797387accbb99301a6cf3ede10e4a332170c56f/research/r01-block-gram-bound/README.md).
A obrigação pendente é estabelecer o teto para as somas assinadas
desses blocos específicos. O resultado acima é uma equivalência
demonstrada em texto e ainda sem build Lean próprio.

## Escala da contração

Se N_k=2^k, uma contração fixa de fator 1/2 força D_(N_k)=O(1/N_k).
Se N_k=2^(2^k), o mesmo fator dá D_(N_k)=O(1/log N_k). Na segunda malha,
a igualdade-modelo D_(N_k)=c/log N_k satisfaz exatamente a redução
pela metade e permanece na escala do piso logarítmico. A compatibilidade
em ordem não fornece uma estimativa do ganho real.

A nota é pública. Os repositórios privados permanecem fechados.
