# R01 — cota suficiente por bloco de Gram

Registro de 21/11/2026. Esta nota demonstra a redução por blocos e fornece uma desigualdade concreta sobre os geradores. A desigualdade para os geradores de Báez–Duarte permanece OPEN_MATH.

## Redução exata

Sejam V_n os espaços gerados pelos primeiros n geradores, P_n suas projeções e r_n=χ−P_nχ, com D_n=||r_n||². Dados m>n, ortogonalize o bloco novo apenas em relação ao espaço antigo: u_k=(I−P_n)φ_k para n<k≤m. Defina A como a matriz de Gram dos u_k e d_k=⟨r_n,u_k⟩. Se o bloco ortogonalizado for independente, A é definida positiva e

```text
D_n − D_m = dᵀ A⁻¹ d.
```

De fato, V_m é a soma ortogonal de V_n e span(u_k). As equações normais para projetar r_n no segundo espaço são A c=d. A norma quadrática da projeção é cᵀAc=dᵀA⁻¹d. Para blocos dependentes, pode-se escolher uma base do span(u_k) e aplicar a mesma fórmula. Um bloco nulo tem ganho zero.

Em termos dos blocos da gramiana original, escreva G_m = [[G_n,B],[Bᵀ,C]] e b_m = [b_n; e]. Quando G_n é invertível, segue diretamente da definição de P_n que

```text
A = C − BᵀG_n⁻¹B,
d = e − BᵀG_n⁻¹b_n.
```

## Critério suficiente em escala logarítmica

Tome n_j=2^(2^j). Se para todo j suficientemente grande o ganho do bloco [n_j+1,n_(j+1)] satisfizer dᵀA⁻¹d ≥ D_(n_j)/2, então D_(n_j)≤2^(−(j−j₀))D_(n_j₀). Como log(n_j)=2^j log 2 e log(n_j+2)≤2 log(n_j) para n_j≥2, a conclusão é uma cota K/log(n_j+2). Para n_j≤N<n_(j+1), use D_N≤D_(n_j) e log(N+2)≤2 log(n_j+2). Os N iniciais ficam cobertos aumentando K.

Uma condição mais forte que pode ser testada diretamente é ||d||²≥λ_max(A)D_(n_j)/2, pois A⁻¹≥I/λ_max(A) na ordem de formas quadráticas. Alternativamente, basta exibir um único vetor c≠0 no bloco tal que

```text
|cᵀd|² ≥ (D_(n_j)/2) (cᵀAc),   cᵀAc > 0.
```

Essa forma segue de projetar r_n apenas na direção Σ c_k u_k. O fator 1/2 constante é uma hipótese suficiente. Ganhos irregulares podem ser tratados pelo [critério acumulado](https://github.com/ShantiDraconis/atk-riemann-public/blob/285874f28534eb8b5dba62817527a5aabafa0b45/research/r01-geometry-gain/README.md).

## Fronteira

A nova desigualdade a demonstrar é uma cota inferior do acoplamento do resíduo concreto com o bloco de novos geradores, em relação à energia desse bloco. Identidades de Gram e positividade isoladas permitem d=0 e por isso são insuficientes para essa estimativa. A redução acima é uma demonstração matemática em texto, ainda sem verificação Lean própria. A cota incondicional, a prioridade sobre uma prova dessa cota e o produtor explicitGramRateTarget_real continuam pendentes.
