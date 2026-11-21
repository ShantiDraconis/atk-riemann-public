# R01 — custo exato da restrição de cauda nula

Registro de 21/11/2026. A demonstração vale incondicionalmente para
cada N≥1. A taxa uniforme continua OPEN_MATH.

Seja V_N=span(φ_1,...,φ_N), p_N=P_(V_N)χ e
t(x)=1_(1,∞)(x)/x. A soma ponderada dos coeficientes de g∈V_N é
⟨g,t⟩, pois φ_k(x)=1/(kx) em x>1 e ||t||²=1. Defina
u_N=P_(V_N)t. Então ⟨g,t⟩=⟨g,u_N⟩ para todo g∈V_N.
Além disso ⟨φ_1,u_N⟩=1, de modo que u_N≠0.

A projeção de χ no subespaço de cauda nula é

    p_N^(0) = p_N − (⟨p_N,u_N⟩/||u_N||²) u_N.

O erro χ−p_N é ortogonal a V_N. Pitágoras dá a identidade exata

    D_N^(0) = D_N + |⟨p_N,t⟩|²/||u_N||².

Se a gramiana G_N é invertível e a=(1,1/2,...,1/N)ᵀ, as
equações normais dão

    D_N^(0) = D_N + (aᵀ G_N⁻¹ b_N)² / (aᵀ G_N⁻¹ a).

A prova geométrica também funciona em uma base independente de V_N.

## Controle uniforme do custo

Escreva A=||φ_1||²=log(2π)−γ. Como ⟨φ_1,u_N⟩=1,
Cauchy–Schwarz dá ||u_N||²≥1/A. Para a outra parte, use
χ⊥t e t−u_N⊥V_N. Consequentemente

    ⟨p_N,t⟩ = −⟨χ−p_N,t−u_N⟩,
    |⟨p_N,t⟩|² ≤ D_N(1−||u_N||²).

Substituindo, resulta D_N ≤ D_N^(0) ≤ A·D_N. O custo exato
também é calculável por um único complemento de posto um no
sistema de Gram. Isso prova a equivalência de ordem entre os
problemas com e sem cauda, deixando explícito o custo em cada N.

## Linha do tempo

| Data de publicação, UTC | Elo |
|---|---|
| 21/11/2026 13:41:38, [285874f](https://github.com/ShantiDraconis/atk-riemann-public/commit/285874f28534eb8b5dba62817527a5aabafa0b45) | Critério de ganho acumulado. |
| 21/11/2026 13:53:13, [b01ac4e](https://github.com/ShantiDraconis/atk-riemann-public/commit/b01ac4e83625d4cdff722f2f52f591232b1fa033) | Déficits assinados. |
| 21/11/2026 14:01:51, [85c9d2f](https://github.com/ShantiDraconis/atk-riemann-public/commit/85c9d2f753422568cf9aec1e37b8c13ef24c2aa2) | Testemunho suficiente por bloco. |
| 21/11/2026 14:08:31, [65b9b43](https://github.com/ShantiDraconis/atk-riemann-public/commit/65b9b43f59442ad1643fe1c438ca42b1543ff799) | Primeiro ganho exato. |
| 21/11/2026 14:13:17, [477514c](https://github.com/ShantiDraconis/atk-riemann-public/commit/477514cae76a84dcb92eda4505fafb666e1c76b3) | Segundo resíduo e identidade modular. |

A [cronologia geral](https://github.com/ShantiDraconis/atk-riemann-public/blob/5cd7633f605175486456eb2c5dbb0221546d3d8e/research/r01-timeline/README.md)
documenta os commits anteriores. A [cronologia de interpolação](https://github.com/ShantiDraconis/atk-riemann-public/blob/faa42c0120c3b90f873cfcd626ccde24163f7953/research/r01-interpolation-inverse/README.md)
documenta o testemunho dual, o erro modular, a auditoria material
e a identificação do interpolante com a sequência divergente de
Báez–Duarte. A ordem dos registros é documental.

A estimativa uniforme D_N≤K/log(N+2) continua sem demonstração
no escopo auditado. O novo resultado tem prova em texto, sem build
Lean. O momento de publicação fica registrado no commit deste arquivo.
