# R01 — primeiro cruzamento do limiar de raiz quadrada

Registro de 21/11/2026. O limiar testado é D_N ≤ 1/√N para N≥1,
onde D_N é o erro quadrático ótimo. A norma ótima é d_N=√D_N e
tem outra escala.

## Faixa finita excluída por cotas já registradas

Se V_a⊆V_N, minimizar o mesmo erro sobre V_N dá D_N≤D_a.
Assim, para a≤N≤b, basta U_a² b<1, com U_a uma cota superior
para D_a, para verificar D_N<1/√N no bloco inteiro. As comparações
racionais dos blocos abaixo usam os extremos superiores arredondados
para cima da escada Arb e a fórmula de D_1.

| a | b | U_a |
|---:|---:|---:|
| 1 | 1 | 0.85821206 |
| 2 | 3 | 0.28996458 |
| 4 | 7 | 0.06512887 |
| 8 | 15 | 0.02416143 |
| 16 | 31 | 0.01789403 |
| 32 | 63 | 0.01405195 |
| 64 | 127 | 0.01137605 |
| 128 | 255 | 0.00965855 |
| 256 | 14750 | 0.00823372 |

Todas as comparações U_a² b<1 valem. Por exemplo, 0.00823372 é
205843/25000000, e 14750·205843²<25000000², enquanto em 14751
a mesma comparação falha. Isso indica o fim da cobertura dessa
cota constante. O primeiro cruzamento verdadeiro N_* é ≥14751.
[Escada Arb e contexto](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/imports/final-proof/RIEMANN/ad3011f1/research/r2/DNLimitZeroAttack.md)
· [Certificado de D_256](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/pesquisa/rodada3/certificado_D256/D256_certificado.md).

## Existência de um ponto finito de quebra e o dado que falta

O piso de Burnol dá liminf D_N log N>0. Assim existem c>0 e N_0≥2
com D_N≥c/log N para todo N≥N_0. Como log N≤4N^(1/4), segue que
D_N>1/√N para todo N≥N_0 que também satisfaça N>(4/c)^4.
Logo N_*:=min{N≥1 : D_N>1/√N} existe e é finito. O uso do piso
assintótico prova a existência, mas não identifica um N_0 efetivo
nem o primeiro N_*. Para certificar o primeiro ponto exato, é
preciso uma cota inferior que exceda 1/√N nesse ponto e evidência
que exclua todos os índices anteriores. Um teste que verifica
apenas um cruzamento fornece um limite superior para N_*.

Referência: [piso de Burnol e definição de d_N²](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/77DAE25DB88A44714D7A7B271A072900/S0008439500024085a.pdf/on-the-size-of-an-expression-in-the-nyman-beurling-baez-duarte-criterion-for-the-riemann-hypothesis.pdf).

## Significado das coordenadas

N é a dimensão de truncagem, um inteiro finito. Uma extensão em
degraus D(x)=D_floor(x), x≥1, mantém o mesmo espaço de aproximação
em cada intervalo unitário. A reta crítica s=1/2+it é uma reta
no plano complexo, com coordenadas σ e t. Um parâmetro de
truncagem ou uma etiqueta de valor indeterminado pode ser adicionado
a um modelo, mas requer definição e teoremas próprios para ligar
seus valores aos zeros de ζ.

A quantidade 1/√N é exatamente a norma L² da indicadora de
(0,1/N]. Se um aproximante acerta χ fora desse intervalo,
seu erro só é limitado por essa norma quando a amplitude do
erro dentro dele é uniformemente limitada pela unidade. O
comprimento do intervalo, sozinho, não controla a amplitude.

Registro matemático em texto. Nenhum certificado Arb novo e nenhum
build Lean foram executados. O teto logarítmico do R01 permanece OPEN_MATH.
