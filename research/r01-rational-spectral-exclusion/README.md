# R01 — exclusão racional finita e fechamento global

## Multiplicação cruzada

Para 1/2<σ<1, escreva s=σ+it. Na cota de Mellin, a soma
|1−s|²+(2σ−1) é |s|². Os denominadores são estritamente positivos
na faixa aberta. A cota simplifica para
b(s)=(2σ−1)|1−s|²/|s|⁴.

Escreva σ=p/q, t=a/b, U=u/v com q,b,v>0, e defina
A=p²b²+a²q², B=(q−p)²b²+a²q². Então o teste exato é

    U < b(s)  ⇔  u A² < v(2p−q)B q b².

Isso segue substituindo as frações e usando A>0. A exclusão usa
duas premissas: D_N≤U e ζ(s)=0 → b(s)≤D_N. Se o teste estrito
passa, segue ζ(s)≠0. A equação funcional e a conjugação dão a
exclusão do ponto refletido no interior da faixa. Se o teste
falha, a desigualdade sozinha deixa o ponto sem decisão.

Testei a equivalência em 44.352 casos racionais em Python com
frações exatas. Com U=205843/25000000, σ=7/8 e t=9, o teste passa.
Com t=10 e a mesma σ, a desigualdade estrita falha.

## Compatibilidade da convenção de sinais

Se F=Σ a_k φ_k com a₁=1 e b_k=−a_k/k, a condição de cauda
nula é Σ_{k≥2} b_k=1. Nas células m≥1,

    F(x)=−Σ_{k≥2} b_k(m mod k),
    χ(x)+F(x)=1−Σ_{k≥2} b_k(m mod k).

Fixar a₁=1 é uma normalização adicional. O espaço completo de
cauda nula permite a₁=Σ b_k sem exigir que a soma seja 1.
A equivalência quantitativa com D_N usa o espaço completo.

## Fechamento lógico por regiões

Para inteiro j≥5, considere o retângulo real/imaginário
1/2+1/j≤σ≤1−1/j e |t|≤j. Nessa região,
2σ−1≥2/j, |1−s|²≥1/j² e |s|⁴≤(1+j²)². Logo

    b(s) ≥ 2/[j³(1+j²)²].

Um certificado finito U_N abaixo desse limiar exclui todos os zeros
nesse retângulo e em seu reflexo. A união dos retângulos cobre a
metade direita da faixa aberta. Portanto, provar a existência de
um certificado para cada j é suficiente para a RH no critério da
faixa crítica. A mera definição dos limiares deixa esse fornecimento
de certificados em aberto. A taxa uniforme solicitada pelo R01
implicaria a existência deles.

## Estados ATK e auditoria

O estado sobre/fora da reta é uma classificação geométrica do
zero. O estado zeroSobreZero classifica a avaliação de um par
numerador/denominador. O teste de exclusão usa a cota espectral
e o certificado superior. Nenhum estado operacional substitui
uma dessas premissas.

[Exclusion.lean](Exclusion.lean) contém a multiplicação cruzada
sobre os reais, a classificação e a implicação que exclui um zero
dados o certificado e a premissa de Mellin. O código foi publicado
sem execução de Lean nesta rodada; a auditoria produzida pelo kernel
ainda está pendente. A desigualdade inteira aparece demonstrada
acima e testada em aritmética racional exata.

A referência de desenvolvimento para o teste espectral inclui
[BarreiraZero.lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/BarreiraZero.lean)
e a [ponte direta de Mellin](../r01-mellin-bridge/README.md).
O commit desta nota registra a data desta formulação pública.
O produtor quantitativo permanece OPEN_MATH.
