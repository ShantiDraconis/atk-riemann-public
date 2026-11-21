# R01 — cálculo exato do segundo resíduo pela paridade

Demonstração incondicional em texto, registrada em 21/11/2026. O
resultado fecha D₂ e dá uma cota constante para todos os índices
posteriores. A taxa uniforme do R01 continua OPEN_MATH.

Escreva φ_k(x)={1/(kx)} e χ=1_(0,1]. Para cada inteiro k≥2,
a identidade das partes inteiras dá

    k φ_k(x) − φ_1(x) = floor(1/x) mod k.

De fato, com t=1/x, a diferença é floor(t)−k floor(t/k);
floor(t/k)=floor(floor(t)/k). Para k=2, e=2φ₂−φ₁ é a indicadora
das células I_m=(1/(m+1),1/m] com m ímpar. Ela vale zero para x>1.
Logo ⟨χ,e⟩=||e||²=Σ_{j≥1}1/[(2j−1)2j]=log 2.

## Produto cruzado e projeção

Em I_(2j−1), a integral de φ₁ é
log(2j/(2j−1))−1/(2j). Portanto

    Σ_{j=1}^M ∫_(I_(2j−1)) φ₁
      = log( 4^M (M!)² / (2M)! ) − H_M/2
      → (log π − γ)/2.

O limite segue de Stirling e H_M−log M→γ. Escreva

    L = log 2, B = (log π−γ)/2,
    A = log(2π)−γ, J = 1−γ.

Os valores A=||φ₁||² e J=⟨χ,φ₁⟩ seguem do
[primeiro testemunho](https://github.com/ShantiDraconis/atk-riemann-public/blob/65b9b43f59442ad1643fe1c438ca42b1543ff799/research/r01-first-exact-witness/README.md).
A família {e, φ₁} gera V₂. Ortogonalize φ₁ por v=φ₁−(B/L)e.
Como v(x)=1/x para x>1, ||v||²=A−B²/L>0. A projeção de χ em e
é e, e a projeção em v tem coeficiente (J−B)/(A−B²/L). Portanto

    P_(V₂)χ = e + [(J−B)/(A−B²/L)] v,
    D₂ = 1−L−(J−B)²/(A−B²/L) ≈ 0,289964573742.

Em particular D_N≤D₂≤1−log 2 para N≥2, pela inclusão dos espaços.
A indicadora e sozinha já fornece a cota 1−log 2.

## Ponte para índices gerais

O espaço V_N é gerado por φ₁ e pelos resíduos da divisão de
floor(1/x) pelos inteiros k=2,...,N. As funções de resíduo somem em
x>1, de modo que permitem construir aproximantes com cauda nula
usando apenas diferenças entre geradores. O caso k=2 admite cálculo
exato acima. Para fechar o R01 ainda é necessário demonstrar, para
uma família de combinações desses resíduos ou dos geradores originais,
que o erro quadrático decai uniformemente como 1/log(N+2).
A identidade modular fornece uma representação para esse ataque.
Nenhum build Lean foi executado para esta nota.
