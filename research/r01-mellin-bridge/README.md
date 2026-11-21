# Obstrução direta à densidade por um zero de zeta

Considere o espaço real L²((0,∞), dx), o alvo χ = 1_(0,1] e os geradores
r_k(x) = {1/(kx)}, com k ≥ 1. Seja D_N o quadrado da distância de χ
ao span dos primeiros N geradores. O argumento abaixo prova que D_N → 0
implica a Hipótese de Riemann para essa família. O majorante logarítmico
uniforme de D_N permanece um problema em aberto neste trabalho.

## Funcional contínuo

Para s = σ + it com 1/2 < σ < 1, defina

```text
q_s(x) = x^(s−1)                  para 0 < x ≤ 1
q_s(x) = 1 / ((1−s) x)            para x > 1

L_s(f) = integral de f(x) q_s(x) dx
||q_s||² = 1/(2σ−1) + 1/|1−s|²
```

Cauchy–Schwarz dá |L_s(f)| ≤ ||q_s|| ||f||. O funcional é
real-linear e tem valores complexos. Em particular, L_s(χ)=1/s.

Para x>1, r_k(x)=1/(kx). Assim, a substituição de x^(s−1) por q_s(x)
preserva a integral contra cada gerador na cauda, pois ambas dão
1/[k(1−s)]. Portanto L_s(r_k) é exatamente a transformada de Mellin
do gerador na faixa.

Por mudança de variável u=1/(kx), essa transformada é
k^(−s) ∫₀^∞ {u}u^(−s−1) du = −k^(−s)ζ(s)/s.
Para conferir a última identidade, inicialmente para Re(s)>1,
integre floor(u)u^(−s−1) em [1,∞) somando os degraus
1_[n,∞)(u). Isso dá ζ(s)/s e, ao escrever floor(u)=u−{u},
resulta em ζ(s)/s = 1/(s−1) − ∫₁^∞ {u}u^(−s−1) du.
A integral da direita é holomorfa para Re(s)>0.
Na faixa 0<Re(s)<1, a integral em (0,1) de {u}u^(−s−1)
vale 1/(1−s). A identidade segue por continuação analítica.

## Limite inferior uniforme

Se ζ(s)=0 no semiplano direito da faixa, L_s anula todos os geradores.
Para todo aproximante g no span finito, Cauchy–Schwarz implica

```text
1/|s| = |L_s(χ−g)| ≤ ||q_s|| ||χ−g||,

D_N ≥ 1 / ( |s|² (1/(2σ−1) + 1/|1−s|²) ) > 0.
```

Logo D_N → 0 exclui zeros com 1/2<Re(s)<1. A equação funcional
reflete qualquer zero com 0<Re(s)<1/2 para a metade direita da faixa.
Assim, a densidade implica a RH. O argumento usa o funcional no espaço
físico diretamente e dispensa a reprodução espectral de Cauchy.

## Verificação reproduzível

Execute `python3 check_mellin_bridge.py` com mpmath instalado.
O script compara a integral discretizada com a fórmula de Mellin e
verifica a substituição na cauda. A margem de truncamento em x pequeno
é limitada por (1/(M+1))^σ/σ. A aritmética em ponto flutuante faz deste
teste uma verificação numérica, sem certificação por intervalos.
A prova acima está em texto matemático e ainda não foi formalizada em Lean.

Referência para o contexto do critério de densidade:
[L. Báez-Duarte, A strengthening of the Nyman–Beurling criterion](https://arxiv.org/abs/math/0202141).
