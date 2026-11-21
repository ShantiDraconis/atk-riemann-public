# R01 — integral exata do erro modular por período

Para N≥2, seja L=lcm(2,...,N), f(m)=1−Σ_(k=2)^N b_k(m mod k)
e E_N(b)=Σ_(m≥1) |f(m)|²/[m(m+1)]. Esta é a norma quadrática
de um aproximante com cauda nula. O objetivo permanece encontrar
coeficientes com E_N(b)≤K/log(N+2), uniformemente em N.

## Lei exata

Como f é L-periódica, a divisão m=qL+r, q≥0, 1≤r≤L, dá

    E_N(b) = Σ_(r=1)^L |f(r)|² W_L(r),
    W_L(r) = ∫₀¹ t^(r−1)/(1+t+...+t^(L−1)) dt.

De fato, 1/[m(m+1)]=∫₀¹ t^(m−1)(1−t)dt. As parcelas são
não negativas, então a troca de soma e integral é válida por
convergência monótona. A série geométrica em q soma a 1/(1−t^L).
Cancelando 1−t resulta a fórmula. Em particular Σ W_L(r)=1.

Há uma obstrução pontual que os coeficientes não podem cancelar:
f(L)=1, porque L mod k=0 para todos os k. Sua contribuição é
W_L(L)>0. Isso fornece um piso finito, não um teto assintótico.

## Uma cota certificável por truncamento

Para qualquer corte M≥1, ponha
B=1+Σ_(k=2)^N |b_k|(k−1). Então |f(m)|≤B, e

    0 ≤ E_N(b) − Σ_(m=1)^M |f(m)|²/[m(m+1)] ≤ B²/(M+1).

Isso segue por soma telescópica de 1/[m(m+1)]. Desta forma,
para cada N, basta um certificado finito em duas partes: um
erro parcial pequeno e controle do tamanho dos coeficientes.
Uma família com erro parcial ≤C/log(N+2) e
M+1≥B²log(N+2)/C daria E_N(b)≤2C/log(N+2).
O limiar de corte sozinho não entrega o erro parcial.

## Derivadas de otimização

Se X_(r,k)=r mod k, W=diag(W_L(r)) e 1 denota o vetor constante,

    E_N(b) = (1−Xb)ᵀ W (1−Xb),
    ∇E_N(b) = 2XᵀW(Xb−1),
    ∇²E_N(b) = 2XᵀWX.

Logo basta resolver as equações normais XᵀWX b=XᵀW1 para obter
um minimizador. As equações caracterizam o ótimo de cada N;
a taxa do ótimo com N variável exige uma estimativa adicional.

Esta publicação demonstra a integral, o truncamento e as
derivadas em texto. Ainda falta a família uniforme de
coeficientes e a verificação Lean. O R01 permanece OPEN_MATH.
