# Testemunho dual de Möbius para o erro finito de Báez–Duarte

Demonstração em texto de 21/11/2026. Para N≥1, escreva φ_k(x)={1/(kx)},
g=Σ_{k≤N} a_k φ_k e A=Σ_{k≤N} a_k/k. Nas células
I_m=(1/(m+1),1/m], o erro χ−g assume o valor

    E_m = 1 − mA + F_m,
    F_m = Σ_{k≤N} a_k floor(m/k).

Ponhamos E_0=F_0=0 para a álgebra discreta. Para 1≤j≤N, seja

    h_j = (1/j) Σ_{d≤N/j} μ(d)/d,     h_(N+1)=0.

Como F_j−F_(j−1)=Σ_{k|j} a_k, a inversão de Möbius dá
A=Σ_{j≤N} h_j(F_j−F_(j−1)). Além disso, Σ h_j=1, pois ao agrupar
jd=k vira Σ_{k≤N}(1/k)Σ_{d|k}μ(d). Substituindo F_j−F_(j−1)
por E_j−E_(j−1)+A−1_{j=1}, segue a identidade exata

    Σ_{j≤N} (h_j−h_(j+1)) E_j = h_1 = Σ_{d≤N} μ(d)/d.

Ela vale para todos os coeficientes reais a_k. Equivalentemente,
a função que em I_j vale j(j+1)(h_j−h_(j+1)) para j≤N e vale
zero fora dessas células anula cada gerador φ_k com k≤N.
Seu produto interno com χ é h_1. Aplicando Cauchy–Schwarz e tomando
o ínfimo sobre os coeficientes, obtemos

    D_N ≥ |Σ_{d≤N} μ(d)/d|² /
          Σ_{j=1}^N j(j+1)|h_j−h_(j+1)|².

O denominador é positivo porque h_N=1/N. O numerador é não nulo:
para N≥2, escolha um primo N/2<p≤N pelo postulado de Bertrand
(com N=2 e N=3 imediatos). Ao multiplicar a soma por
lcm(1,...,N), todos os termos exceto d=p são múltiplos de p.
O termo d=p é não nulo módulo p. Para N=1, a soma vale 1.

Isso demonstra D_N>0 para cada estágio finito e justifica definir
η_N=(D_N−D_(N+1))/D_N sem um caso degenerado para essa família.
O argumento dá uma cota inferior finita. A cota superior uniforme
D_N ≤ K/log(N+2) continua OPEN_MATH. A identidade ainda aguarda
formalização e compilação em Lean.
