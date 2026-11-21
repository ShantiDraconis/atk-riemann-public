# Normalização e limite de cada coeficiente modular

Usamos a convenção de R01.multiplierLoss: f_N(j)=1+Σ_{k=2}^N λ_k^(N)(j mod k), M=100N⁵ e Q_N=Σ_{j=1}^M f_N(j)²/[j(j+1)]. Esta dedução em texto dá condições necessárias para uma família candidata.

## Primeira célula

Escreva T_N=Σ_{k=2}^N λ_k^(N). Como 1 mod k=1 para todo k≥2, Q_N≥(1+T_N)²/2. Qualquer família com Q_N→0 satisfaz T_N→−1. A normalização T_N=0 custa pelo menos 1/2 para cada N. Na decomposição por pisos, o termo j T_N cancela exatamente a parte linear dos pisos para qualquer T_N.

## Todas as células fixas

Se Q_N→0, então para cada j fixo, |f_N(j)|≤√[j(j+1)Q_N]→0, a partir de M≥j. Para 2≤m≤N, a diferença entre células consecutivas satisfaz

    f_N(m)−f_N(m−1) = T_N − Σ_{k|m, k≥2} k λ_k^(N).

De fato, o resto aumenta de 1 a cada passo salvo nos múltiplos de k, onde o incremento é 1−k. Logo a soma sobre divisores no lado direito tende a −1 para cada m≥2 fixo. Acrescente o termo de índice 1 com valor 1. As somas sobre todos os divisores passam a tender a 0 para m≥2, e valem 1 em m=1. A inversão finita de Möbius dá, para cada k≥2 fixo,

    lim_{N→∞} k λ_k^(N) = μ(k).

Em particular os coeficientes dos módulos 2, 3, 4 e 6 devem tender a −1/2, −1/3, 0 e 1/6. Esta conclusão admite ajustes dependentes de N. Convergência em cada índice fixo deixa aberta a contribuição conjunta dos índices crescentes.

## Cauda e estatuto

Se |f_N(j)|≤A nos índices J<j≤M, a contribuição da cauda é no máximo A²(1/(J+1)−1/(M+1)). Com A uniforme, J≥log(N+2) assegura O(1/log(N+2)). Para deduzir pequeno-o dessa estimativa basta que J/log(N+2)→∞.

A comparação com o D_N concreto está [demonstrada em texto](../r01-fixed-rational-bridge/README.md). O [endpoint Lean](../r01-rational-spectral-exclusion/ConcreteClosure.lean) recebe a transferência e a cota uniforme como premissas. O [lema anterior de duas células](https://github.com/ShantiDraconis/atk-riemann-public/blob/3b1e613696426be48adc4bc20aeffa74a1c17bc7/research/r01-rational-spectral-exclusion/DualMultipliers.lean) tem auditoria própria. Esta nota não executa um novo build. O alvo quantitativo continua OPEN_MATH.
