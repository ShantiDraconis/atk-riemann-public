# R01 — teste racional com cota de cauda por sinal

Para f(m)=1−Σ_{k=2}^N b_k(m mod k), defina
P=Σ_{b_k>0} b_k(k−1) e Q=Σ_{b_k<0}|b_k|(k−1).
Como 0≤m mod k≤k−1, vale 1−P≤f(m)≤1+Q.
Assim a parte após M células é limitada por
max(|1−P|,1+Q)^2/(M+1). A cota usa a soma telescópica dos pesos.

Para gerar os coeficientes, minimizamos exatamente sobre as M
primeiras células. Com X_{j,k}=j mod k, W_{j,j}=1/[j(j+1)],
resolve-se (XᵀWX)b=XᵀW1 em aritmética racional. Pode-se
multiplicar o sistema pelo m.m.c. de 1 a M+1 para acumular seus
elementos com inteiros, pois j e j+1 são coprimos. O erro parcial
ótimo é M/(M+1)−bᵀ XᵀW1. A ele se soma a cota de cauda acima.

| N | M | Limite inferior para D_N^(0) | Limite superior para D_N^(0) |
|---:|---:|---:|---:|
| 4 | 256 | 0.06503944 | 0.06893051 |
| 4 | 1024 | 0.06572279 | 0.06669842 |
| 8 | 256 | 0.02362371 | 0.03067558 |
| 8 | 1024 | 0.02408852 | 0.02584938 |
| 16 | 256 | 0.01725458 | 0.04159331 |
| 16 | 1024 | 0.01776950 | 0.02369990 |

Os valores são exibidos com margem decimal para fora dos resultados
calculados. Os sistemas e os limites foram calculados em aritmética
racional. D_N^(0) é o erro ótimo com cauda nula. Seu limite superior
também vale para D_N. Para a taxa do R01, basta controlar esse limite
superior com uma única constante para todo N. Esse passo permanece
OPEN_MATH. Não houve compilação Lean neste experimento.
