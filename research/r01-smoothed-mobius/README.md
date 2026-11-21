# R01 — pesos suavizados de Möbius

Experimento de 2026-11-21. O R01 permanece `OPEN_MATH`.

## Fórmula demonstrada

Para N ≥ 2, defina a_k = −μ(k)(1 − log(k)/log(N)) e A = Σ_{k≤N} a_k/k.
Em x > 1, o aproximante g_N = Σ a_k{1/(kx)} é A/x, com contribuição
A² à norma quadrática. Em (1/(m+1),1/m], o erro é constante e vale
E(m) = 1 − mA + Σ a_k floor(m/k). Assim,

```text
||χ − g_N||² = A² + Σ_{m≥1} |E(m)|² / [m(m+1)].
```

A soma omitida após M células é no máximo
(1 + Σ|a_k|)²/(M+1), pela cota unitária para a parte fracionária e
pela soma telescópica dos comprimentos. A minimalidade dá
D_N ≤ ||χ − g_N||². A fórmula e a margem de truncamento são analíticas.
Os valores do script usam ponto flutuante, sem aritmética intervalar.

A condição A=0 é opcional para o espaço de aproximação considerado.
O termo A² está incluído nos resultados. Uma taxa O(1/log(N+2)) para
esta família bastaria para produzir o majorante do R01.

## Datas e proveniência

- 2012-11-22 — submissão em arXiv do trabalho de Bettin, Conrey e Farmer
  com estes pesos e uma taxa sob a RH e uma hipótese adicional sobre
  os valores de ζ′ nos zeros. [Preprint](https://arxiv.org/abs/1211.5191)
- 2026-10-07 — snapshot dos lemas Lean do R01, commit
  `c114452706e06317fbb46a46eda14747cfc0cf2d`.
  O certificado registra a verificação em 2026-11-10.
  [Certificado](https://github.com/ShantiDraconis/atk-riemann-public/blob/658ed8c3c8061b31d0675421d11baf6dd1f20ae6/mvei/branches/m-core-riemann/atk_terminal-parameter-law-20261003/certificate.json)
- 2026-11-21 13:00:35 UTC — commit público da ponte direta de Mellin.
  [Commit](https://github.com/ShantiDraconis/atk-riemann-public/commit/d0715064c9813cc4a240d18446e6b442e9b849e3)
- 2026-11-21 13:03:41 UTC — commit do índice público de cinco lemas.
  [Commit](https://github.com/ShantiDraconis/atk-riemann-public/commit/658ed8c3c8061b31d0675421d11baf6dd1f20ae6)

As datas registram ocorrências documentadas. Data de concepção anterior
à primeira evidência disponível permanece indeterminada.

## Execução

Use Python 3 com NumPy e SymPy.

```sh
python3 check_smoothed_mobius.py
```

Saída para um milhão de células por N:

```text
N       sum(a/k)       partial error    omitted upper bound
 16  -0.360106001      0.314198408        0.000023777
 32  -0.288547772      0.204954197        0.000050054
 64  -0.240514626      0.144314918        0.000119087
128  -0.205987603      0.106956375        0.000312580
256  -0.180450434      0.083545791        0.000884651
```

A cota uniforme incondicional para todos os N e a formalização Lean da
ponte direta permanecem pendentes. O experimento verifica valores finitos.
