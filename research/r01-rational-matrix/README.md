# R01 — matriz de frações e proveniência dos cálculos

Registro de 21/11/2026. Uma fração nesta tabela representa exatamente
o decimal publicado. Valores numéricos arredondados continuam sendo
aproximações de D_N. A coluna das diferenças é subtração dos decimais
registrados e só tem valor de intervalo quando os extremos usados
são cotas na direção apropriada.

| N | Decimal registrado | Fração reduzida | Valor anterior menos o atual | Evidência |
|---:|---:|---|---|---|
| 0 | 1 | `1/1` | — | exato |
| 1 | 0.8582120513955109 | `8582120513955109/10000000000000000` | `1417879486044891/10000000000000000` | decimal da fórmula exata |
| 2 | 0.2899645737422027318112005834160466 | `1449822868711013659056002917080233/5000000000000000000000000000000000` | `2841237388266540840943997082919767/5000000000000000000000000000000000` | decimal exibido na escada Arb |
| 4 | 0.06512886865990024957106136367286124 | `1628221716497506239276534091821531/25000000000000000000000000000000000` | `2810446313528781028001740246789817/12500000000000000000000000000000000` | decimal exibido na escada Arb |
| 8 | 0.02416142158589668502280894301085134 | `1208071079294834251140447150542567/50000000000000000000000000000000000` | `409674470740035645482524206620099/10000000000000000000000000000000000` | decimal exibido na escada Arb |
| 16 | 0.01789402347696943509905506314795876 | `447350586924235877476376578698969/25000000000000000000000000000000000` | `313369905446362496187693993144629/50000000000000000000000000000000000` | decimal exibido na escada Arb |
| 32 | 0.01405194369952985983642504072212329 | `1405194369952985983642504072212329/100000000000000000000000000000000000` | `384207977743957526263002242583547/100000000000000000000000000000000000` | decimal exibido na escada Arb |
| 64 | 0.01137604029967365814705897002932677 | `1137604029967365814705897002932677/100000000000000000000000000000000000` | `66897584996405042234151767319913/25000000000000000000000000000000000` | decimal exibido na escada Arb |
| 128 | 0.009658549278111909910035392571452577 | `9658549278111909910035392571452577/1000000000000000000000000000000000000` | `1717491021561748237023577457874193/1000000000000000000000000000000000000` | decimal exibido na escada Arb |
| 256 | 0.00823371627726102144159803810263543453410463 | `823371627726102144159803810263543453410463/100000000000000000000000000000000000000000000` | `142483300085088846843735446881714246589537/100000000000000000000000000000000000000000000` | extremo superior publicado |
| 7999 | 0.0050692748577823043996341385 | `10138549715564608799268277/2000000000000000000000000000` | `316444141947871704196389960263543453410463/100000000000000000000000000000000000000000000` | double-double |
| 8000 | 0.005069120200107221 | `5069120200107221/1000000000000000000` | `309315350166799268277/2000000000000000000000000000` | double |

## Onde estão os cálculos de origem

- [D_1, integração por células e projeção](https://github.com/ShantiDraconis/atk-riemann-public/blob/65b9b43f59442ad1643fe1c438ca42b1543ff799/research/r01-first-exact-witness/README.md).
- [D_2, paridade e projeção ortogonal](https://github.com/ShantiDraconis/atk-riemann-public/blob/477514cae76a84dcb92eda4505fafb666e1c76b3/research/r01-second-exact-witness/README.md).
- [Escada Arb de N=2 até N=256](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/imports/final-proof/RIEMANN/ad3011f1/research/r2/DNLimitZeroAttack.md).
- [Certificado intervalar de D_256](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/pesquisa/rodada3/certificado_D256/D256_certificado.md).
- [Dados de D_7999 e D_8000](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/pesquisa/rodada4/dados/certifica_texto.json).
- [Experimento racional com cauda nula](https://github.com/ShantiDraconis/atk-riemann-public/blob/cf291fdd0d4fa5f6d8d18b1c99778d1bccb904dd/research/r01-rational-certificates/signed-tail-experiment.md).

As fórmulas de D_1 e D_2 envolvem logaritmos e a constante de
Euler–Mascheroni. A identidade exata para D_1 é
1−(1−γ)²/(log(2π)−γ). A fração na tabela é sua aproximação
decimal convertida, sem alegação de racionalidade do valor verdadeiro.

## Subtrações úteis e cotas

- Teto registrado U para D_256: `823371627726102144159803810263543453410463/100000000000000000000000000000000000000000000`.
- A cota abreviada 0,00823372 é `1029215/125000000`
  (equivalentemente, `205843/25000000`). A folga sobre U é exatamente
  `372273897855840196189736456546589537/100000000000000000000000000000000000000000000`.
- Os dois extremos decimais exibidos no relatório de D_256 diferem
  por 10^(−44). A largura interna de aproximadamente 5,7·10^(−47)
  reportada pelo cálculo intervalar refere-se ao intervalo antes da
  apresentação decimal.
- O valor registrado em double para D_8000 é `5069120200107221/1000000000000000000`. A diferença
  U menos esse decimal é
  `316459607715380044159803810263543453410463/100000000000000000000000000000000000000000000`.
  Isso mede a melhoria candidata em relação ao certificado de N=256.
- Em N=16, o intervalo rational com cauda nula exibido é
  [177695/10000000, 236999/10000000], de largura `7413/1250000`.
  O teto racional menos o decimal Arb do problema completo é
  `145146913075764122523623421301031/25000000000000000000000000000000000`.
  Os dois problemas variacionais têm espaços distintos.
- Por monotonicidade, 0≤D_∞≤D_N≤U para todo N≥256.
  Para 256≤N≤8000, D_N log(N+2)≤U log(8002)≈0,07400008692.
  Em N=1, qualquer K global satisfaz exatamente
  K≥[1−(1−γ)²/(log(2π)−γ)] log 3≈0,94284230595.

## Como apertar o teto rigoroso

Para certificar um teto em N=8000, basta obter um vetor racional c
de comprimento N e avaliar com arredondamento dirigido
Q(c)=1−2cᵀb_N+cᵀG_Nc. O extremo superior de Q(c) é um teto para D_N
por minimalidade, independentemente de c ser ótimo. O
[verificador por coeficientes usado em N=256](https://github.com/ShantiDraconis/M-Core/blob/c2f4d2eeba16f6393482c033a246760093b4c05d/pesquisa/rodada3/certificado_D256/verifica_coef.py)
documenta essa rota. Nenhum novo certificado de N=8000 foi executado
nesta publicação.

Esta nota registra a data da comparação e as fontes existentes.
A cota uniforme para todos os índices continua OPEN_MATH.
