# Obstrução para multiplicadores de suporte fixo no R01

Para N ≥ 2, seja Q_N a perda modular truncada em M_N = 100N⁵, com resíduo f_N(j) = 1 + Σ λ_k^(N) (j mod k) e peso 1/[j(j+1)]. Os coeficientes podem variar com N.

**Proposição.** Fixe S ⊂ {2,3,…} finito e não vazio. Se todos os coeficientes fora de S forem nulos, tome P = mmc(S). Em cada múltiplo j = rP todos os restos ativos valem zero. Logo f_N(rP) = 1 e, pela positividade das parcelas,

    Q_N ≥ Σ_{1 ≤ r ≤ M_N/P} 1/[rP(rP+1)].

Em particular, assim que M_N ≥ P, vale Q_N ≥ 1/[P(P+1)]. Para qualquer C ≥ 0, todo N desse regime com log(N+2) > C P(P+1) viola Q_N ≤ C/log(N+2). A prova vale também ao longo de uma subsequência ilimitada de índices com suporte contido no mesmo S. Consequentemente, para uma família com a taxa exigida, o maior índice com coeficiente não nulo tem de tender a infinito (convenciona-se máximo zero para o suporte vazio).

**Caso concreto.** Com os módulos 2 e 3, P = 6. Para todo N ≥ 3, a sexta célula sozinha custa 1/42, mesmo que os dois coeficientes sejam reotimizados a cada N. O mínimo 233/3682 no corte M = 6 continua correto. O prolongamento com apenas esses dois módulos falha como produtor uniforme.

**Controle superior independente.** Na convenção f = 1 − Σ y_k(j mod k), tome y₂ = 1059/1841, y₃ = 851/1841. Os numeradores de 1841 f nas classes j = 1,…,6 são −69, 139, 782, 990, −920, 1841, respectivamente. Logo |f| ≤ 1. A soma exata das primeiras 60 células acrescida do teto telescópico 1/61 para o restante é 3019742143153202358029288417/28072262065425932167949945040, inferior a 0,108. Isso fornece um teto para a perda desta família, juntamente com o piso 1/42. O piso demonstra a falha assintótica.

O resultado diz respeito a famílias com suporte fixo ou recorrentemente limitado. O mínimo L_N otimiza sobre todos os módulos até N. A prova de limitação de L_N log(N+2) e a transferência concreta em Lean continuam pendentes. Demonstração em texto e cálculo racional, sem novo build. [Caso de seis células aceito pelo kernel](2026-11-21-multiple-links.md) · [Decisão da rodada](2026-11-21-minimum-to-endpoint.md).
