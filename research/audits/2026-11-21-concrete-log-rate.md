# Auditoria da implicação quantitativa do R01

Revisão pública auditada: [e671d9cdfca608cf0da7690a46a8fb183fdd4142](https://github.com/ShantiDraconis/atk-riemann-public/tree/e671d9cdfca608cf0da7690a46a8fb183fdd4142/research/r01-rational-spectral-exclusion). Execução de integração 44935602810, job 136941404267, concluída com sucesso. O verificador compila ATK.BarreiraZero e os módulos de integração com a revisão ATK fixada em verify.sh.

ConcreteLogRate afirma que existe K ≥ 0 tal que D_N ≤ K/log(N+2) para todo N natural. O teorema concrete_closure_of_log_rate recebe essa proposição como hipótese e conclui dInf = 0 e RiemannHypothesis. A construção incondicional de um termo de ConcreteLogRate permanece em OPEN_MATH.

Saída do kernel com horários UTC:

```text
2026-11-21T18:33:39.7439578Z 'R01.certificates_of_log_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T18:33:39.7440423Z 'R01.concrete_closure_of_log_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
```
