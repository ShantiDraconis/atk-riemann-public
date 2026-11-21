# Auditoria da ponte concreta do R01

Em 21 de novembro de 2026, o Lean 4.34.1 compilou os módulos da [revisão pública auditada](https://github.com/ShantiDraconis/atk-riemann-public/tree/f9fb252722b54e79465b955b2261ccbd69bfbdc2/research/r01-rational-spectral-exclusion). O [CI público](https://github.com/ShantiDraconis/atk-riemann-public/actions/runs/44934333607) compilou Closure e Exclusion. A integração compilou ATK.BarreiraZero da revisão fixada no verificador, os dois módulos públicos e ConcreteClosure. O job de integração 136937567114 da execução 44934335671 rodou no repositório de acesso restrito que fornece a dependência ATK.

A declaração final tem a hipótese `ArbitrarilySmallUpperCertificates DN`, isto é, para todo ε > 0 existe N com D_N < ε. O teorema deduz `RiemannHypothesis` dessa hipótese. A existência incondicional dos certificados e a taxa uniforme exigida pelo R01 permanecem em OPEN_MATH.

Saída de `#print axioms` da integração, com timestamps UTC:

```text
2026-11-21T18:18:43.4475424Z 'R01.concrete_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T18:18:43.4491254Z 'R01.concrete_strip_of_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T18:18:43.4494458Z 'R01.concrete_inf_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T18:18:43.4495498Z 'R01.mathlib_rh_of_concrete_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
```
