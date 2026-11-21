# Vínculos nos múltiplos e energia modular

[Revisão Lean](https://github.com/ShantiDraconis/atk-riemann-public/blob/d236382084e40f23e7278f34f07d207389c5abcc/research/r01-rational-spectral-exclusion/DualMultipliers.lean) e [execução pública](https://github.com/ShantiDraconis/atk-riemann-public/actions/runs/44940232271).

- Verificado: telescopagem com os dois termos de fronteira; troca das somas sobre os múltiplos; identidade da diferença com o momento j mod k; cota de energia diretamente dos vínculos sobre F quando F₁=1 e F_{M+1}=0.
- Verificado: para N=3, M=6, o mínimo da perda truncada é 233/3682 em (y₂,y₃)=(1059/1841,851/1841), na convenção de resíduos 1−Σyₖ(j mod k). Na fatia y₃=0, os pesos pares somam 101/420.
- [Endpoint condicional auditado](2026-11-21-modular-multipliers.md): para M=100N⁵, recebe a comparação entre DN e a perda finita acrescida de 1/N, além da cota uniforme para a perda. A primeira ainda requer a formalização do sanduíche no ATK concreto e a segunda exige uma estimativa analítica independente de RH. OPEN_MATH continua ativo para o produtor sem parâmetros.

Saídas de axiomas do novo módulo, UTC:

```text
2026-11-21T19:20:27.0723469Z 'R01.sum_cell_increments' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:20:27.0724070Z 'R01.sum_multiple_tails' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:20:27.0724701Z 'R01.multiple_link_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:20:27.0725407Z 'R01.dual_energy_from_multiple_links' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:20:27.0726020Z 'R01.six_cell_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:20:27.0727149Z 'R01.six_cell_exact_loss' depends on axioms: [propext, Classical.choice, Quot.sound]
```
