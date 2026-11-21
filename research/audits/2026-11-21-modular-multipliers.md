# Ponte de multiplicadores do R01

[Fontes auditadas](https://github.com/ShantiDraconis/atk-riemann-public/tree/6097070813cfbb3c3ed6e4892fc12bc1dfc10ea2/research/r01-rational-spectral-exclusion) e [build público](https://github.com/ShantiDraconis/atk-riemann-public/actions/runs/44938918858). A integração no repositório ATK de acesso restrito passou na execução 44938921570, job 136951596608.

DualMultipliers verifica a identidade linear para todos os vínculos j mod k e a cota de energia α²/perda, com perda positiva. Com α=1, a perda é a soma truncada dos quadrados de 1+Σ v_k(j mod k) com pesos 1/[j(j+1)]. Os coeficientes da convenção primal 1−Σ b_k(j mod k) correspondem a v_k=−b_k.

ConcreteClosure usa M=100N⁵ e uma família v(N,k). Para N≥2 recebe a comparação D_N≤perda_N+1/N e a cota perda_N≤C/log(N+2), com C≥0 independente de N. Produz ConcreteLogRate com K=max(log 3,C+1), dInf=0 e RiemannHypothesis. O teorema finito de energia e o de fechamento usam a mesma perda. A existência da família uniforme continua OPEN_MATH; a transferência do sanduíche escrito para a primeira premissa também precisa de prova no kernel para uso incondicional.

Saída de auditoria, UTC:

```text
2026-11-21T19:09:34.7673171Z 'R01.multiplier_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:09:34.7675832Z 'R01.dual_energy_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T19:09:34.7678395Z 'R01.closure_of_modular_multipliers' depends on axioms: [propext, Classical.choice, Quot.sound]
```
