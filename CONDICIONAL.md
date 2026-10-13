# Estado: CONDICIONAL — Hipótese de Riemann

Auditoria de 13/10/2026 sobre o commit `13e24b4` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

`RiemannHypothesis` (Mathlib): todo zero `s` de `ζ`, não trivial e `s ≠ 1`, tem `Re s = 1/2`.
Enunciável. No portão de fechamento ATK (M-Core, `closure/closure_gate.py`) só contam
declarações de tipo exatamente `RiemannHypothesis` ou `¬ RiemannHypothesis`.

**Estado no portão: ABERTO.**

## 2. Varredura do conteúdo

2 arquivos Lean · 0 `axiom` · 0 `sorry`/`admit`.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Onde | Por que é condicional | O que fechar |
|---|---|---|---|---|
| R1 | `RHClosure DN` / `ConcreteUniformLogDNBound DN` | `imports/lean/MCore/Material/Closure.lean` | `DN : ℕ → ℝ` é **parâmetro livre**: com `DN := 0` e `K0 := 0` a estrutura é habitada sem matemática; `closure_produces_bound` é só `⟨h⟩` | Fixar `DN` como a distância de Nyman–Beurling/Báez-Duarte definida (ínfimo em `L²(0,∞)` sobre combinações de `ρ(1/(kx))`, `k ≤ N`), não como parâmetro |
| R2 | Ponte "cota ⇒ RH" | ausente | O critério de Báez-Duarte (RH ⇔ `d_N → 0`) não está na Mathlib nem aqui | Formalizar: `D_N ≤ K0/log(N+2)` para a família real ⇒ `RiemannHypothesis` |
| R3 | A cota uniforme em si | — | É o conteúdo aberto. A numérica (Gram de Vasyunin até `N = 1000`, M-Core `numerics/`) é compatível com `D_N ≈ C/log N`, mas número não é prova. Burnol (2002) provou uma cota **inferior** dessa ordem; a **superior** é aberta e (com R2) implicaria RH | Prova analítica da cota superior para todo `N` |
| R4 | Alvo inconsistente entre repositórios | `atk-math-core-public` registra para RH `FiniteSpanApproximatesChi concreteGeneratorFamily`; aqui é `ConcreteUniformLogDNBound` | Dois "alvos terminais" diferentes para o mesmo problema | Um único alvo canônico: `RiemannHypothesis`; os dois anteriores ficam como rotas CONDICIONAIS a R2 |
| R5 | `ATK/Riemann.lean` (4 lemas de Gram/Schur) | `imports/m-core-riemann/atk-kernel/ATK/Riemann.lean` | Lemas auxiliares corretos e genéricos; não mencionam `ζ` | Nenhuma correção matemática; só ligar a R1/R2 |
| R6 | Compilação | todo `imports/` | Instantâneos: `Closure.lean` importa `MCore`, ausente aqui; não compila isoladamente | CI que compila a partir do commit de origem registrado em `provenance/` |

## 4. Falsificador exato

Um zero `s` de `ζ` com `s ≠ 1`, não trivial e `Re s ≠ 1/2` — necessariamente com `0 < Re s < 1`
(M-Core: `ATK.Closure.rh_false_iff`, `ATK.Closure.rh_counterexample_in_open_strip`;
`atk-math-core-public`: `RiemannOffCriticalZero`).

## 5. Condição para mudar o estado

ABERTO → FECHADO somente com uma declaração de tipo `RiemannHypothesis` (ou a negação) aceita
pelo portão: compilada no kernel, sem `sorry`, só com `propext`, `Classical.choice`,
`Quot.sound`, e sem a conclusão entre as hipóteses.

---

**English summary.** Status CONDITIONAL / gate OPEN. The imported `RHClosure DN` takes `DN` as a
free parameter (trivially inhabited with `DN := 0`); to matter it must be the actual
Nyman–Beurling/Báez-Duarte distance (R1), the criterion "bound ⇒ RH" must be formalized (R2), and
the uniform upper bound `D_N ≤ K0/log N` itself is the open content (R3). Numerics are evidence,
not proof. Falsifier: a nontrivial zero off the critical line.
