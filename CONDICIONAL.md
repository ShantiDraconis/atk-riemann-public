# Estado: CONDICIONAL — Hipótese de Riemann

Auditoria de 13/10/2026 sobre o commit `13e24b4` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 0. Ponte no formato NS — certificada no kernel

Mesmo formato do Navier–Stokes (`clayC_of_fc : FCBreakdownR3 → ClayC`):

| Peça | Declaração (`audit/lean/ATK/RHBridge.lean`) |
|---|---|
| Alvo exato | `RiemannHypothesis` (Mathlib) |
| Hipótese H | `ATK.RHBridge.NoZerosRightOfHalf` — `ζ(s) ≠ 0` para `Re s > 1/2` |
| Ponte | `rh_of_noZerosRightOfHalf : NoZerosRightOfHalf → RiemannHypothesis` (equação funcional `riemannZeta_one_sub`; os zeros que a reflexão `s ↦ 1 − s` não alcança são exatamente os triviais) |
| Força de H | **equivalente** ao alvo (`rh_iff_noZerosRightOfHalf`); como a Mathlib já prova `ζ ≠ 0` em `Re s ≥ 1`, o que falta é a faixa `1/2 < Re s < 1` |
| Falsificador | `not_rh_of_zero`: um zero com `Re s > 1/2` |
| Próximo elo | Nyman–Beurling/Báez-Duarte: `χ` no fecho `L²` da família `ρ(1/(kx))` ⇒ H (itens R1–R3) |
| Kernel | **5/5 CERTIFIED** — Lean 4.34.1 + Mathlib v4.34.1, só `propext`/`Classical.choice`/`Quot.sound` (workflow `audit-kernel`) |

## 0b. Linha de explosão — certificada no kernel

| Peça | Declaração (`audit/lean/ATK/RHExplosion.lean`) |
|---|---|
| Testemunha de explosão | `OffLineZero`: zero de `ζ` com `Re s > 1/2` |
| Refutação | `explosion_refutes : OffLineZero → ¬ RiemannHypothesis` |
| Dicotomia | `rh_iff_no_explosion : RiemannHypothesis ↔ IsEmpty OffLineZero` |
| Normalização | `explosion_of_not_rh`: todo contraexemplo de RH vira uma testemunha (reflexão `s ↦ 1 − s`) |
| Localização | `explosion_location`: uma explosão só existe em `1/2 < Re s < 1` |
| Estado | **nenhuma testemunha conhecida**; zeros verificados na reta até altura `3·10¹²` (Platt–Trudgian 2021) |

Fechar por explosão = exibir uma testemunha (OPEN_MATH → false, RH falsa). Fechar pelo lado
regular = provar `IsEmpty OffLineZero` (= H da ponte).

## 0c. Linha de fechamento — CLOSED_MATH calculado pelo kernel

Mesmo formato das linhas condicional e de explosão: **alvo exato** → **certificado** (declaração
sem hipóteses, de tipo exatamente o alvo) → **portão** (`audit/lean/scripts/closure_gate.py`:
kernel + axiomas padrão + controles) → **bandeira** calculada, nunca escrita à mão.

| Alegação | Alvo exato | CLOSED_MATH | Certificado | Rotas certificadas até ela |
|---|---|---|---|---|
| RH | `RiemannHypothesis` | **false** | — | ponte `rh_of_noZerosRightOfHalf` (H aberta) |
| ¬RH | `¬ RiemannHypothesis` | **false** | — | explosão `explosion_refutes` (sem testemunha) |

Controles do portão (todos OK, run `38387833807`): aceita uma decisão verdadeira de problema-brinquedo;
recusa alvo como `axiom`; recusa `sorry`; recusa a ponte e a linha de explosão oferecidas como
certificado (falta H / falta a testemunha); recusa `alvo ∨ ¬alvo` (teorema vazio).

Para mudar uma bandeira para `true`, basta acrescentar a `audit/lean/closure/registry.json`
uma declaração que o kernel aceite com o tipo exato — vinda de uma prova de H (pela ponte) ou de
uma testemunha (pela explosão). Nenhuma outra edição altera o resultado.

## 1. Alvo exato

`RiemannHypothesis` (Mathlib): todo zero `s` de `ζ`, não trivial e `s ≠ 1`, tem `Re s = 1/2`.
Enunciável. No portão de fechamento ATK (M-Core, `closure/closure_gate.py`) só contam
declarações de tipo exatamente `RiemannHypothesis` ou `¬ RiemannHypothesis`.

**Estado no portão: CONDICIONAL** — ponte certificada; H em aberto (equivalente ao alvo).

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

CONDICIONAL → FECHADO somente com uma declaração de tipo `RiemannHypothesis` (ou a negação) aceita
pelo portão: compilada no kernel, sem `sorry`, só com `propext`, `Classical.choice`,
`Quot.sound`, e sem a conclusão entre as hipóteses.

---

**English summary.** Status CONDITIONAL: kernel-checked bridge `NoZerosRightOfHalf → RiemannHypothesis` via Mathlib's functional equation (H is equivalent to RH; the remaining region is `1/2 < Re s < 1`). The imported `RHClosure DN` takes `DN` as a
free parameter (trivially inhabited with `DN := 0`); to matter it must be the actual
Nyman–Beurling/Báez-Duarte distance (R1), the criterion "bound ⇒ RH" must be formalized (R2), and
the uniform upper bound `D_N ≤ K0/log N` itself is the open content (R3). Numerics are evidence,
not proof. Falsifier: a nontrivial zero off the critical line.
