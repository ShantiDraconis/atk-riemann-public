# Checklist do R01 e correção do caso de quatro células

## Caso finito e limite na família com um gerador modular

Em N=2 a coluna r₂(m)=m mod 2 é (1,0,1,0,…) começando em m=1. Em M=4 a ortogonalidade nos incrementos é d₁+d₃=0. A normalização F₁=1 dá d₂+d₄=1. A energia excede 60/13 exatamente por 14d₁²+26(d₂−10/13)². O minimizador é (0,10/13,0,3/13). O recíproco do mínimo é H(2,4)=13/60, também igual ao erro primal. O cálculo 7/12 corresponde a anular a soma dos incrementos pares.

Mais geralmente, para N=2 e M≥1, o coeficiente primal ótimo é 1: nas células ímpares o erro é 1−b e nas pares é 1. Portanto L(2,M)=Σ_{j=1}^{⌊M/2⌋}[1/(2j)−1/(2j+1)]. Quando M cresce, a série harmônica alternada dá L(2,∞)=1−log 2. Aqui N está fixo em 2 e a restrição de cauda nula está ativa. O limite do corte M não fornece o limite dos resíduos completos quando N cresce.

## O que as branches localizadas estabelecem

O [inventário](../branch-inventory-and-ramp/README.md) contou 4.523 pares em 262 repositórios. O [levantamento do critério](../r01-complete-criterion/README.md) enumerou 657 branches em três repositórios. A [auditoria material](../r01-material-branch-audit/README.md) relata busca por caminho em 181 branches e comparação dirigida de cinco candidatas com main. A análise matemática não foi exaustiva sobre todo o histórico.

- A equivalência qualitativa de Báez–Duarte relaciona a convergência de D_N a zero com RH.
- A rota BCF combina três cotas uniformes e uma decomposição que domina D_N. O certificado dos três termos é uma entrada no materializador inspecionado.
- A branch do majorante transporta um certificado já fornecido. A branch material informa READY_CONDITIONAL. A comparação de caminhos da branch de Gram identifica transporte; a branch de decaimento ponderado estava atrás de main.
- As [branches identificadas pelo nome Claude](../r01-claude-branches/README.md) incluem resultados de transporte e periodicidade. A busca nominal cobre somente esse recorte.
- A [auditoria de Lean do endpoint concreto](2026-11-21-concrete-log-rate.md) registra a implicação da cota uniforme para dInf=0 e RiemannHypothesis, com os três axiomas permitidos.

## Condição de saída

Na via dual escrita, fixam-se N≥2 e M=100N⁵. A energia de todo vetor admissível com F₁=1 precisa ser pelo menos c log(N+2), com o mesmo c>0 para todos os índices. Pela [dualidade](../r01-dual-discrete-energy/README.md), isso dá L_N≤1/[c log(N+2)]. Pela [comparação com D_N](https://github.com/ShantiDraconis/atk-riemann-public/commit/cc7c4edf1ca7f686df198cf47431de03e9b25223), D_N≤L_N+1/N. Como log(N+2)≤N para N≥2 e D_N≤1 nos dois índices iniciais, K=max(log 3,1+1/c) serve para todo N.

A promoção do produtor requer (i) demonstrar a desigualdade de energia ou outra estimativa incondicional da mesma força; (ii) formalizar a transferência usada com as definições concretas do ledger; (iii) compilar e auditar o produtor sem parâmetros e o certificado derivado. O lema abstrato que inverte uma energia positiva só usa o item (i) como premissa. O estado quantitativo permanece OPEN_MATH.

## Verificação Lean do caso M=4

[Revisão auditada](https://github.com/ShantiDraconis/atk-riemann-public/commit/23e655083c3e8d4502c8e0cf6cbfd94a829176ea) e [execução pública](https://github.com/ShantiDraconis/atk-riemann-public/actions/runs/44938243815).

```text
2026-11-21T18:58:18.9432796Z 'R01.four_cell_energy_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-21T18:58:18.9433343Z 'R01.four_cell_exact_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
```
