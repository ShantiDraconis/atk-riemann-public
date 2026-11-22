# ATK RIEMANN — Formal Research

Research repository maintained by Tiago Paschoalatto Fagliari (ORCID: https://orcid.org/0009-0006-6874-3910).

Status: **research in progress; no unconditional solution or Millennium Prize certification is claimed.**

This repository will preserve source paths, original commit SHAs, authorship, dependencies, and exact Lean verification outcomes. A successful Lean build does not by itself prove an original open problem unless the formalized theorem exactly matches it and all assumptions are discharged.

Related publication: https://doi.org/10.5281/zenodo.15164501 (historical publication; not a proof certificate).

Do not add confidential data or third-party code without checking its license and attribution.

## R01 em revisão pública

A autoria deste projeto está registrada em nome de **Tiago Paschoalatto Fagliari**. Para citar uma contribuição específica, indique também o nome da declaração Lean e o commit que examinou. [Dados de citação](CITATION.cff)

| Para quem quer | Onde começar |
|---|---|
| Ler a demonstração modular | [Lei dos multiplicadores](research/r01-rational-spectral-exclusion/DualMultipliers.lean) e [teorema de fechamento condicional](research/r01-rational-spectral-exclusion/ConcreteClosure.lean) |
| Conferir uma alegação | [Enunciados e alcance de cada resultado](research/audits/external-certificates/CLAIMS.md) e [protocolo de reprodução](research/audits/external-certificates/REPRODUCE.md) |
| Examinar o que falta | [Registro das obrigações abertas](research/audits/2026-11-22-r01-public-gap-register.md) |
| Discutir ou contestar um passo | [Discussão pública na issue #5](https://github.com/ShantiDraconis/atk-riemann-public/issues/5) |

A pergunta matemática para revisão é se existe uma família de multiplicadores e **uma mesma constante** que dê a cota logarítmica para todo índice a partir de 2. O teorema de fechamento recebe essa estimativa e a transferência para a distância concreta como hipóteses. Uma contribuição à discussão pode identificar o passo que resolve, o enunciado exato e uma demonstração ou um contraexemplo que outros leitores possam conferir.

<!-- mvei:start -->
## Lean sources and kernel check (MVEI)

[`imports/m-core-riemann/`](imports/m-core-riemann/) holds the Lean sources of `ShantiDraconis/m-core-riemann` at commit `193117c` (2026-10-11): 27 files. In the MVEI verification the Lean kernel closed 191 theorems here (56 unique, without the lemmas Lean generates itself), with 0 conditional and 0 open (`sorry`). A closed theorem proves the statement written in the file; it is not a claim that an open problem is solved. Statements, axioms, the build log and how to reproduce: [`mvei/README.md`](mvei/README.md).
<!-- mvei:end -->

<!-- mvei-branches:start -->
## Theorems found only on branches

26 branch(es) with 650 theorems that exist only on branches and that the Lean kernel closed, each with a certificate (commit, date, history, SHA-256): [`branches/README.md`](branches/README.md).
<!-- mvei-branches:end -->
