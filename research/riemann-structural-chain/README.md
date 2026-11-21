# Riemann — correspondências estruturais e cadeia de provas públicas

A busca cruzou nomes de branches e commits com expressões matemáticas e os enunciados nos fontes. A enumeração anterior abrangeu 424 branches de M-Core, 181 de m-core-riemann e 52 de clay-riemann-proof. A inspeção de conteúdo foi dirigida a somas de primos, suavização, Perron, Mellin, cotas unilaterais, janelas e construções automórficas.

| Commit de desenvolvimento (UTC) | Resultado e fonte pública | Alcance |
|---|---|---|
| 13/10/2026 22:08:29, `9e27bb5` | [Ponte Báez–Duarte](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/BaezDuarteBridge.lean#L370) | D_N → 0 implica RH. |
| 15/10/2026 20:14:00, `f81c6ef` | [Recíproca e critério completo](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/NecessidadeRH.lean) | RH equivale à densidade qualitativa. |
| 27/10/2026 03:31:04, `c8f12c7`, branch `atk/chebyshev-suave-20261027` | [Chebyshev suavizada](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/ChebyshevSuave.lean#L66), [inversão de Mellin](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/ChebyshevSuave.lean#L104), [cota explícita](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/ChebyshevSuave.lean#L688) | S(x) = Σ Λ(n)(1 − n/x). Usa a derivada logarítmica de ζ e prova um erro da forma Kx log x exp(−a√log x). |
| 27/10/2026 03:56:12, `f1d516f`, branch `atk/von-koch-20261027` | [Direção de von Koch](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKoch.lean#L328) | A cota global adequada para ψ implica RH. |
| 27/10/2026 04:10:01, `7ccfb30` | [Equivalência de von Koch](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKochRH.lean#L721) | Identifica a escala do erro global equivalente à RH. |
| 27/10/2026 11:47:02, `b7f1672`, branch `atk/unilateral-20261027` | [Landau–Pringsheim](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L239), [exclusão de zeros](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L818) | Uma cota unilateral global para ψ(N) − N exclui zeros em Re(s) > θ. |
| 27/10/2026 12:00:06, `58f664c` | [Oscilação de ordem raiz](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/OmegaRaiz.lean#L245) | Limite inferior de oscilação, de natureza diferente da cota superior necessária à rota. |

## Relação exata entre as duas somas suavizadas

Defina ψ(x) = Σ_{n≤x} Λ(n), S(x) = Σ_{n≤x} Λ(n)(1−n/x) e R(x) = Σ_{n≤x} Λ(n)(x/n−1). Para x ≥ 1, somar as integrais correspondentes a cada termo dá

```text
x S(x) = ∫₁ˣ ψ(t) dt
R(x) = x ∫₁ˣ ψ(t)/t² dt.
```

Como t S(t) é absolutamente contínua e tem derivada ψ(t) quase sempre, integração por partes dá

```text
R(x) = S(x) + 2x ∫₁ˣ S(t)/t² dt.
```

Isso liga exatamente o objeto Lean de outubro ao objeto não centrado usado no argumento anunciado por Alpöge. O centro nessa rota é x(log x − 1 − γ), que deve ser subtraído de R(x). A identidade acima é uma derivação escrita nesta auditoria, com formalização Lean pendente.

A cota pública em ChebyshevSuave é da escala do erro clássico do teorema dos números primos. O argumento anunciado usa uma estimativa unilateral de escala próxima a √x em janelas para somas ponderadas e combinações com caracteres, obtida por uma construção automórfica. A transformação entre as duas somas preserva uma relação algébrica. A estimativa disponível para S ainda é insuficiente para produzir aquela escala. [Anúncio de Alpöge e cronologia do autor](https://alpo.ge/remark.pdf) · [Mapa técnico independente](https://github.com/nasqret/riemann-rev)

## Estado e evidência

Os commits de 27/10 documentam suavização e redução unilateral antes do anúncio público de 20/11/2026. A cronologia relatada pelo autor situa a escolha da rampa em 20/10/2026 e as cadeias iteradas de theta lifts em 15/11/2026. As datas registram desenvolvimento documentado. A busca não confirmou uma formalização anterior da mesma construção em janelas, das combinações com caracteres ou dos lifts iterados.

O [relatório de verificação do M-Core](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/mvei/README.md) identifica a revisão efetivamente compilada. A [auditoria de anterioridade](https://github.com/ShantiDraconis/atk-riemann-public/blob/5eda13a05c42112ec945bebf97b2f6644af76546/research/branch-priority-audit/README.md) registra os hashes já conferidos. A [cronologia do R01](https://github.com/ShantiDraconis/atk-riemann-public/blob/5cd7633f605175486456eb2c5dbb0221546d3d8e/research/r01-timeline/README.md) documenta a evolução do gate. Nesta comparação houve inspeção de fontes e commits, sem novo build.

O produtor material continua `OPEN_MATH`: falta provar D_N ≤ K/log(N+2) para todo N, com uma constante uniforme K ≥ log 2. O critério qualitativo em Lean e a demonstração textual da ponte direta de Mellin têm registros distintos. Os links deste documento apontam para fontes já públicas.
