# R01 — busca da contração no histórico

Auditoria de 21/11/2026. A consulta ao caminho `lean/MCore/RH/R0/HardFrontierReal.lean` foi executada nas 181 branches acessíveis do m-core-riemann. Todas retornaram arquivo ausente. Buscas de código nas branches padrão indexadas da conta também abrangeram nomes alternativos e termos ligados a contração e à cota uniforme. A busca por caminho em todas as 181 branches e a busca indexada por termos têm coberturas distintas. A inspeção por conteúdo permanece seletiva.

## Resultado encontrado sob outro nome

[ContracaoDN.lean](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ContracaoDN.lean) formaliza:

- `iter_contracao` itera a hipótese D(2N) ≤ q·D(N).
- `riemann_de_contracao` deduz RH recebendo a contração uniforme como premissa.
- `sem_contracao_de_piso_log` e `contracao_impossivel` deduzem a incompatibilidade dessa hipótese com o piso logarítmico positivo. O piso aparece como hipótese nesse módulo.

[Material/Closure.lean](https://github.com/ShantiDraconis/atk-riemann-public/blob/285874f28534eb8b5dba62817527a5aabafa0b45/imports/lean/MCore/Material/Closure.lean) recebe um habitante de RHClosure DN e o empacota. O teorema `closure_produces_bound` depende desse habitante.

## Diferença entre as escalas

Se D(2N) ≤ q·D(N) eventualmente para algum q<1, então D(2^k) ≤ C·q^k e D(2^k)·log(2^k+2) tende a zero. Um piso eventual D(N) ≥ c/log(N+2), com c>0, contradiz essa conclusão. Para N_j=2^(2^j), uma redução pela metade a cada passagem N_j→N_(j+1) entrega a escala 1/log(N_j) e é compatível em ordem com o piso. Também é possível usar ganhos variáveis em blocos de duplicação. A [redução por blocos](https://github.com/ShantiDraconis/atk-riemann-public/blob/e797387accbb99301a6cf3ede10e4a332170c56f/research/r01-block-gram-bound/README.md) registra o ganho exato a estimar.

A auditoria usa fontes públicas existentes e publica apenas a análise e a cobertura. A prova incondicional do produtor continua OPEN_MATH. Não houve novo build Lean.
