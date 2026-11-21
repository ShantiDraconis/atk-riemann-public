# R01 — auditoria das branches candidatas ao produtor material

Em 21/11/2026 foram comparadas cinco branches candidatas com main.
A busca por caminho anterior cobriu 181 branches e a investigação
aqui examinou declarações que podem exercer a mesma função com
outros nomes. A inspeção de conteúdo continua dirigida.

| Branch | Evidência inspecionada | Resultado |
|---|---|---|
| atk/rh-bcf-three-term-materializer-20261001 | BCFThreeTermMaterializer.lean e BCFExplicitLogBounds.lean | Para o limite zero, o primeiro módulo recebe a decomposição majorante e a hipótese de que o termo de resíduos tende a zero. Para a taxa, o segundo recebe as três estimativas uniformes como campos. |
| audit/rh-log-majorant-materialized-20261001 | ConcreteLogMajorantLaws.lean | O transporte ao endpoint e o aumento de K recebem um certificado ou a própria desigualdade como hipótese. |
| atk/rh-r01-material-20261004 | Ledger de materialização | READY_CONDITIONAL, uma lacuna material e build real pendente no ledger consultado. |
| audit/rh-gram-final-materialized-20261001 | Comparação de caminhos com main | Contém módulos de transporte de majorantes. A comparação de caminhos não certifica um produtor concreto. |
| atk/rh-r01-weighted-decay-20261004 | Comparação Git | A referência estava atrás de main, sem commits exclusivos nessa comparação. |

## Enunciado preciso faltante na rota BCF

O módulo da taxa tem a estrutura BCFExplicitLogBounds D B. Ela exige
provas de A,Z,F≥0 e, para cada N, três desigualdades:

    logarithmicDerivative(N) ≤ A/log(N+2)
    zeroResidue(N) ≤ Z/log(N+2)
    entireRemainder(N) ≤ F/log(N+2).

A estrutura BCFThreeTermMajorant também exige a prova de que a soma
dos termos domina D_N. Dadas essas hipóteses, a adição entrega
D_N≤(A+Z+F)/log(N+2). Convergência qualitativa do termo de resíduos
seria suficiente na rota do limite e deixa em aberto sua taxa.
A inspeção não encontrou um habitante sem premissas para a estrutura
quantitativa concreta. A documentação do módulo aponta para a
estimativa de resíduos como obstáculo. As outras cotas e a
identificação do majorante concreto também precisam de evidência
formal antes da promoção.

O resultado material requerido é explicitGramRateTarget_real,
sem argumentos, e segue OPEN_MATH nesta auditoria.
A publicação divulga os resultados da inspeção e os enunciados
selecionados. Nenhum build novo foi executado.
