# Quais vínculos podem ser descartados na prova por energia?

Considere a [caracterização dual do erro truncado](https://github.com/ShantiDraconis/atk-riemann-public/blob/4d507ad69afc2021f9c8093eb35dcde3af397cde/research/r01-dual-discrete-energy/README.md). Escreva T_k(F)=Σ_m F_m−k Σ_j F_{kj}, com todas as somas truncadas em M.

**Proposição.** Fixe um inteiro livre de quadrados q≥2. Na família relaxada que impõe T_k(F)=0 apenas para índices k diferentes de q, a melhor constante na desigualdade F₁²≤H E(F) satisfaz H≥1/E_q>0 para todo M≥q, independentemente de N. Aqui E_q é um inteiro calculável com no máximo q parcelas.

**Prova.** Para 1≤m≤M, defina F_m=μ(q/m) se m divide q e F_m=0 nos outros casos, com F_{M+1}=0. A soma total é Σ_{d|q}μ(d)=0. Se k não divide q, nenhum múltiplo de k contribui. Se k divide q, a soma dos valores nos múltiplos de k é Σ_{d|(q/k)}μ(d), igual a 1 para k=q e a 0 nos demais casos. Portanto T_k(F)=−q quando k=q e T_k(F)=0 em todos os outros índices. Vale F₁=μ(q)=±1. O inteiro E_q=Σ_{m=1}^q m(m+1)(F_m−F_{m+1})² é positivo, pois F_q=1 e F_{q+1}=0. O vetor dividido por F₁ já tem a normalização requerida e a mesma energia. Isso prova a proposição.

Para q=3, o vetor normalizado começa por (1,0,−1) e segue com zeros. Seus incrementos dão energia 2+6+12=20. Para q=6 a energia é 92. Assim, reter somente as potências de dois deixa um piso de 1/20 no erro ótimo truncado da família relaxada, e reter somente os primos deixa um piso de 1/92. Agrupar todos os vínculos por escalas diádicas continua possível. O obstáculo ocorre quando o agrupamento perde a informação que detecta esses vetores.

Mais geralmente, se um q livre de quadrados fixo for omitido para infinitos N com M(N)≥q, a relaxação não pode fornecer a desigualdade E(F)≥c log(N+2) para todos os vetores normalizados e todos esses N, com c>0 independente de N. O vetor acima deixa de ser admissível no problema completo assim que o vínculo k=q é imposto.

Conferência por aritmética inteira de E_q para q=2,3,5,6,10,30: respectivamente 14,20,52,92,264,2652. A demonstração geral acima é escrita. O resultado é uma obstrução para relaxações; a estimativa uniforme do sistema completo permanece em OPEN_MATH.
