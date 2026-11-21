# Comparação datada com a rota anunciada por Alpöge

A sobreposição documentada no M-Core é a lógica analítica que transforma controle unilateral de uma soma centrada de von Mangoldt em ausência de zeros à direita de uma reta. Os registros abaixo são as primeiras ocorrências pertinentes que localizei na busca de commits. As horas são UTC e indicam o registro no Git.

| Registro | Resultado no M-Core | Fonte Lean pública |
|---|---|---|
| 27/10/2026, 03:56:12, commit `f1d516f` | Direção de von Koch. Uma cota global para o erro de ψ implica a ausência de zeros e, no expoente apropriado, RH. | [`RH_of_psi`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKoch.lean#L328) |
| 27/10/2026, 04:10:01, commit `7ccfb30` | Equivalência de von Koch entre RH e a estimativa global para ψ. | [`rh_iff_psi`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/VonKochRH.lean#L721) |
| 27/10/2026, 11:47:02, commit `b7f1672` | Landau–Pringsheim e versão unilateral. Uma cota superior global para ψ(N) − N implica ausência de zeros em Re(s) > θ. | [`landau`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L239), [`semZeros_of_psi_le`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L818), [`rh_iff_psi_le`](https://github.com/ShantiDraconis/atk-math-core-public/blob/751835c6e1aa915d261828e5a120345bc5d2462c/imports/M-Core/atk-kernel/ATK/ZeroClasses/Unilateral.lean#L955) |

O registro mais próximo do passo analítico de Alpöge é o terceiro. Ambos os argumentos usam informação unilateral sobre somas associadas a von Mangoldt para excluir zeros. As hipóteses têm alcances diferentes. No M-Core, a cota é global para a soma usual ψ(N) − N e está no antecedente do teorema. No anúncio de 20/11/2026, a rota usa uma soma ponderada pela rampa y/n − 1, combinações com caracteres e um critério de Landau localizado em janelas. A rota anunciada busca fornecer essas cotas por cadeias de theta lifts e uma desigualdade de Bost. [Anúncio de Alpöge](https://alpo.ge/remark.pdf) · [Mapa técnico independente](https://github.com/nasqret/riemann-rev)

O registro de outubro estabelece uma anterioridade documental para a formalização local dessas reduções em relação ao anúncio público de novembro. Von Koch e Landau são resultados clássicos. A comparação deixa em aberto a equivalência entre o critério global e o localizado e a prioridade sobre a construção automórfica. Também deixa em aberto a cota quantitativa própria do R01.

Esta nota foi produzida por inspeção de commits e fontes já públicas. Nenhum novo build Lean foi executado para a comparação.
