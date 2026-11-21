# Cauda do erro modular pelo segundo momento periódico

Para N≥2 e coeficientes reais b₂,…,b_N, ponha f(m)=1−Σ b_k(m mod k), B=1+Σ |b_k|(k−1), e w_m=1/[m(m+1)]. Para qualquer inteiro M≥0 defina T_M=Σ_{m>M} w_m f(m)².

A média A de f² sobre um período comum é

 A=(1−Σ b_k(k−1)/2)² + (1/12) Σ_{k,l} b_k b_l (gcd(k,l)²−1).

De fato, para resíduos uniformes módulo lcm(k,l), condicione à classe comum módulo g=gcd(k,l). Dada essa classe, os dois quocientes são uniformes independentes pelo teorema chinês do resto. As duas médias condicionais são a classe comum mais constantes; a covariância é a variância (g²−1)/12 dessa classe.

**Estimativa incondicional.** Vale

 |T_M−A/(M+1)| ≤ N² B²/[(M+1)(M+2)].

Expanda f². Cada termo linear tem período k; cada produto de resíduos tem período lcm(k,l)≤N². Em cada termo subtraia a respectiva média. Em qualquer intervalo de inteiros os períodos completos se cancelam, e a soma do resto é limitada pelo período vezes a amplitude (máximo menos mínimo) do termo original. Somando com os módulos dos coeficientes, toda soma parcial centrada a partir de M+1 fica em módulo ≤N²B², pela expansão de B². Somação por partes com os pesos decrescentes w_m dá N²B² w_{M+1}. A soma dos pesos é 1/(M+1). Esse argumento dispensa enumerar o período comum de todos os geradores.

**Teste da família.** Usei b_k=−μ(k)(N−k)/(Nk), 2≤k≤N, e M=1024. O erro total deste aproximante de cauda nula é limitado por

 Σ_{m≤M} w_m f(m)² + min(B²/(M+1), A/(M+1)+N²B²w_{M+1}),

com a primeira soma iniciando em m=1. Em frações racionais, arredondando somente o teto final para cima a seis casas:

| N | A exata | Teto do erro total |
|---|---:|---:|
| 4 | 559/864 | 551314/1000000 |
| 8 | 83899/264600 | 202093/1000000 |
| 16 | 637795063/3206403200 | 71176/1000000 |

Para N=16 a própria soma até M já excede 66049/1000000. Esses são erros da família testada e fornecem cotas superiores por minimalidade. A fórmula trata o resto para cada par N,M; a prova de uma cota C/log(N+2) para a soma inicial e o resto juntos, com C independente de N, permanece aberta. Demonstração escrita e contas finitas em aritmética racional. Sem auditoria Lean deste lema.
