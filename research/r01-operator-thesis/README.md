# R01 — tese técnica das formulações e seus operadores

Registro de 21/11/2026. O alvo quantitativo continua OPEN_MATH.

## Objetos e passagens

| Formulação | Operador ou lei | Escopo verificável |
|---|---|---|
| Real, Hilbert | P_N é a projeção ortogonal em V_N=span(φ₁,...,φ_N), no espaço L²((0,∞),dx). χ=1_(0,1], φ_k(x)={1/(kx)} e D_N=||χ−P_Nχ||². | Inclusão de espaços dá monotonicidade. A [fórmula de Gram e ganho por bloco](../r01-block-gram-bound/README.md) calcula a variação do mínimo. |
| Restrição de cauda | A(g)=⟨g,t⟩, t=1_(1,∞)/x. O subespaço de cauda nula é ker A dentro de V_N. | [Custo exato da projeção restrita](../r01-exact-tail-penalty/README.md): D_N≤D_N^(0)≤(log(2π)−γ)D_N para N≥1. |
| Fracionário e modular | Para m=floor(1/x), kφ_k−φ₁=m mod k. A leitura por células é uma isometria para funções constantes nessas células com pesos 1/[m(m+1)]. | [Período, integral dos pesos e equações normais](../r01-modular-period/README.md). [Certificados racionais de truncagem](../r01-rational-certificates/README.md). |
| Euler e aritmética | Diferença discreta das somas com piso, convolução com a função constante 1, inversão por μ. | [Inversão explícita dos erros nas primeiras N−1 células](../r01-interpolation-inverse/README.md). |
| Riemann e Mellin | M(f)(s)=∫₀∞ f(x)x^(s−1)dx. Na reta crítica, a mudança logarítmica de variável torna M uma transformada de Fourier. | [Fórmula espectral e redução qualitativa](../r01-complete-criterion/README.md). A [ponte direta](../r01-mellin-bridge/README.md) está demonstrada em texto. |
| Somas de von Mangoldt | Integração de ψ(t) contra 1 ou t^(−2) relaciona as somas suavizadas S e R. | [Identidade integral e comparação estrutural](../riemann-structural-chain/README.md). A estimativa na escala do R01 ainda precisa de prova. |
| Critério e auditoria | O R01 pede D_N≤K/log(N+2). O critério qualitativo estabelece RH ↔ D_N→0. | [Índice das declarações auditadas](../kernel-verified-index/README.md). A cota logarítmica uniforme não está demonstrada. |

## Ponte explícita entre coeficientes aritméticos e Mellin

Escreva g=Σ a_k φ_k e A_N(s)=Σ a_k k^(−s). Pela identidade de
Mellin dos geradores, no interior da faixa crítica,

    M(χ−g)(s) = [1 + ζ(s) A_N(s)]/s.

Se a cauda está anulada, escreva g=Σ_{k=2}^N b_k(kφ_k−φ₁).
Substituir cada gerador dá, com os mesmos coeficientes,

    A_N(s) = Σ_{k=2}^N b_k(k^(1−s)−1),
    A_N(1) = 0.

A recíproca vale para os polinômios de Dirichlet de comprimento N:
a condição A_N(1)=0 força a₁=−Σ_{k=2}^N a_k/k; tomando
b_k=a_k/k, recupera-se a forma modular. Com s=1/2+it e a
normalização usual de Plancherel:

    Σ_{m≥1} |1 − Σ_{k=2}^N b_k(m mod k)|²/[m(m+1)]
      = (1/2π)∫_ℝ |1+ζ(s)A_N(s)|²/(1/4+t²) dt.

Para justificar a normalização, ponha x=e^u e F(u)=e^(u/2)f(e^u).
Então ||F||²_L²(ℝ)=||f||²_L²(0,∞) e M(f)(1/2+it) é a transformada
de Fourier com núcleo e^(itu). Plancherel fornece o fator 1/(2π).
Assim o erro discreto e o erro na reta crítica coincidem para a
mesma escolha de coeficientes. O produto de Euler fornece
1/ζ(s)=Σ μ(k)k^(−s) para Re(s)>1. Sua utilidade como inspiração
para coeficientes deixa pendente a estimativa ponderada em Re(s)=1/2.

## Obstruções e estados formais

A [divergência do interpolante com correção no último gerador](../r01-last-generator-obstruction/README.md)
é uma obstrução matemática a uma família concreta. O estado
aberto-sorry informa dependência de uma lacuna na revisão auditada.
O estado nao_alcancado informa ausência de verificação daquela
declaração no build registrado. Esses estados são metadados de
verificação e não coordenadas analíticas do plano complexo.

As representações preservam ou comparam normas nos escopos
declarados. A ortogonalidade usada é a do espaço de Hilbert nos
teoremas de projeção. Na formulação de Mellin, 1/2 é a coordenada
real fixa e t é a coordenada imaginária. N é um índice de
truncagem externo. O [primeiro cruzamento do limiar de raiz](../r01-first-square-root-crossing/README.md)
é um problema separado sobre esse índice.

## Lema material que fecharia a cadeia

Basta construir para todo N≥2 um A_N de comprimento N com
A_N(1)=0 e provar que a integral acima é ≤K/log(N+2) para
um mesmo K. A versão modular é equivalente em ordem à
formulação sem restrição de cauda, pelo controle uniforme do custo.
Então a minimalidade produz a cota para D_N e o majorante
logarítmico produz DNLimit=0. A prova desse lema ainda falta.

Esta síntese registra as conexões matemáticas em texto e remete aos
snapshots já auditados. Não houve novo build Lean. O registro
público data a síntese e preserva as referências clássicas.
