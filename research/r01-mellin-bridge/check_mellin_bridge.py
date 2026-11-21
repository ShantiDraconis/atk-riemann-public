"""Numerical regression checks for the direct Mellin functional."""
import math
import mpmath as mp


def finite_mellin(s, k, cells):
    """Integrate exactly on reciprocal cells, up to floating-point rounding."""
    terms = []
    hi = 1.0 + 0j
    for m in range(1, cells + 1):
        lo = (m + 1) ** (-s)
        terms.append((hi * m - lo * (m + 1)) / (k * (s - 1))
                     - (m // k) * (hi - lo) / s)
        hi = lo
    return complex(math.fsum(t.real for t in terms),
                   math.fsum(t.imag for t in terms))


def check(s, k, cells):
    corrected_tail = mp.quad(lambda u: 1 / (k * (1 - s)), [0, 1])
    # u = 1/x yields a constant integrand for r_k(x) q_s(x) dx.
    expected_tail = 1 / (k * (1 - s))
    assert abs(corrected_tail - expected_tail) < 1e-12
    actual = finite_mellin(s, k, cells) + complex(corrected_tail)
    expected = complex(-mp.power(k, -s) * mp.zeta(s) / s)
    truncation = (cells + 1) ** (-s.real) / s.real
    discrepancy = abs(actual - expected)
    assert discrepancy <= truncation + 1e-10
    norm_sq = 1 / (2 * s.real - 1) + 1 / abs(1 - s) ** 2
    lower_bound = 1 / (abs(s) ** 2 * norm_sq)
    assert 0 < lower_bound <= 1
    print(f"s={s}, k={k}: residual={discrepancy:.3e}, "
          f"truncation bound={truncation:.3e}")


if __name__ == "__main__":
    for point in (0.75 + 0j, 0.6 + 3j, 0.75 + 14j):
        for index in (1, 2, 7):
            check(point, index, 20_000)
    print("9 numerical checks passed")
