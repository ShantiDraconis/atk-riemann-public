"""Evaluate the smoothed Möbius approximant by reciprocal cells."""
import math

import numpy as np
from sympy import mobius


def squared_error(n, cells):
    indices = np.arange(1, n + 1)
    weights = -np.array([int(mobius(int(k))) for k in indices])
    coefficients = weights * (1 - np.log(indices) / math.log(n))
    tail = math.fsum(coefficients / indices)
    m = np.arange(1, cells + 1)
    residual = 1 - m * tail
    for k, coefficient in zip(indices, coefficients):
        if coefficient:
            residual += coefficient * (m // k)
    included = tail**2 + np.sum(residual**2 / (m * (m + 1.0)))
    omitted_bound = (1 + math.fsum(abs(coefficients)))**2 / (cells + 1)
    return tail, included, omitted_bound


if __name__ == "__main__":
    print("N       sum(a/k)       partial error    omitted upper bound")
    for n in (16, 32, 64, 128, 256):
        tail, partial, omitted = squared_error(n, 1_000_000)
        assert partial >= tail**2 and omitted > 0
        print(f"{n:3d}  {tail: .9f}      {partial:.9f}        {omitted:.9f}")
