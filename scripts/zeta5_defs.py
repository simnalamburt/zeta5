"""Exact reference implementation of the objects defined in §2 and §5 of the paper.

A. Fauzan, "ζ(5) is irrational" (17 September 2026), `ZETA5_IS_IRRATIONAL.pdf`.
Equation numbers refer to the paper.  Everything here is exact rational arithmetic
(python-flint), so these functions double as a reference for the Lean definitions of Phase 1.

Affine values `a + b X` of the functional μ_X are represented as pairs `(a, b)` of `fmpq`.
"""

from functools import lru_cache

import gmpy2
from flint import arb, fmpq, fmpq_mat, fmpq_poly, fmpz

ALPHA = fmpq(3, 40)
LAMBDA = fmpq(37, 40)
H_CONST = fmpq(23, 20)  # H = 1 + 2α in (2.1)

T = fmpq_poly([0, 1])


def params(n):
    """(2.1): K = 40n, N = 3n, h = 37n."""
    return 40 * n, 3 * n, 37 * n


def D(m, start=1):
    """D_m(t) = ∏_{j=start}^{m} (t + j²).  `D(m)` is the paper's D_m."""
    p = fmpq_poly([1])
    for j in range(start, m + 1):
        p *= fmpq_poly([j * j, 1])
    return p


@lru_cache(maxsize=None)
def H5(j):
    """H_j^(5) = Σ_{v ≤ j} v⁻⁵."""
    if j == 0:
        return fmpq(0)
    return H5(j - 1) + fmpq(1, j**5)


@lru_cache(maxsize=None)
def mu_monomial(e):
    """(2.2): μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24."""
    return (-1) ** e * fmpq.bernoulli(2 * e + 2) * (2 * e + 3) * (2 * e + 4) * (2 * e + 5) / 24


@lru_cache(maxsize=None)
def mu_pole(j):
    """(2.3): μ_X(1/(t + j²)) = j⁴ (X - H_j^(5)) - 1/4 + 1/(2j), as (constant, coefficient of X)."""
    return (-(j**4) * H5(j) - fmpq(1, 4) + fmpq(1, 2 * j), fmpq(j**4))


def mu_poly(P):
    """μ on polynomials, by linearity from (2.2)."""
    s = fmpq(0)
    for e, c in enumerate(P.coeffs()):
        if c != 0:
            s += c * mu_monomial(e)
    return s


def mu_X(num, poles):
    """μ_X(num / ∏_{j ∈ poles} (t + j²)) for distinct positive integers `poles`.

    Polynomial division plus simple partial fractions, as described after (2.3).
    Returns (constant, coefficient of X)."""
    den = fmpq_poly([1])
    for j in poles:
        den *= fmpq_poly([j * j, 1])
    P, _ = divmod(num, den)
    dden = den.derivative()
    a, b = mu_poly(P), fmpq(0)
    for j in poles:
        c = num(-j * j) / dden(-j * j)
        p0, p1 = mu_pole(j)
        a += c * p0
        b += c * p1
    return a, b


def hankel_moments(n):
    """The Hankel symbols of G_K(X) in (2.4).

    Returns lists a, b of length 2h-1 with μ_X(D_N⁶ t^s / D_K) = a[s] + b[s] X.
    After cancellation D_N⁶ / D_K = D_N⁵ / D_tail with D_tail = ∏_{N<j≤K} (t + j²)."""
    K, N, h = params(n)
    W = D(N) ** 5
    Dtail = D(K, N + 1)
    dDtail = Dtail.derivative()
    poles = list(range(N + 1, K + 1))
    # residue of W t^s / D_tail at t = -j² is base_j (-j²)^s
    v = [W(-j * j) / dDtail(-j * j) for j in poles]
    p0 = [mu_pole(j)[0] for j in poles]
    j4 = [fmpq(j**4) for j in poles]
    a, b = [], []
    num = W
    for s in range(2 * h - 1):
        P, _ = divmod(num, Dtail)
        a.append(mu_poly(P) + sum((vj * pj for vj, pj in zip(v, p0)), fmpq(0)))
        b.append(sum((vj * qj for vj, qj in zip(v, j4)), fmpq(0)))
        num *= T
        v = [vj * (-j * j) for vj, j in zip(v, poles)]
    return a, b


def hankel(seq, h):
    return fmpq_mat(h, h, [seq[i + j] for i in range(h) for j in range(h)])


def G_matrices(n):
    """G_K(X) = A + X B as a pair of h×h rational matrices."""
    _, _, h = params(n)
    a, b = hankel_moments(n)
    return hankel(a, h), hankel(b, h)


def delta_poly(A, B):
    """Δ(X) = det(A + X B) ∈ ℚ[X], assuming B invertible.

    det(A + X B) = det B · det(X I + B⁻¹A) = det B · charpoly(-B⁻¹A)(X)."""
    C = B.solve(A)
    chi = (-C).charpoly()
    return B.det() * chi


def leading_coeff_29(n):
    """(2.9): [X^h] Δ_K = (-1)^{h(h-1)/2} ∏_{N<j≤K} j⁴ D_N(-j²)⁵."""
    K, N, h = params(n)
    DN = D(N)
    r = fmpq((-1) ** (h * (h - 1) // 2))
    for j in range(N + 1, K + 1):
        r *= fmpq(j**4) * DN(-j * j) ** 5
    return r


def factorial(m):
    return fmpz(int(gmpy2.fac(m)))


def S_K(n):
    """(2.5): S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)."""
    K, N, h = params(n)
    den = factorial(N) ** (12 * h)
    for i in range(1, h):
        den *= factorial(2 * i) ** 2
    return fmpq(factorial(K) ** (2 * h) * fmpz(4) ** (h - 1), den)


def log_S_K(n):
    """log S_K as an arb ball (avoids forming the huge rational)."""
    K, N, h = params(n)
    lf = lambda m: arb(m + 1).lgamma()
    r = 2 * h * lf(K) + (h - 1) * arb(4).log() - 12 * h * lf(N)
    for i in range(1, h):
        r -= 2 * lf(2 * i)
    return r


def vp_factorial(m, p):
    """Legendre's formula."""
    s, q = 0, p
    while q <= m:
        s += m // q
        q *= p
    return s


def vp_int(x, p):
    x = gmpy2.mpz(int(x))
    if x == 0:
        return None  # +∞
    return int(gmpy2.remove(x, p)[1])


def vp(q, p):
    """p-adic valuation of a rational; None stands for +∞."""
    q = fmpq(q)
    if q == 0:
        return None
    return vp_int(q.p, p) - vp_int(q.q, p)


def vp_SK(n, p):
    """(5.3), Legendre's formula for v_p(S_K)."""
    K, N, h = params(n)
    r = 2 * h * vp_factorial(K, p) - 12 * h * vp_factorial(N, p)
    r -= 2 * sum(vp_factorial(2 * i, p) for i in range(1, h))
    r += (h - 1) * vp_int(4, p)
    return r


def vpG(coeffs, p):
    """Gauss valuation: minimum p-adic valuation over the coefficients (None = +∞)."""
    vals = [vp(c, p) for c in coeffs if c != 0]
    return min(vals) if vals else None


def primes_upto(m):
    return [p for p in range(2, m + 1) if gmpy2.is_prime(p)]
