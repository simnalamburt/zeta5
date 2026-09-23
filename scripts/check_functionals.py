# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint>=0.7", "gmpy2", "mpmath"]
# ///
"""Phase 0: the functionals μ_X (§2) and τ_X (§3), checked against their defining properties.

Getting these definitions exactly right (signs, the B₁ convention, the harmonic index d(r)) is the
first task of Phase 1, so they are checked here before anything is formalised.

* Proposition 2.2: μ_{ζ(5)}(R) = ∫_0^∞ R(y²) w(y) dy for monomials, for simple poles 1/(t + a²)
  (Hermite's formula, also at non-integer a), and for entries of G_40(ζ(5)) (numerical quadrature);
* the pullback identity (3.1) μ_X(R) = τ_X(x⁵ R(-x²)) for random rational functions (exact);
* the reflection and difference identities (3.2), (3.3) (exact);
* the distribution formula (3.7) for polynomials (Bernoulli multiplication, exact);
* C_p ∈ p⁵ ℤ_p in (3.6), using the expansion (3.5).

Run: `uv run scripts/check_functionals.py`.
"""

import random
import sys

import mpmath as mp
from flint import fmpq, fmpq_poly

from zeta5_defs import D, H5, G_matrices, mu_monomial, mu_pole, mu_X, params, vp

failures = []


def check(name, ok, detail=""):
    print(f"[{'OK' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        failures.append(name)


# ---------------------------------------------------------------------------------------------
# Proposition 2.2


def w(y):
    """(2.10): w(y) = (2π)⁴ y⁵/12 Σ ℓ⁴ e^{-2πℓy}, via Σ ℓ⁴ q^ℓ = q(1+11q+11q²+q³)/(1-q)⁵."""
    q = mp.exp(-2 * mp.pi * y)
    return (2 * mp.pi) ** 4 * y**5 / 12 * q * (1 + 11 * q + 11 * q**2 + q**3) / (1 - q) ** 5


def integral(f):
    # fine subdivision: the integrands are analytic only in a strip of width ~1 around (0, ∞)
    pts = [mp.mpf(k) / 4 for k in range(0, 200)] + [mp.inf]
    return mp.quad(lambda y: f(y) * w(y), pts)


def rel(a, b):
    return abs(a - b) / max(abs(a), abs(b))


def to_mp(q):
    return mp.mpf(int(q.p)) / int(q.q)


# ---------------------------------------------------------------------------------------------
# τ_X of §3: L(x^k) = B_k (B₁ = -1/2), τ(P) = L(P''')/24, τ_X(1/(x - r)) = H_{d(r)}^(5) - X


def d_index(r):
    return r if r >= 0 else -r - 1


def tau_poly(P):
    P3 = P.derivative().derivative().derivative()
    s = fmpq(0)
    for k, c in enumerate(P3.coeffs()):
        if c != 0:
            s += c * fmpq.bernoulli(k)
    return s / 24


def tau_X(num, poles):
    """τ_X(num / ∏_{r ∈ poles} (x - r)) for distinct integers r, as (constant, coefficient of X)."""
    den = fmpq_poly([1])
    for r in poles:
        den *= fmpq_poly([-r, 1])
    P, _ = divmod(num, den)
    dden = den.derivative()
    a, b = tau_poly(P), fmpq(0)
    for r in poles:
        c = num(r) / dden(r)
        a += c * H5(d_index(r))
        b -= c
    return a, b


def compose(P, Q):
    """P(Q(x))."""
    r = fmpq_poly([0])
    for c in reversed(P.coeffs()):
        r = r * Q + c
    return r


def rand_poly(deg, rng):
    return fmpq_poly([fmpq(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(deg + 1)])


def main():
    rng = random.Random(20260923)
    mp.mp.dps = 40
    z5 = mp.zeta(5)

    print("== Proposition 2.2 (numerical quadrature, 40 digits)")
    worst = max(rel(to_mp(mu_monomial(e)), integral(lambda y, e=e: y ** (2 * e))) for e in range(12))
    check("μ(t^e) = ∫ y^{2e} w(y) dy for e < 12", worst < mp.mpf(10) ** -30, f"max rel. err {mp.nstr(worst, 3)}")
    worst = 0
    for j in range(1, 8):
        c0, c1 = mu_pole(j)
        worst = max(worst, rel(to_mp(c0) + to_mp(c1) * z5, integral(lambda y, j=j: 1 / (y**2 + j * j))))
    check("(2.3) μ_ζ(5)(1/(t + j²)) = ∫ w(y)/(y² + j²) dy for j < 8", worst < mp.mpf(10) ** -30,
          f"max rel. err {mp.nstr(worst, 3)}")
    worst = 0
    for a in [mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf("4.25")]:
        hermite = a**4 * mp.zeta(5, a) - 1 / (2 * a) - mp.mpf(1) / 4
        worst = max(worst, rel(hermite, integral(lambda y, a=a: 1 / (y**2 + a * a))))
    check("Hermite: ∫ w(y)/(y² + a²) dy = a⁴ ζ(5, a) - 1/(2a) - 1/4 at non-integer a", worst < mp.mpf(10) ** -30,
          f"max rel. err {mp.nstr(worst, 3)}")

    # entries of G_40(ζ(5)); the exact entries a + b ζ(5) cancel heavily, so ζ(5) needs many digits
    n = 1
    K, N, h = params(n)
    A, B = G_matrices(n)
    DN6, DK = D(N) ** 6, D(K)
    worst = 0
    for i, j in [(0, 0), (3, 5), (10, 10), (20, 30), (36, 36)]:
        mp.mp.dps = 2000
        exact = to_mp(A[i, j]) + to_mp(B[i, j]) * mp.zeta(5)
        mp.mp.dps = 40
        R = lambda y, s=i + j: mp_poly(DN6, y * y) * (y * y) ** s / mp_poly(DK, y * y)
        worst = max(worst, rel(+exact, integral(R)))
    check("G_40(ζ(5))_{ij} = ∫ D_N⁶(y²) y^{2(i+j)} / D_K(y²) w(y) dy (sampled entries)",
          worst < mp.mpf(10) ** -12, f"max rel. err {mp.nstr(worst, 3)}")

    print("\n== (3.1) pullback μ_X(R) = τ_X(x⁵ R(-x²))")
    ok = True
    for _ in range(40):
        poles = rng.sample(range(1, 12), rng.randint(1, 4))
        num = rand_poly(rng.randint(0, 10), rng)
        lhs = mu_X(num, poles)
        # x⁵ num(-x²) / ∏ (j² - x²) = (-1)^k x⁵ num(-x²) / ∏ (x - j)(x + j)
        numx = fmpq_poly([0, 0, 0, 0, 0, 1]) * compose(num, fmpq_poly([0, 0, -1]))
        sign = (-1) ** len(poles)
        rhs = tau_X(numx * sign, sorted(poles + [-j for j in poles]))
        ok &= lhs == rhs
    check("(3.1) on 40 random rational functions", ok)

    print("\n== (3.2), (3.3)")
    ok2 = ok3 = True
    for _ in range(40):
        poles = rng.sample(range(-8, 9), rng.randint(0, 4))
        num = rand_poly(rng.randint(0, 9), rng)
        # g(-1-x): a pole at r becomes a pole at -1-r, and the denominator picks up a sign
        num_r = compose(num, fmpq_poly([-1, -1])) * (-1) ** len(poles)
        a, b = tau_X(num, poles)
        ar, br = tau_X(num_r, [-1 - r for r in poles])
        ok2 &= (ar, br) == (-a, -b)
        if 0 in poles:
            continue
        # g(x+1) - g(x) over the common denominator
        den = fmpq_poly([1])
        for r in poles:
            den *= fmpq_poly([-r, 1])
        den_sh = compose(den, fmpq_poly([1, 1]))
        allp = sorted(set(poles) | {r - 1 for r in poles})
        full = fmpq_poly([1])
        for r in allp:
            full *= fmpq_poly([-r, 1])
        diff_num = compose(num, fmpq_poly([1, 1])) * divmod(full, den_sh)[0] - num * divmod(full, den)[0]
        lhs = tau_X(diff_num, allp)
        ok3 &= lhs == (derivative_at_zero(num, den, 4) / 24, fmpq(0))
    check("(3.2) τ_X(g(-1-x)) = -τ_X(g(x)) on 40 random g", ok2)
    check("(3.3) τ_X(g(x+1) - g(x)) = g⁗(0)/24 on random g regular at 0", ok3)

    print("\n== (3.7) for polynomials (Bernoulli multiplication)")
    ok = True
    for p in [7, 11, 13]:
        for _ in range(5):
            g = rand_poly(rng.randint(3, 14), rng)
            rhs = sum((tau_poly(compose(g, fmpq_poly([a, p]))) for a in range(p)), fmpq(0)) / p**4
            ok &= tau_poly(g) == rhs
    check("τ(g) = p⁻⁴ Σ_a τ(g(a + px)) for polynomial g, p ∈ {7, 11, 13}", ok)

    print("\n== (3.6) C_p ∈ p⁵ ℤ_p via (3.5)")
    ok = True
    detail = []
    for p in [7, 11, 13, 17]:
        # τ^an(1/(x + a/p)) = -1/4 Σ_k C(k+3, 3) B_k s^{-k-4} with s = -a/p; term k has valuation ≥ k+3,
        # so truncating at k ≤ 40 determines C_p modulo p^40.
        Cp = fmpq(0)
        for a in range(1, p):
            s = fmpq(-a, p)
            Cp += -fmpq(1, 4) * sum((fmpq(binom(k + 3, 3)) * fmpq.bernoulli(k) * s ** (-k - 4)
                                     for k in range(41)), fmpq(0))
        v = vp(Cp, p)
        detail.append(f"v_{p} = {v}")
        ok &= v >= 5
    check("v_p(C_p) ≥ 5 for p ∈ {7, 11, 13, 17}", ok, ", ".join(detail))

    print()
    if failures:
        print(f"{len(failures)} check(s) FAILED")
        sys.exit(1)
    print("all checks passed")


def binom(n, k):
    from math import comb
    return comb(n, k)


def derivative_at_zero(num, den, k):
    """The k-th derivative of num/den at 0, from its power series."""
    from math import factorial
    # power series division up to order k
    nc = num.coeffs() + [fmpq(0)] * (k + 1)
    dc = den.coeffs() + [fmpq(0)] * (k + 1)
    q = []
    for i in range(k + 1):
        s = nc[i] - sum((q[j] * dc[i - j] for j in range(i)), fmpq(0))
        q.append(s / dc[0])
    return q[k] * factorial(k)


def mp_poly(P, x):
    r = mp.mpf(0)
    for c in reversed(P.coeffs()):
        r = r * x + to_mp(c)
    return r


if __name__ == "__main__":
    main()
