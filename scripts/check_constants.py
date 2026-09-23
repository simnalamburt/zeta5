# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Phase 0: exact reproduction of the rational constants of §5 and Appendix B.

Everything is exact rational arithmetic (`fractions.Fraction`); no floating point is used for any
claim.  Checks:

* the inner limiting function R(x) of (5.4)-(5.6), computed straight from the definitions, agrees
  with the closed form (5.12), (5.13), (B.1);
* R is affine between the breakpoints (B.2), there are 143 such intervals, and (B.3) reproduces
  Table 3 and (5.18);
* the outer integrand of §5.2 reproduces Table 4, ∫ d = 9/640 and I_out = 127751/96000 (5.10);
* the tail constants P̄, the bound on |C|, (5.16), (5.17), A* (5.19), A_M (5.20);
* the final margins (7.2) and the values of A_200, A_100000 in Appendix B.3;
* the quadratic-coefficient identity stated after (B.2).

Run: `uv run scripts/check_constants.py`.
"""

import math
import sys
from fractions import Fraction as Fr

ALPHA = Fr(3, 40)
LAMBDA = Fr(37, 40)
H = 1 + 2 * ALPHA  # 23/20

failures = []


def check(name, ok, detail=""):
    print(f"[{'OK' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        failures.append(name)


def floor(x):
    return math.floor(x)


def frac(x):
    return x - floor(x)


def pos(x):
    return x if x > 0 else Fr(0)


# ---------------------------------------------------------------------------------------------
# §5.1  The inner limiting function, from the definitions (5.4)-(5.6)


def ell(x, z):
    """ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1."""
    return floor(x - z) + floor(x + z) + 1


def Gamma(x):
    """(5.4).  The z-integral is computed exactly: the integrand is a step function of z whose
    jumps are at the fractional parts f, 1-f of x and g, 1-g of αx."""
    f, g = frac(x), frac(ALPHA * x)
    cuts = sorted({Fr(0), Fr(1, 2)} | {c for c in (f, 1 - f, g, 1 - g) if 0 < c < Fr(1, 2)})
    T = floor(2 * H * x)
    integral = Fr(0)
    for lo, hi in zip(cuts, cuts[1:]):
        z = (lo + hi) / 2
        l = ell(x, z)
        b = 3 * ell(ALPHA * x, z)
        integral += (hi - lo) * (T - b) * (T + b - l - 5)
    s = H * x - Fr(T, 2)
    q = floor(2 * x)
    n_plus = (2 * x - q) / 2
    return integral + s * (2 * T - q - 5) + pos(s - n_plus)


def J(u):
    m = floor(2 * u)
    return m * u - Fr(m * (m + 1), 4)


def Nfun(x):
    """(5.5)."""
    return 2 * LAMBDA * x * floor(x) - 12 * LAMBDA * x * floor(ALPHA * x) - 2 * J(LAMBDA * x)


def R_def(x):
    """(5.6)."""
    return -Gamma(x) - Nfun(x)


# The closed form (5.12), (5.13), (B.1)


def d0(u):
    return min(u, 1 - u)


def e(u):
    return 1 if u <= Fr(1, 2) else -1


def R_closed(x):
    f, g = frac(x), frac(ALPHA * x)
    tau, sigma, eta = frac(2 * H * x), frac(2 * x), frac(2 * LAMBDA * x)
    F = 4 * LAMBDA + 2 * LAMBDA * f - 12 * LAMBDA * g
    intB2 = d0(g) * (1 - 2 * d0(g))
    intAB = e(f) * e(g) * (min(d0(f), d0(g)) - 2 * d0(f) * d0(g))
    Q = (tau * (tau - sigma) - pos(tau - sigma) + eta * (1 - eta)) / 2 + 9 * intB2 - 3 * intAB
    return x * F + Q, F, Q


def inner_breakpoints(lo, hi):
    """(B.2): the endpoints and all x in (lo, hi) with c x ∈ ℤ."""
    cs = [2, 2 * ALPHA, 2 * LAMBDA, 2 * H, 4 * ALPHA, 2 * (1 - ALPHA), 2 * (1 + ALPHA)]
    pts = {Fr(lo), Fr(hi)}
    for c in cs:
        k = floor(c * lo) + 1
        while Fr(k) / c < hi:
            pts.add(Fr(k) / c)
            k += 1
    return sorted(pts)


def integrate_affine_over_x3(fun, pts):
    """∫ fun(x) x⁻³ dx over [pts[0], pts[-1]], assuming fun is affine on each (pts[i], pts[i+1]).

    Affinity is checked at three interior points; the pieces are integrated as in (B.3)."""
    total = Fr(0)
    pieces = []
    for l, r in zip(pts, pts[1:]):
        xi, yi = (2 * l + r) / 3, (l + 2 * r) / 3
        a = (fun(yi) - fun(xi)) / (yi - xi)
        b = fun(xi) - a * xi
        for probe in ((l + r) / 2, (5 * l + r) / 6, (l + 5 * r) / 6):
            if fun(probe) != a * probe + b:
                raise AssertionError(f"not affine on [{l}, {r}]")
        piece = a * (1 / l - 1 / r) + b / 2 * (1 / l**2 - 1 / r**2)
        pieces.append((l, r, a, b, piece))
        total += piece
    return total, pieces


# ---------------------------------------------------------------------------------------------
# §5.2  The outer integrand


def R0(y):
    """(5.8)."""
    if Fr(1, 3) < y < Fr(1, 2):
        return 8 - 9 * y - 8 * ALPHA - 5 * min(ALPHA, 1 - 2 * y) - 5 * pos(1 + ALPHA - 3 * y)
    if Fr(1, 2) < y < 1:
        return (7 * (1 - y) - 6 * min(ALPHA, 1 - y) - 6 * pos(1 + ALPHA - 2 * y)
                + pos(1 + 4 * ALPHA - 2 * y))
    if y > 1:
        return Fr(0)
    raise ValueError(y)


def drank(y):
    """(5.9)."""
    if Fr(1, 3) < y < Fr(1, 2):
        return pos(1 + 4 * ALPHA - 3 * y - pos(1 + ALPHA - 3 * y))
    return Fr(0)


def Tout(y):
    """The outer integrand of (5.10) / Appendix B.2."""
    return (R0(y) - drank(y) - 2 * LAMBDA * floor(1 / y)
            + sum(pos(2 * LAMBDA - j * y) for j in range(1, 6)))


def integrate_affine(fun, pts):
    total = Fr(0)
    pieces = []
    for l, r in zip(pts, pts[1:]):
        xi, yi = (2 * l + r) / 3, (l + 2 * r) / 3
        c = (fun(yi) - fun(xi)) / (yi - xi)
        b = fun(xi) - c * xi
        for probe in ((l + r) / 2, (5 * l + r) / 6, (l + 5 * r) / 6):
            if fun(probe) != b + c * probe:
                raise AssertionError(f"not affine on [{l}, {r}]")
        pieces.append((l, r, b, c))
        total += b * (r - l) + c * (r * r - l * l) / 2
    return total, pieces


# ---------------------------------------------------------------------------------------------
# Data transcribed from the paper

TABLE3 = {
    3: Fr(26807, 161280),
    4: Fr(37383, 704000),
    5: Fr(37523, 8236800),
    6: Fr(-120923, 6552000),
    7: Fr(-10025233, 356428800),
    8: Fr(-110029309, 3348864000),
    9: Fr(-2278419487, 64465632000),
    10: Fr(-282415081, 7724640000),
    11: Fr(-3236921227, 87524236800),
    12: Fr(-3350220001, 90899827200),
    13: Fr(7424224373, 2217983040000),
    14: Fr(16775764609, 955086612480),
    15: Fr(369043847, 30810528000),
    16: Fr(651380108633, 86461373856000),
    17: Fr(472851276229, 119820121344000),
    18: Fr(4930060867, 4724197793280),
    19: Fr(-15199801, 11563552000),
}

TABLE4 = [  # (l, r, b, c)
    (Fr(1, 3), Fr(43, 120), Fr(279, 40), -9),
    (Fr(43, 120), Fr(37, 100), Fr(451, 40), -21),
    (Fr(37, 100), Fr(13, 30), Fr(377, 40), -16),
    (Fr(13, 30), Fr(37, 80), Fr(429, 40), -19),
    (Fr(37, 80), Fr(1, 2), Fr(17, 4), -5),
    (Fr(1, 2), Fr(43, 80), Fr(51, 10), -3),
    (Fr(43, 80), Fr(37, 60), Fr(231, 20), -15),
    (Fr(37, 60), Fr(13, 20), Fr(97, 10), -12),
    (Fr(13, 20), Fr(37, 40), Fr(42, 5), -10),
    (Fr(37, 40), Fr(1), Fr(1), -2),
    (Fr(1), Fr(37, 20), Fr(37, 20), -1),
]

INNER_3_20 = Fr(322437603634266857629, 7535670527041937280000)  # (5.18)
A_STAR = Fr(9928298118277006344769, 7535670527041937280000)  # (5.19)
I_OUT = Fr(127751, 96000)  # (5.10)
TAIL_20 = Fr(-2689, 48000)  # (5.16)
PBAR = Fr(2923, 240)
U_BAR = Fr(-2733991, 2000000)  # (6.4)
A_200 = Fr(127125602969131786927559, 94195881588024216000000)
A_100000 = Fr(7756864096839411316755964319057, 5887242599251513500000000000000)
MARGIN_200 = Fr(3089837638249482469, 58872425992515135000)
MARGIN_100000 = Fr(29873543950273155160680943, 3679526624532195937500000000)


def A_M(M):
    """(5.20)."""
    return A_STAR + 7 * LAMBDA / M - (PBAR - Fr(1, 4)) / M**2 + Fr(32) / M**3


def main():
    print("== Quadratic coefficient identity (after (B.2))")
    check("2λ - 12λα + 2(H² - H - λ²) - 18α² + 6α = 0",
          2 * LAMBDA - 12 * LAMBDA * ALPHA + 2 * (H * H - H - LAMBDA**2) - 18 * ALPHA**2 + 6 * ALPHA == 0)

    print("\n== §5.1  R(x): definitions (5.4)-(5.6) vs closed form (5.12), (5.13), (B.1)")
    samples = [Fr(3) + Fr(k, 997) for k in range(0, 17 * 997, 7)] + [Fr(k, 40) for k in range(120, 2000)]
    bad = [x for x in samples if R_def(x) != R_closed(x)[0]]
    check(f"R_def = R_closed at {len(samples)} rational points in [3, 50)", not bad,
          f"first mismatch at x = {bad[0]}" if bad else "")
    qs = [R_closed(x)[2] for x in samples]
    check("(5.14): -1/2 ≤ Q(x) ≤ 13/8 at the sample points",
          min(qs) >= Fr(-1, 2) and max(qs) <= Fr(13, 8),
          f"observed range [{float(min(qs)):.4f}, {float(max(qs)):.4f}]")

    print("\n== Appendix B.1  ∫_3^20 R(x) x⁻³ dx")
    pts = inner_breakpoints(3, 20)
    check("(B.2) gives s = 143 intervals", len(pts) - 1 == 143, f"got {len(pts) - 1}")
    total, pieces = integrate_affine_over_x3(R_def, pts)
    check("R is affine on each interval of (B.2)", True)
    for j in range(3, 20):
        unit = sum(pc for l, r, a, b, pc in pieces if j <= l and r <= j + 1)
        check(f"Table 3, j = {j}", unit == TABLE3[j], f"computed {unit}")
    check("(5.18) ∫_3^20 R x⁻³ = 322437603634266857629/7535670527041937280000", total == INNER_3_20,
          f"computed {total}")
    check("Table 3 sums to (5.18)", sum(TABLE3.values()) == INNER_3_20)

    print("\n== Appendix B.2  the outer integral")
    ypts = sorted({Fr(1, 3), Fr(1, 2), Fr(1), 2 * LAMBDA, 1 - 2 * ALPHA, ALPHA,
                   (1 + ALPHA) / 3, (1 + 4 * ALPHA) / 3, (1 - ALPHA) / 2, (1 + ALPHA) / 2,
                   (1 + 4 * ALPHA) / 2, 1 - ALPHA} | {2 * LAMBDA / j for j in range(1, 6)})
    ypts = [y for y in ypts if Fr(1, 3) <= y <= 2 * LAMBDA]
    # (1 - 2α)... are only candidates; drop spurious ones by merging collinear neighbours
    total, pieces = integrate_affine(Tout, ypts)
    merged = []
    for l, r, b, c in pieces:
        if merged and merged[-1][2] == b and merged[-1][3] == c:
            merged[-1] = (merged[-1][0], r, b, c)
        else:
            merged.append((l, r, b, c))
    check("Table 4 (pieces, intercepts, slopes)", merged == [(l, r, Fr(b), Fr(c)) for l, r, b, c in TABLE4],
          "" if merged == TABLE4 else f"computed {merged}")
    check("I_out = 127751/96000 (5.10)", total == I_OUT, f"computed {total}")
    dint, _ = integrate_affine(drank, [y for y in ypts if y <= Fr(1, 2)])
    check("∫_{1/3}^{1/2} d(y) dy = 9/640", dint == Fr(9, 640), f"computed {dint}")

    print("\n== §5.3  tail constants")
    # P̄ is the mean of P(x) = 74 g(1-g) - λ f(1-f) over a period; mean of u(1-u) is 1/6.
    check("P̄ = (74 - λ)/6 = 2923/240", (74 - LAMBDA) / 6 == PBAR)
    Cmax_coeff = (74 / ALPHA + LAMBDA) / 36  # max|C| ≤ this / √3
    check("(74/α + λ)/36 = 118511/4320", Cmax_coeff == Fr(118511, 4320))
    check("118511/(4320√3) < 16  ⟺  118511² < 3·(16·4320)²", Cmax_coeff**2 < 3 * 16**2)
    # (5.16): -λ/T - P(T)/T² + P̄/T² + 2·16/T³ + 6·16/(3T³) + (13/8)/(2T²) at T = 20,
    # with P(20) = 37/2 and C(20) = 0.
    T = 20
    tail = -LAMBDA / T - Fr(37, 2) / T**2 + PBAR / T**2 + Fr(6 * 16, 3 * T**3) + Fr(13, 8) / (2 * T**2)
    check("P(20) = 74·(1/2)(1/2) = 37/2", 74 * Fr(1, 4) == Fr(37, 2))
    check("(5.16) upper bound at T = 20 equals -2689/48000", tail == TAIL_20, f"computed {tail}")
    check("(5.19) A* = I_out + (5.18) + (5.16)", A_STAR == I_OUT + INNER_3_20 + TAIL_20,
          f"I_out + (5.18) + (5.16) = {I_OUT + INNER_3_20 + TAIL_20}")
    check("A_200 (Appendix B.3)", A_M(200) == A_200, f"computed {A_M(200)}")
    check("A_100000 (Appendix B.3)", A_M(100000) == A_100000, f"computed {A_M(100000)}")

    print("\n== (7.2) final margins")
    m200 = -1600 * (A_200 + U_BAR) - Fr(139, 5)
    m1e5 = -1600 * (A_100000 + U_BAR) - Fr(7907, 100)
    check("-1600(A_200 + Ū) - 139/5 = 3089837638249482469/58872425992515135000",
          m200 == MARGIN_200, f"computed {m200}")
    check("  … and it is positive", m200 > 0, f"≈ {float(m200):.6f}")
    check("-1600(A_100000 + Ū) - 7907/100 (Appendix B.3)", m1e5 == MARGIN_100000, f"computed {m1e5}")
    check("  … and it is positive", m1e5 > 0, f"≈ {float(m1e5):.6f}")
    check("A_100000 + Ū < -79/1600 (C.7)", A_100000 + U_BAR < Fr(-79, 1600))
    print(f"\n   A_200 ≈ {float(A_200):.6f}, Ū ≈ {float(U_BAR):.6f}, A_200 + Ū ≈ {float(A_200 + U_BAR):.6f}")
    print(f"   so the claimed decay rate is K⁻² log Q_(K,200)(ζ(5)) ≤ {float(A_200 + U_BAR):.6f} eventually;")
    print(f"   the margin is {float(-(A_200 + U_BAR) / A_200) * 100:.2f}% of A_200.")

    print()
    if failures:
        print(f"{len(failures)} check(s) FAILED")
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
