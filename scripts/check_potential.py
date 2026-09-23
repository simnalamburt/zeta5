# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint>=0.7"]
# ///
"""Phase 0: Appendix A of the paper (Lemma 6.1).

* Table 1 sanity: Σ c_j = 37/40, nesting, lengths > 1/225, support in (0, 2).
* (A.2), (6.3), (A.10), (6.4): I(ρ), C* and λM₀ - I(ρ) + C* < Ū, in rigorous ball arithmetic (arb).
* (A.5) against the integral definition (6.1) of V (numerical quadrature, non-rigorous).
* The location of the minimum of V: Φ'(√q₋) < 0 < Φ'(√q₊), and the sign change of Φ'' at 711/880.
* Table 2 is a partition of [0, 2], and (A.9) B(l, r) < -6645002/10⁶ < -1329/200 on every interval,
  rigorously (arb).
* (6.8) on [2, ∞).
* Precision experiment for Phase 4: the smallest b such that dyadic enclosures with denominator 2^b
  of each log/arctan/sqrt/π (the Lean strategy) still prove (A.9) with -1329/200 on every interval.

Run: `uv run scripts/check_potential.py`.
"""

import math
import sys
from fractions import Fraction as Fr

from flint import arb, ctx, fmpq

ALPHA = Fr(3, 40)
LAMBDA = Fr(37, 40)
M0 = Fr(-1329, 200)
M0_STRONG = Fr(-6645002, 10**6)
U_BAR = Fr(-2733991, 2000000)

# Table 1: 10¹² a_j, 10¹² b_j, 10¹² c_j
TABLE1 = [
    (3906748086, 8992695531, 10515596180),
    (2312248264, 15340997855, 29471737793),
    (1402286665, 25730180724, 42934365099),
    (881725356, 41909578246, 58204231966),
    (578197906, 65851089563, 69037621310),
    (396324613, 99481037884, 78873099189),
    (283911191, 144325727458, 84856120711),
    (212206188, 201105762729, 88396082127),
    (165097686, 269345996903, 88303382125),
    (133347132, 347089554156, 85472321255),
    (111522114, 430806704415, 78899184238),
    (96349355, 515561896511, 70353471918),
    (85815639, 595448778546, 58838976615),
    (78667711, 664241383483, 44421321106),
    (74129565, 716160577112, 30462865791),
    (71741310, 746637295669, 5959622577),
]
AS = [Fr(a, 10**12) for a, _, _ in TABLE1]
BS = [Fr(b, 10**12) for _, b, _ in TABLE1]
CS = [Fr(c, 10**12) for _, _, c in TABLE1]

Q_MINUS = Fr(59205077, 10**10)
Q_PLUS = Fr(59205079, 10**10)

# Table 2: rows (j, d, k-ranges); a range (k0, k1) includes both endpoints.
TABLE2 = [
    (0, 1, [(0, 0)]), (0, 2, [(2, 3)]),
    (1, 0, [(0, 0)]), (2, 0, [(0, 0)]), (3, 0, [(0, 0)]), (4, 0, [(0, 0)]),
    (5, 0, [(0, 0)]), (6, 0, [(0, 0)]), (7, 0, [(0, 0)]), (8, 0, [(0, 0)]),
    (9, 1, [(0, 1)]), (10, 1, [(0, 1)]), (11, 1, [(0, 1)]),
    (12, 1, [(0, 0)]), (12, 2, [(2, 3)]),
    (13, 2, [(0, 3)]), (14, 2, [(0, 3)]),
    (15, 1, [(0, 0)]), (15, 2, [(2, 3)]),
    (16, 0, [(0, 0)]), (17, 0, [(0, 0)]), (18, 0, [(0, 0)]),
    (19, 1, [(1, 1)]), (19, 3, [(0, 0), (2, 3)]), (19, 4, [(2, 3)]),
    (20, 2, [(3, 3)]), (20, 3, [(4, 5)]), (20, 4, [(0, 1), (6, 7)]), (20, 5, [(4, 11)]),
    (21, 2, [(3, 3)]), (21, 3, [(5, 5)]), (21, 4, [(0, 0), (7, 9)]), (21, 5, [(2, 4), (10, 13)]),
    (21, 6, [(10, 19)]),
    (22, 3, [(5, 7)]), (22, 4, [(0, 0), (8, 9)]), (22, 5, [(2, 3), (12, 15)]), (22, 6, [(8, 23)]),
    (23, 3, [(6, 7)]), (23, 4, [(9, 11)]), (23, 5, [(0, 2), (14, 17)]), (23, 6, [(6, 13), (19, 27)]),
    (23, 7, [(28, 37)]),
    (24, 3, [(6, 7)]), (24, 4, [(10, 11)]), (24, 5, [(0, 2), (15, 19)]), (24, 6, [(6, 11), (22, 29)]),
    (24, 7, [(24, 43)]),
    (25, 3, [(7, 7)]), (25, 4, [(10, 13)]), (25, 5, [(0, 2), (16, 19)]), (25, 6, [(6, 11), (24, 31)]),
    (25, 7, [(24, 47)]),
    (26, 3, [(7, 7)]), (26, 4, [(11, 13)]), (26, 5, [(0, 2), (17, 21)]), (26, 6, [(6, 11), (25, 33)]),
    (26, 7, [(24, 49)]),
    (27, 4, [(11, 15)]), (27, 5, [(0, 2), (17, 21)]), (27, 6, [(6, 11), (26, 33)]), (27, 7, [(24, 51)]),
    (28, 4, [(12, 15)]), (28, 5, [(0, 2), (18, 23)]), (28, 6, [(6, 11), (27, 35)]), (28, 7, [(24, 53)]),
    (29, 4, [(13, 15)]), (29, 5, [(0, 2), (19, 25)]), (29, 6, [(6, 12), (27, 37)]), (29, 7, [(26, 53)]),
    (30, 4, [(13, 15)]), (30, 5, [(0, 2), (20, 25)]), (30, 6, [(6, 14), (26, 39)]), (30, 7, [(30, 51)]),
    (31, 4, [(14, 15)]), (31, 5, [(0, 2), (20, 27)]), (31, 6, [(6, 39)]),
    (32, 4, [(15, 15)]), (32, 5, [(0, 4), (19, 29)]), (32, 6, [(10, 37)]),
    (33, 4, [(0, 0), (15, 15)]), (33, 5, [(2, 29)]),
    (34, 2, [(2, 3)]), (34, 3, [(3, 3)]), (34, 4, [(3, 5)]), (34, 5, [(4, 5)]), (34, 6, [(5, 7)]),
    (34, 7, [(6, 9)]), (34, 8, [(7, 11)]), (34, 9, [(5, 13)]), (34, 10, [(0, 9)]),
]

failures = []


def check(name, ok, detail=""):
    print(f"[{'OK' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        failures.append(name)


def A_points():
    """The partition points A_0, …, A_35 of Appendix A.3."""
    A = [Fr(0)] + [AS[16 - j] for j in range(1, 17)] + [Q_MINUS, Q_PLUS] + BS + [Fr(2)]
    assert len(A) == 36
    return A


def table2_intervals():
    A = A_points()
    out = []
    for j, d, ranges in TABLE2:
        for k0, k1 in ranges:
            for k in range(k0, k1 + 1):
                l = A[j] + (A[j + 1] - A[j]) * Fr(k, 2**d)
                r = A[j] + (A[j + 1] - A[j]) * Fr(k + 1, 2**d)
                out.append(((j, d, k), l, r))
    return out


# ---------------------------------------------------------------------------------------------
# Rigorous evaluation with arb balls


def A(x):
    return arb(fmpq(x.numerator, x.denominator))


def U_unit_arb(a, b, t):
    """(A.1) for rational a < b and rational t."""
    if a <= t <= b:
        return A((b - a) / 4).log()
    m = (a + b) / 2
    s = A((t - a) * (t - b)).sqrt()
    return ((A(abs(t - m)) + s) / 2).log()


def U_rho_arb(t):
    return sum((A(c) * U_unit_arb(a, b, t) for a, b, c in zip(AS, BS, CS)), arb(0))


def V_arb(t):
    """(A.5); V(0) = -12α log α - 2 + 12α."""
    al = A(ALPHA)
    if t == 0:
        return -12 * al * al.log() - 2 + 12 * al
    st = A(t).sqrt()
    return ((A(1 + t)).log() - 6 * al * A(t + ALPHA**2).log() - 2 + 12 * al
            + 2 * st * (arb.pi() + (1 / st).atan() - 6 * (al / st).atan()))


def V_star_arb():
    """(A.6)."""
    al = A(ALPHA)
    sp, sm = A(Q_PLUS).sqrt(), A(Q_MINUS).sqrt()
    return (A(1 + Q_MINUS).log() - 6 * al * A(Q_PLUS + ALPHA**2).log() - 2 + 12 * al
            + 2 * sp * (arb.pi() + (1 / sp).atan() - 6 * (al / sm).atan()))


def dPhi_arb(y):
    """Φ'(y) = 2(π + arctan(1/y) - 6 arctan(α/y))."""
    return 2 * (arb.pi() + (1 / y).atan() - 6 * (A(ALPHA) / y).atan())


# ---------------------------------------------------------------------------------------------
# Emulation of the Lean strategy: every transcendental value is replaced by a dyadic enclosure
# with denominator 2^bits, and the rest is exact rational interval arithmetic.


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(Fr(o))
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Iv) else Iv(Fr(o))))

    def __rsub__(self, o):
        return Iv(Fr(o)) - self

    def __mul__(self, o):
        o = o if isinstance(o, Iv) else Iv(Fr(o))
        ps = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Iv(min(ps), max(ps))

    __rmul__ = __mul__


class Dyadic:
    """Monotone transcendental functions with outward-rounded dyadic enclosures."""

    def __init__(self, bits):
        self.bits = bits
        self.scale = 2**bits
        self.cache = {}

    def _enclose(self, key, value_arb):
        if key not in self.cache:
            w = value_arb * self.scale
            lo = int(w.lower().floor().unique_fmpz())
            hi = int(w.upper().ceil().unique_fmpz())
            self.cache[key] = (Fr(lo, self.scale), Fr(hi, self.scale))
        return self.cache[key]

    def log(self, x):
        return Iv(self._enclose(("log", x.lo), A(x.lo).log())[0],
                  self._enclose(("log", x.hi), A(x.hi).log())[1])

    def sqrt(self, x):
        return Iv(self._enclose(("sqrt", x.lo), A(x.lo).sqrt())[0],
                  self._enclose(("sqrt", x.hi), A(x.hi).sqrt())[1])

    def atan(self, x):
        return Iv(self._enclose(("atan", x.lo), A(x.lo).atan())[0],
                  self._enclose(("atan", x.hi), A(x.hi).atan())[1])

    def pi(self):
        lo, hi = self._enclose(("pi",), arb.pi())
        return Iv(lo, hi)

    def inv(self, x):  # exact
        return Iv(1 / x.hi, 1 / x.lo)


def U_unit_dy(D, a, b, t):
    if a <= t <= b:
        return D.log(Iv((b - a) / 4))
    m = (a + b) / 2
    s = D.sqrt(Iv((t - a) * (t - b)))
    return D.log((Iv(abs(t - m)) + s) * Fr(1, 2))


def U_rho_dy(D, t):
    r = Iv(Fr(0))
    for a, b, c in zip(AS, BS, CS):
        r = r + c * U_unit_dy(D, a, b, t)
    return r


def V_dy(D, t):
    if t == 0:
        return -12 * ALPHA * D.log(Iv(ALPHA)) - 2 + 12 * ALPHA
    st = D.sqrt(Iv(t))
    paren = D.pi() + D.atan(D.inv(st)) - 6 * D.atan(ALPHA * D.inv(st))
    return (D.log(Iv(1 + t)) - 6 * ALPHA * D.log(Iv(t + ALPHA**2)) - 2 + 12 * ALPHA
            + 2 * st * paren)


def V_star_dy(D):
    sp, sm = D.sqrt(Iv(Q_PLUS)), D.sqrt(Iv(Q_MINUS))
    paren = D.pi() + D.atan(D.inv(sp)) - 6 * D.atan(ALPHA * D.inv(sm))
    # (A.6) multiplies by √q₊ because the parenthesis is negative.  At low precision its sign is not
    # certified (it is ≈ -10⁻⁸), so multiply by the whole range of √t instead; this is still a
    # valid lower bound for V on [q₋, q₊].
    return (D.log(Iv(1 + Q_MINUS)) - 6 * ALPHA * D.log(Iv(Q_PLUS + ALPHA**2)) - 2 + 12 * ALPHA
            + 2 * Iv(sm.lo, sp.hi) * paren)


def B_upper_dy(D, l, r, Ucache):
    for t in (l, r):
        if t not in Ucache:
            Ucache[t] = U_rho_dy(D, t)
    Umax = max(Ucache[l].hi, Ucache[r].hi)
    if r <= Q_MINUS:
        Vlo = V_dy(D, r).lo
    elif l >= Q_PLUS:
        Vlo = V_dy(D, l).lo
    else:
        Vlo = V_star_dy(D).lo
    return 2 * Umax - Vlo


def main():
    ctx.prec = 256

    print("== Table 1")
    check("Σ c_j = 37/40", sum(CS) == LAMBDA)
    check("0 < a_16 < … < a_1 < b_1 < … < b_16 < 2",
          0 < AS[15] and all(AS[i + 1] < AS[i] for i in range(15)) and AS[0] < BS[0]
          and all(BS[i] < BS[i + 1] for i in range(15)) and BS[15] < 2)
    check("b_j - a_j > 1/225", all(b - a > Fr(1, 225) for a, b in zip(AS, BS)),
          f"min length {float(min(b - a for a, b in zip(AS, BS))):.6f}, 1/225 ≈ {1/225:.6f}")
    check("c_j > 0", all(c > 0 for c in CS))

    print("\n== (A.2), (6.3), (A.10), (6.4)")
    S = [Fr(0)]
    for c in CS:
        S.append(S[-1] + c)
    I_rho = sum((A(S[j + 1] ** 2 - S[j] ** 2) * A((b - a) / 4).log()
                 for j, (a, b) in enumerate(zip(AS, BS))), arb(0))
    check("-2126593445148/10¹² < I(ρ) < -2126593445147/10¹²",
          I_rho > A(Fr(-2126593445148, 10**12)) and I_rho < A(Fr(-2126593445147, 10**12)),
          f"I(ρ) = {I_rho.str(15)}")
    lam, al = A(LAMBDA), A(ALPHA)
    C_star = -2 * lam + 12 * al * lam * (1 - al.log()) + 3 * lam**2 - 2 * lam**2 * (2 * lam).log()
    check("2653035990340/10¹² < C* < 2653035990341/10¹²",
          C_star > A(Fr(2653035990340, 10**12)) and C_star < A(Fr(2653035990341, 10**12)),
          f"C* = {C_star.str(15)}")
    check("λM₀ = -49173/8000", LAMBDA * M0 == Fr(-49173, 8000))
    Uval = A(LAMBDA * M0) - I_rho + C_star
    check("λM₀ - I(ρ) + C* < -1366995564511/10¹² < Ū = -2733991/2000000",
          Uval < A(Fr(-1366995564511, 10**12)) and Fr(-1366995564511, 10**12) < U_BAR,
          f"λM₀ - I(ρ) + C* = {Uval.str(15)}")

    print("\n== (A.5) vs the integral definition (6.1) (numerical quadrature)")
    worst = 0.0
    for t in [1e-4, 1e-3, 0.0059, 0.05, 0.3, 1.0, 1.7]:
        n = 20000
        # midpoint rule for ∫_0^1 log(t+u²) du - 6 ∫_0^α log(t+u²) du; the integrands are smooth
        i1 = sum(math.log(t + ((k + 0.5) / n) ** 2) for k in range(n)) / n
        a = float(ALPHA)
        i2 = sum(math.log(t + (a * (k + 0.5) / n) ** 2) for k in range(n)) * a / n
        v_int = 2 * math.pi * math.sqrt(t) + i1 - 6 * i2
        ctx.prec = 64
        v_a5 = float(V_arb(Fr(t)).mid())
        ctx.prec = 256
        worst = max(worst, abs(v_int - v_a5))
    check("(A.5) agrees with (6.1) to quadrature accuracy", worst < 1e-6, f"max diff {worst:.2e}")

    print("\n== The minimum of V")
    check("Φ'(√q₋) < 0 < Φ'(√q₊)",
          dPhi_arb(A(Q_MINUS).sqrt()) < 0 and dPhi_arb(A(Q_PLUS).sqrt()) > 0)
    y2 = Fr(711, 880)
    check("Φ''(y) = 0 at y² = 711/880", -2 / (1 + y2) + 12 * ALPHA / (ALPHA**2 + y2) == 0)
    sp, sm = A(Q_PLUS).sqrt(), A(Q_MINUS).sqrt()
    paren = arb.pi() + (1 / sp).atan() - 6 * (A(ALPHA) / sm).atan()
    check("the parenthesis in (A.6) is negative", paren < 0, f"{paren.str(6)}")
    vs = V_star_arb()
    vmin = min((V_arb(Q_MINUS + (Q_PLUS - Q_MINUS) * Fr(k, 64)) for k in range(65)),
               key=lambda x: float(x.mid()))
    check("V* ≤ min V on [q₋, q₊]", vs < vmin, f"V* = {vs.str(12)}, sampled min V = {vmin.str(12)}")

    print("\n== Table 2")
    ivs = table2_intervals()
    srt = sorted(ivs, key=lambda x: x[1])
    contiguous = srt[0][1] == 0 and srt[-1][2] == 2 and all(
        srt[i][2] == srt[i + 1][1] for i in range(len(srt) - 1))
    check("Table 2 partitions [0, 2]", contiguous, f"{len(ivs)} intervals")

    ctx.prec = 256
    Ucache = {}
    worst = None
    margins = []
    for key, l, r in ivs:
        for t in (l, r):
            if t not in Ucache:
                Ucache[t] = U_rho_arb(t)
        Umax_up = max(float(Ucache[l].upper().mid()), float(Ucache[r].upper().mid()))
        Uhi = Ucache[l] if Ucache[l].upper() > Ucache[r].upper() else Ucache[r]
        if r <= Q_MINUS:
            V = V_arb(r)
        elif l >= Q_PLUS:
            V = V_arb(l)
        else:
            V = vs
        B = 2 * Uhi - V
        ok = B < A(M0_STRONG)
        margins.append((float((A(M0) - B).mid()), key, l, r, ok))
    bad = [m for m in margins if not m[4]]
    check("(A.9) B(l, r) < -6645002/10⁶ on every interval (arb, 256 bits)", not bad,
          f"{len(bad)} failures" if bad else "")
    margins.sort()
    print("   tightest intervals, margin = -1329/200 - B(l, r):")
    for m, key, l, r, _ in margins[:8]:
        print(f"     (j,d,k) = {key}: [{float(l):.6f}, {float(r):.6f}]  margin {m:.3e}")
    print(f"   loosest margin {margins[-1][0]:.3f}")

    # dense sampling of 2U^ρ - V, to see how far (6.2) is from sharp
    ctx.prec = 64
    grid = [Fr(k, 20000) for k in range(0, 40001)]
    best = max(grid, key=lambda t: float((2 * U_rho_arb(t) - V_arb(t)).mid()))
    sup = float((2 * U_rho_arb(best) - V_arb(best)).mid())
    print(f"   sampled sup of 2U^ρ(t) - V(t) on [0, 2]: {sup:.7f} at t ≈ {float(best):.5f}"
          f" (M₀ = {float(M0):.7f})")
    ctx.prec = 256

    print("\n== (6.8) on [2, ∞)")
    f68 = lambda t: 1.3 * math.log(t) + 6 * float(ALPHA) ** 3 / t - 2 * math.pi * math.sqrt(t)
    ts = [2 * 1.01**k for k in range(2000)]
    check("(6.8) right-hand side at t = 2 is < M₀", f68(2) < float(M0), f"{f68(2):.4f}")
    check("(6.8) RHS + √t/K is decreasing on [2, ∞) (K ≥ 2, sampled)",
          all(f68(b) + math.sqrt(b) / 2 < f68(a) + math.sqrt(a) / 2 for a, b in zip(ts, ts[1:])))
    ctx.prec = 64
    grid = [2 + Fr(k, 2) for k in range(1200)]
    ok = all(float((2 * U_rho_arb(t) - V_arb(t)).mid()) <= f68(float(t)) for t in grid)
    ctx.prec = 256
    check("2U^ρ(t) - V(t) ≤ (6.8) RHS (sampled on [2, 601.5])", ok)

    print("\n== Precision needed for dyadic enclosures (Phase 4 planning)")
    ctx.prec = 400
    results = {}
    for bits in [12, 16, 20, 22, 24, 26, 28, 32, 40, 64]:
        D = Dyadic(bits)
        Uc = {}
        worst_weak = max(B_upper_dy(D, l, r, Uc) for _, l, r in ivs)
        results[bits] = worst_weak
        print(f"   bits = {bits:3d}: max_intervals B_upper = {float(worst_weak):.9f}"
              f"   < -1329/200: {worst_weak < M0}   < -6645002/10⁶: {worst_weak < M0_STRONG}")
    minimal = min((b for b, w in results.items() if w < M0), default=None)
    print(f"   smallest tested b proving (A.9) with -1329/200: {minimal}")

    print()
    if failures:
        print(f"{len(failures)} check(s) FAILED")
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
