# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Phase 6: generate `Zeta5/RData.lean`, the breakpoints of the limiting exponent R(x).

R(x) is the function `Zeta5.eR` of `Zeta5/RFun.lean`: -L_p(K, M) ≤ p R(K/p) + O(1) for every prime
p ≤ 2h with K/p < M. It is affine between consecutive points of the set (B.2) extended to the outer
range, x ∈ [20/37, 200]:

    x = k/c,  c ∈ {1, 2, 2α, 2λ, 2H, 4α, 2(1-α), 2(1+α), 1+α, 1+4α, α}.

The points are split into chunks; for each chunk the exact value of ∫ R(x) x⁻³ dx is rounded up to a
multiple of 10⁻¹⁵. The Lean kernel re-checks, chunk by chunk, that `eR` is affine on every interval
and that the exact integral is at most the rounded value (`Zeta5/RCheck.lean`), so the correctness
of this script does not matter for the proof.

Besides writing the file, the script checks that

* R agrees with the paper's R(x) of (5.4)-(5.6) on [3, 200) and with x T_out(1/x) of (5.8)-(5.10)
  on [20/37, 3), where T_out is the integrand of (5.10);
* the Lagrangian form of Γ used by `eR` agrees with (5.4) (it is the paper's Γ);
* ∫_{20/37}^3 R x⁻³ = I_out and ∫_3^20 R x⁻³ = (5.18);
* I_out + 6λ/200 + ∫_3^200 R x⁻³ ≤ A_200.

Run: `uv run scripts/gen_rdata.py`.
"""

import math
from fractions import Fraction as Fr
from pathlib import Path

import check_constants as cc

ROOT = Path(__file__).resolve().parent.parent
ALPHA, LAMBDA, H = cc.ALPHA, cc.LAMBDA, cc.H
M = 200
CHUNK = 190
SCALE = 10**15
fl = math.floor


def frac(x):
    return x - fl(x)


def d0(u):
    return min(u, 1 - u)


def pos(u):
    return u if u > 0 else Fr(0)


def N_fun(x):
    """(5.5), as `Zeta5.RFun.eN`."""
    m = fl(2 * LAMBDA * x)
    return 2 * LAMBDA * x * fl(x) - 12 * LAMBDA * x * fl(ALPHA * x) - 2 * (m * LAMBDA * x - Fr(m * (m + 1), 4))


def Gamma_lagrange(x):
    """`Zeta5.RFun.eGam`: μλx - ∫_0^{1/2} ⌊(6ℓ(αx, z) - ℓ(x, z) - 5 - μ)²/4⌋ dz."""
    k, f = fl(x), frac(x)
    kN, g = fl(ALPHA * x), frac(ALPHA * x)
    sK = 2 * fl(2 * f) - 1
    sN = 2 * fl(2 * g) - 1
    dK, dN = d0(f), d0(g)
    mu = 2 * fl(2 * H * x) - fl(2 * x) - 5 + (1 if frac(2 * x) < frac(2 * H * x) else 0)
    D = 12 * kN - 2 * k - mu
    phi = lambda e: fl(Fr(e * e, 4))
    mn, mx = min(dK, dN), max(dK, dN)
    integral = (phi(D) * mn + phi(D - sK) * (dN - mn) + phi(D + 6 * sN) * (dK - mn)
                + phi(D + 6 * sN - sK) * (Fr(1, 2) - mx))
    return mu * LAMBDA * x - integral


def R(x):
    """`Zeta5.eR`."""
    a = ALPHA
    if x < 1:
        g = Fr(0)
    elif x < 2:
        g = 7 * (x - 1) - 6 * (min(a * x, x - 1) + pos((1 + a) * x - 2)) + pos((1 + 4 * a) * x - 2)
    elif x < 3:
        g = (7 * (x - 1) - 12 * a * x - 5 * (min(a * x, x - 2) + pos((1 + a) * x - 3))
             + min(pos((1 + 4 * a) * x - 2), 1 + pos((1 + a) * x - 3)))
    else:
        g = -Gamma_lagrange(x)
    return g - N_fun(x)


def breakpoints():
    cs = [Fr(1), Fr(2), 2 * ALPHA, 2 * LAMBDA, 2 * H, 4 * ALPHA, 2 * (1 - ALPHA), 2 * (1 + ALPHA),
          1 + ALPHA, 1 + 4 * ALPHA, ALPHA]
    lo, hi = Fr(20, 37), Fr(M)
    pts = {lo, hi}
    for c in cs:
        k = fl(c * lo) + 1
        while Fr(k) / c < hi:
            pts.add(Fr(k) / c)
            k += 1
    return sorted(pts)


def main():
    pts = breakpoints()
    samples = [Fr(3) + Fr(k, 997) for k in range(0, 197 * 997, 13)]
    assert all(R(x) == cc.R_def(x) for x in samples), "R ≠ (5.6) on [3, 200)"
    assert all(Gamma_lagrange(x) == cc.Gamma(x) for x in samples[::10]), "Γ ≠ (5.4)"
    ysamples = [Fr(20, 37) + Fr(k, 9973) for k in range(1, 9973 * 3) if Fr(20, 37) + Fr(k, 9973) < 3]
    ysamples = [x for x in ysamples if x not in (1, 2)]
    assert all(R(x) == x * cc.Tout(1 / x) for x in ysamples), "R ≠ x T_out(1/x) on [20/37, 3)"

    total, pieces = cc.integrate_affine_over_x3(R, pts)
    out = sum(pc for l, r, a, b, pc in pieces if r <= 3)
    assert out == cc.I_OUT, out
    assert sum(pc for l, r, a, b, pc in pieces if l >= 3 and r <= 20) == cc.INNER_3_20
    limit = total + 6 * LAMBDA / M
    assert limit < cc.A_M(M)
    print(f"{len(pts) - 1} intervals; I_out + 6λ/200 + ∫_3^200 R x⁻³ = {float(limit):.9f}, "
          f"A_200 = {float(cc.A_M(M)):.9f}")

    chunks = []
    for i in range(0, len(pieces), CHUNK):
        ch = pieces[i:i + CHUNK]
        exact = sum(pc for *_, pc in ch)
        bound = Fr(math.ceil(exact * SCALE), SCALE)
        chunks.append((ch[0][0], [r for _, r, *_ in ch], bound))
    total_bound = sum(b for *_, b in chunks)
    assert total_bound + 6 * LAMBDA / M < cc.A_M(M)

    def q(x):
        return f"({x.numerator}, {x.denominator})"

    defs = []
    for k, (start, rs, bound) in enumerate(chunks):
        body = ",\n  ".join(", ".join(q(r) for r in rs[j:j + 6]) for j in range(0, len(rs), 6))
        defs.append(f'''/-- Chunk {k}: the points after `{start}`. -/
def rChunk{k} : List (ℕ × ℕ) := [
  {body}]

/-- The start of chunk {k}. -/
def rStart{k} : ℚ := {start.numerator} / {start.denominator}

/-- An upper bound for `∫ R(x) x⁻³ dx` over chunk {k}. -/
def rBound{k} : ℚ := {bound.numerator} / {bound.denominator}
''')
    text = f'''/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Data.Rat.Defs

/-!
# The breakpoints of `R(x)`

The {len(pts)} points `20/37 = x₀ < x₁ < ⋯ < x_{len(pts) - 1} = 200` between which the limiting
exponent `Zeta5.eR` is affine: `x = k/c` for
`c ∈ {{1, 2, 2α, 2λ, 2H, 4α, 2(1-α), 2(1+α), 1+α, 1+4α, α}}` (Appendix B, (B.2), extended to the
outer range). They come in {len(chunks)} chunks of at most
{CHUNK} intervals, each with an upper bound for the exact integral of `R(x) x⁻³` over it, rounded up
to a multiple of `10⁻¹⁵`.

This file is generated by `scripts/gen_rdata.py`. Its correctness does not matter for the proof:
`Zeta5/RCheck.lean` checks every interval and every bound.
-/

namespace Zeta5

/-- Numerator-denominator pairs to rationals. -/
def toQ (l : List (ℕ × ℕ)) : List ℚ := l.map fun p => (p.1 : ℚ) / p.2

''' + "\n".join(defs) + '''
end Zeta5
'''
    (ROOT / "Zeta5" / "RData.lean").write_text(text)
    print(f"wrote {len(chunks)} chunks; sum of bounds + 6λ/200 = {float(total_bound + 6 * LAMBDA / M):.9f}")


if __name__ == "__main__":
    main()
