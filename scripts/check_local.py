# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint>=0.7", "gmpy2"]
# ///
"""Phase 0: the determinant Δ_K(X) for small K, against §3-§4 (p-adic) and §6 (real).

For K = 40n the matrix G_K(X) of (2.4) is built exactly and Δ_K(X) = det G_K(X) ∈ ℚ[X] is computed
exactly (det(A + XB) = det B · charpoly(-B⁻¹A)).  Then:

* (2.9): the leading coefficient of Δ_K;
* (3.10) entrywise: every entry (K!)² μ_X(f_i f_j / D_K) of the matrix in (3.11) has Gauss valuation
  ≥ -6⌊log_p max(2K, d+1)⌋ - v_p(24) (Lemma 3.3), for every prime p (only for small n);
* (3.12): v_p^G(F_K) ≥ -6h⌊log_p 5K⌋ - h v_p(24) for every prime p;
* Proposition 4.3: v_p^G(Δ_K) ≥ γ_p^out for K/3 < p ≤ K (the hypotheses (4.9) do hold here), and
  v_p^G(Δ_K) ≥ 0 for p > K;
* Proposition 4.1 (inner range p ≤ K/3): the hypothesis K ≥ 200M² cannot hold for such small K, and
  the paper's L₀ = 4M + 10 with M ≥ 40 exceeds h.  We therefore run the allocation (4.4)-(4.8) with
  the smallest L₀ for which it is defined and the zero-source comparison in the proof goes through.
  This gives the *strongest* bound the argument could give.  A failure where the remaining hypotheses
  (p² > 5K and the degree bounds ≤ p + 1 of Lemma 3.1) hold would contradict the argument; failures
  where they do not hold are reported but are not counterexamples;
* Proposition 2.2 / 6.3: Δ_K(ζ(5)) > 0 (rigorous ball arithmetic) and the bounds (6.14), (6.15),
  (6.16); and the growth rates K⁻² log F_K(ζ(5)), K⁻² log of the denominator, and K⁻² log P_K(ζ(5))
  for the primitive integer polynomial P_K = Δ_K / cont(Δ_K).

Run: `uv run scripts/check_local.py [n ...] [--cache DIR]` (default n = 1 2 3, i.e. K = 40, 80, 120).
Computing Δ_K takes about 0.1 s, 3 s, 25 s, 2 min, 5 min, 13 min for n = 1, …, 6; with --cache the
exact polynomials are stored and reused.
"""

import argparse
import math
import os
import pickle
import sys
import time

import gmpy2
from flint import arb, ctx, fmpq, fmpq_mat, fmpq_poly, fmpz, fmpz_mat, fmpz_poly, nmod_mat

from zeta5_defs import (ALPHA, LAMBDA, D, G_matrices, S_K, delta_poly, factorial, hankel_moments,
                        leading_coeff_29, log_S_K, params, primes_upto, vp, vp_int, vp_SK, vpG)

U_BAR = fmpq(-2733991, 2000000)
LAMBDA_M0 = fmpq(-49173, 8000)
I_RHO = (fmpq(-2126593445148, 10**12), fmpq(-2126593445147, 10**12))  # (A.10)
C_STAR = (fmpq(2653035990340, 10**12), fmpq(2653035990341, 10**12))  # (A.10)

failures = []


def check(name, ok, detail=""):
    print(f"[{'OK' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    if not ok:
        failures.append(name)


def floor_log(p, x):
    k, q = 0, p
    while q <= x:
        k += 1
        q *= p
    return k


def gamma_out(p, K, N):
    """(4.14)."""
    v = K - p * (K // p)
    u = max(0, N + v - p + 1)
    tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)


def ell(A, a, p):
    return sum(1 for j in range(1, A + 1) if j % p in (a % p, (-a) % p))


def gamma_in(p, K, N, h, L0):
    """(4.4)-(4.8) with the zero-class dimension L₀ as a parameter; doubled weights are integers.

    Returns None when the allocation is undefined (negative dimensions), else (γ, info)."""
    m = (p - 1) // 2
    lK = {a: ell(K, a, p) for a in range(1, m + 1)}
    lN = {a: ell(N, a, p) for a in range(1, m + 1)}
    mN, mK = N // p, K // p
    rhs = h - L0 + 3 * (N - mN)
    if rhs < 0:
        return None
    T, E = divmod(rhs, m)
    order = sorted(lK, key=lambda a: -lK[a])
    eps = {a: 0 for a in lK}
    for a in order[:E]:
        eps[a] = 1
    b = {a: 3 * lN[a] for a in lK}
    L = {a: T - b[a] + eps[a] for a in lK}
    if min(L.values()) < 0:
        return None
    Z = {a: T + eps[a] for a in lK}
    # doubled weights 2w_{a,i} = 2i + 2b_a - ℓ_K(a) - 4 and (4.7)
    w2 = [2 * i + 2 * b[a] - lK[a] - 4 for a in lK for i in range(L[a])]
    Wstar2 = min(2 * Z[c] - lK[c] - 4 for c in lK)
    w2 += [min(4 * i + 12 * mN - 2 * mK + 1, Wstar2) for i in range(L0)]
    gamma = sum(w2)
    zero_source = 2 * (2 * L0 + 6 * mN - mK) + 1 >= max(2 * (Z[a] - 1) - lK[a] - 4 for a in lK)
    hyp = (p * p > 5 * K and max(2 * Z[a] for a in lK) <= p + 1 and 5 + 4 * L0 + 12 * mN <= p + 1)
    L[0] = L0
    return gamma, dict(zero_source=zero_source, hyp=hyp, L0=L0, L=L, b=b, lK=lK, mN=mN, mK=mK,
                       Wstar2=Wstar2)


def inner_entrywise(p, h, alloc, a_seq, b_seq):
    """The mechanism of the proof of Prop 4.1, entry by entry.

    In the basis (4.5) E_{a,i} = ∏_{c ≠ a} (t + c²)^{L_c} (t + a²)^i, check that
    * the basis is ℤ_p-unimodular;
    * each entry μ_X(D_N⁶ E_{a,i} E_{b,j} / D_K) has Gauss valuation ≥ w_{a,i} + w_{b,j};
    * and even ≥ min over sources c of the bounds (4.2), (4.3).
    Computed p-adically: the Hankel symbols are reduced modulo a sufficiently high power of p."""
    L, bb, lK, mN, mK = alloc["L"], alloc["b"], alloc["lK"], alloc["mN"], alloc["mK"]
    classes = sorted(L)
    full = fmpz_poly([1])
    for c in classes:
        full *= fmpz_poly([c * c, 1]) ** L[c]
    rows, keys = [], []
    for a in classes:
        for i in range(L[a]):
            E = divmod(full, fmpz_poly([a * a, 1]) ** (L[a] - i))[0]
            cf = [int(x) for x in E.coeffs()]
            rows.append(cf + [0] * (h - len(cf)))
            keys.append((a, i))
    unimodular = nmod_mat(rows, p).rank() == h

    def w2(a, i):
        if a == 0:
            return min(4 * i + 12 * mN - 2 * mK + 1, alloc["Wstar2"])
        return 2 * i + 2 * bb[a] - lK[a] - 4

    def half2(a, i, c):  # doubled half-weights at the source c, from (4.2) and (4.3)
        nu = i if a == c else L[c]
        if c == 0:
            return 2 * (2 * nu + 6 * mN - mK) + 1
        return 2 * nu + 2 * bb[c] - lK[c] - 4

    ws = [w2(a, i) for a, i in keys]
    halves = [[half2(a, i, c) for c in classes] for a, i in keys]
    # every bound below is at most max(doubled weight), so this precision resolves all of them
    need = max(max(ws), max(max(hs) for hs in halves))
    vals = [vp(x, p) for x in list(a_seq) + list(b_seq) if x != 0]
    S = -min(vals)  # shift making every Hankel symbol p-integral
    prec = S + need + 4
    mod = p**prec

    def red(x):
        if x == 0:
            return 0
        num, den = int(x.p) * p**S, int(x.q)
        vd = vp_int(den, p)
        num //= p**vd
        den //= p**vd
        return num * pow(den, -1, mod) % mod

    U = fmpz_mat([[r % mod for r in row] for row in rows])
    out = []
    for seq in (a_seq, b_seq):
        H = fmpz_mat(h, h, [red(seq[i + j]) for i in range(h) for j in range(h)])
        out.append((U * H * U.transpose()).entries())
    ok_w = ok_mech = True
    tight = 0
    for idx in range(h * h):
        r, c = divmod(idx, h)
        v = None
        for M in out:
            x = int(M[idx]) % mod
            if x:
                vx = vp_int(x, p) - S
                v = vx if v is None else min(v, vx)
        if v is None:
            continue  # zero to the working precision, i.e. valuation ≥ prec - S
        ok_w &= 2 * v >= ws[r] + ws[c]
        mech = min(hr + hc for hr, hc in zip(halves[r], halves[c]))
        ok_mech &= 2 * v >= mech
        tight += 2 * v < ws[r] + ws[c] + 2
    return unimodular, ok_w, ok_mech, tight


def compute_delta(n, cache):
    path = cache and os.path.join(cache, f"delta_{n}.pkl")
    if path and os.path.exists(path):
        with open(path, "rb") as f:
            return fmpq_poly([fmpq(a, b) for a, b in pickle.load(f)]), None
    A, B = G_matrices(n)
    Dl = delta_poly(A, B)
    if path:
        os.makedirs(cache, exist_ok=True)
        with open(path, "wb") as f:
            pickle.dump([(int(c.p), int(c.q)) for c in Dl.coeffs()], f)
    return Dl, (A, B)


def q_basis(h):
    """Coefficient matrix of q_0 = 1, q_i(t) = (-1)^i 2t D_{i-1}(t) / (2i)! (§3.3)."""
    rows = [[fmpq(1)] + [fmpq(0)] * (h - 1)]
    for i in range(1, h):
        q = fmpq_poly([0, 2]) * D(i - 1) * fmpq((-1) ** i, factorial(2 * i))
        c = q.coeffs()
        rows.append(c + [fmpq(0)] * (h - len(c)))
    return fmpq_mat(rows)


def check_lemma33(n, A, B):
    """(3.10) for every entry of the matrix in (3.11)."""
    K, N, h = params(n)
    Q = q_basis(h)
    c = fmpq(factorial(K) ** 2, factorial(N) ** 12)
    Af = Q * A * Q.transpose() * c
    Bf = Q * B * Q.transpose() * c
    # the determinant of (3.11) is F_K = S_K Δ_K; compare leading coefficients
    check("(3.11) and (2.5): [X^h] det[(K!)² μ_X(f_i f_j / D_K)] = S_K · [X^h] Δ_K",
          Bf.det() == S_K(n) * leading_coeff_29(n))
    worst = {}
    lcm = gmpy2.mpz(1)
    for i in range(h):
        for j in range(h):
            lcm = gmpy2.lcm(lcm, gmpy2.lcm(int(Af[i, j].q), int(Bf[i, j].q)))
    ok = True
    for p in primes_upto(5 * K):
        if lcm % p:
            continue
        for i in range(h):
            for j in range(h):
                d = 5 + 12 * N + 2 * i + 2 * j  # degree of x⁵ f_i(-x²) f_j(-x²)
                bound = -6 * floor_log(p, max(2 * K, d + 1)) - (vp_int(24, p) or 0)
                v = vpG([Af[i, j], Bf[i, j]], p)
                if v is not None and v < bound:
                    ok = False
                    worst.setdefault(p, (i, j, v, bound))
    rest = lcm
    for p in primes_upto(5 * K):
        rest = gmpy2.remove(rest, p)[0]
    check("(3.10) entrywise in the basis f_i of (3.11), all primes", ok and rest == 1,
          f"violations {worst}" if worst else "")


def analyse(n, cache, entrywise, inner_entries):
    K, N, h = params(n)
    print(f"\n==================== n = {n}: K = {K}, N = {N}, h = {h}")
    t0 = time.time()
    Dl, AB = compute_delta(n, cache)
    print(f"   Δ_K computed in {time.time() - t0:.1f}s")
    coeffs = Dl.coeffs()
    check("deg Δ_K = h and (2.9) leading coefficient",
          Dl.degree() == h and Dl.leading_coefficient() == leading_coeff_29(n))
    if entrywise:
        if AB is None:
            AB = G_matrices(n)
        check_lemma33(n, *AB)

    # ---- p-adic
    print("   p  | v_p^G(Δ) | v_p(S_K) | bound (claim)")
    ok312 = ok_out = ok_big = ok_in = ok_uni = ok_inw = ok_mech = True
    notes = []
    hank = None
    n_entry = 0
    for p in primes_upto(2 * h):
        vD = vpG(coeffs, p)
        vS = vp_SK(n, p)
        b312 = -6 * h * floor_log(p, 5 * K) - h * (vp_int(24, p) or 0)
        ok312 &= vD + vS >= b312
        line = f"  {p:4d} | {vD:8d} | {vS:8d} | "
        if p > K:
            ok_big &= vD >= 0
            line += "0 (Prop 4.3, p > K)"
        elif 3 * p > K:
            c49 = p >= 7 and p <= K < 3 * p and p * p > 2 * K and 2 * N < p and 5 * N <= 2 * p - 2
            g = gamma_out(p, K, N)
            ok_out &= (not c49) or vD >= g
            line += f"{g} (γ_out, Prop 4.3; (4.9) {'holds' if c49 else 'fails'})" + ("" if vD >= g else "  VIOLATED")
        elif p >= 7:
            res = None
            for L0 in range(h + 1):
                r = gamma_in(p, K, N, h, L0)
                if r and r[1]["zero_source"]:
                    res = r
                    break
            if res is None:
                line += "(no admissible allocation)"
            else:
                g, info = res
                line += f"{g} (γ_in, L₀ = {info['L0']}; hypotheses {'hold' if info['hyp'] else 'fail'})"
                if vD < g:
                    line += "  VIOLATED"
                    if info["hyp"]:
                        ok_in = False
                    else:
                        notes.append(p)
                if info["hyp"] and inner_entries:
                    if hank is None:
                        hank = hankel_moments(n)
                    uni, ok_w, ok_m, tight = inner_entrywise(p, h, info, *hank)
                    ok_uni &= uni
                    ok_inw &= ok_w
                    ok_mech &= ok_m
                    line += f"; entrywise {'OK' if ok_w and ok_m else 'VIOLATED'} ({tight} entries sharp)"
                    n_entry += 1
        else:
            line += "(3.12) only"
        print(line)
    check("(3.12) v_p^G(F_K) ≥ -6h⌊log_p 5K⌋ - h v_p(24) for all p ≤ 2h", ok312)
    lcm = gmpy2.mpz(1)
    for c in coeffs:
        lcm = gmpy2.lcm(lcm, int(c.q))
    for p in primes_upto(K):
        lcm = gmpy2.remove(lcm, p)[0]
    check("Prop 4.3: v_p^G(Δ_K) ≥ 0 for every prime p > K", ok_big and lcm == 1)
    check("Prop 4.3: v_p^G(Δ_K) ≥ γ_p^out for K/3 < p ≤ K", ok_out)
    check("Prop 4.1 (generalised allocation) wherever its hypotheses hold", ok_in)
    if n_entry:
        check(f"Prop 4.1 proof, entrywise at {n_entry} primes: basis (4.5) is ℤ_p-unimodular", ok_uni)
        check("Prop 4.1 proof, entrywise: v_p^G(entry) ≥ w_(a,i) + w_(b,j)", ok_inw)
        check("Prop 4.1 proof, entrywise: v_p^G(entry) ≥ min over sources of (4.2), (4.3)", ok_mech)
    if notes:
        print(f"   note: the generalised inner bound fails at p = {notes}, where p² > 5K or the degree"
              " bounds of Lemma 3.1 fail; these are outside the scope of Prop 4.1.")

    # ---- real
    maxbits = max(max(int(c.p).bit_length(), int(c.q).bit_length()) for c in coeffs if c != 0)
    ctx.prec = maxbits + 3000
    z5 = arb(5).zeta()
    val = arb(0)
    for c in reversed(coeffs):
        val = val * z5 + arb(c)
    check("Δ_K(ζ(5)) > 0 (Prop 2.2), rigorous", val > 0)
    logD = val.log()
    g = gmpy2.mpz(0)
    l = gmpy2.mpz(1)
    for c in coeffs:
        if c != 0:
            g = gmpy2.gcd(g, int(c.p))
            l = gmpy2.lcm(l, int(c.q))
    log_cont = arb(fmpz(int(g))).log() - arb(fmpz(int(l))).log()
    ctx.prec = 128
    logD, log_cont = arb(logD.mid()), arb(log_cont.mid())
    lS = log_S_K(n)
    logF = lS + logD
    lK = arb(K).log()
    K2 = K * K
    b616 = arb(U_BAR) * K2 + 24 * K * lK + 200 * K
    b614 = (2 * h * (h + 6 * N - K) * lK + (arb(LAMBDA_M0) - arb(I_RHO[0])) * K2 + 18 * h * lK + 160 * h)
    b615 = ((2 * arb(LAMBDA) - 12 * arb(ALPHA) * arb(LAMBDA) - 2 * arb(LAMBDA) ** 2) * K2 * lK
            + arb(C_STAR[1]) * K2 + 6 * h * lK + 6 * h)
    check("(6.14) log Δ_K(ζ(5)) ≤ 2h(h+6N-K) log K + (λM₀ - I(ρ))K² + 18h log K + 160h", logD < b614,
          f"{float(logD.mid()):.1f} ≤ {float(b614.mid()):.1f}")
    check("(6.15) log S_K ≤ (2λ - 12αλ - 2λ²)K² log K + C*K² + 6h log K + 6h", lS < b615,
          f"{float(lS.mid()):.1f} ≤ {float(b615.mid()):.1f}")
    check("(6.16) log F_K(ζ(5)) ≤ ŪK² + 24K log K + 200K (Prop 6.3)", logF < b616,
          f"{float(logF.mid()):.1f} ≤ {float(b616.mid()):.1f}")
    return dict(K=K, real=float(logF.mid()) / K2, denom=float((-(lS + log_cont)).mid()) / K2,
                prim=float((logD - log_cont).mid()) / K2, prim_abs=float((logD - log_cont).mid()))


def inner_only(n):
    """Only the entrywise check of the proof of Prop 4.1; needs the Hankel symbols but not Δ_K,
    so it reaches larger K (and larger x = K/p) than the determinant checks."""
    K, N, h = params(n)
    print(f"\n==================== n = {n}: K = {K}, h = {h} (entrywise Prop 4.1 only)")
    t0 = time.time()
    hank = hankel_moments(n)
    print(f"   Hankel symbols computed in {time.time() - t0:.1f}s")
    ok = True
    tested = []
    for p in primes_upto(K // 3):
        if p < 7:
            continue
        res = None
        for L0 in range(h + 1):
            r = gamma_in(p, K, N, h, L0)
            if r and r[1]["zero_source"]:
                res = r
                break
        if res is None or not res[1]["hyp"]:
            continue
        uni, ok_w, ok_m, tight = inner_entrywise(p, h, res[1], *hank)
        ok &= uni and ok_w and ok_m
        tested.append(f"{p} (x = {K / p:.2f}, {tight} sharp)")
    print("   primes: " + ", ".join(tested))
    check(f"Prop 4.1 proof, entrywise at {len(tested)} primes (unimodular basis, row weights, (4.2)/(4.3))",
          ok and bool(tested))


def extrapolate(rows):
    """Fit c + a log K / K + b / K to K⁻² log F_K(ζ(5)) at the last three K and return c.

    Only the real part is smooth enough in K for this; the arithmetic columns fluctuate with the
    residues of K modulo small primes."""
    if len(rows) < 3:
        return None
    pts = rows[-3:]
    Mx = [[1.0, math.log(r["K"]) / r["K"], 1.0 / r["K"]] for r in pts]

    def det3(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))

    ys = [r["real"] for r in pts]
    return det3([[y] + row[1:] for y, row in zip(ys, Mx)]) / det3(Mx)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", nargs="*", type=int, default=[1, 2, 3])
    ap.add_argument("--cache", default=None)
    ap.add_argument("--entrywise-max-n", type=int, default=2,
                    help="check Lemma 3.3 entrywise for n up to this value (default 2)")
    ap.add_argument("--no-inner-entrywise", action="store_true",
                    help="skip the entrywise check of the proof of Prop 4.1")
    ap.add_argument("--inner-only", action="store_true",
                    help="run only the entrywise check of Prop 4.1 (no determinant)")
    args = ap.parse_args()
    if args.inner_only:
        for n in args.n:
            inner_only(n)
        print()
        if failures:
            print(f"{len(failures)} check(s) FAILED")
            sys.exit(1)
        print("all checks passed")
        return
    rows = [analyse(n, args.cache, n <= args.entrywise_max_n, not args.no_inner_entrywise)
            for n in args.n]

    print("\n==================== growth rates (K⁻² log)")
    print("         F_K(ζ(5))  denominator of F_K  P_K(ζ(5)) = Δ_K(ζ(5)) / cont Δ_K")
    for r in rows:
        print(f"  K={r['K']:<4d} {r['real']:+.5f}   {r['denom']:+.5f}             {r['prim']:+.5f}"
              f"   (log P_K(ζ(5)) = {r['prim_abs']:.1f})")
    ex = extrapolate(rows)
    if ex is not None:
        print(f"  K⁻² log F_K(ζ(5)) extrapolated with c + a log K/K + b/K (last three K): {ex:+.4f}")
    print(f"  paper: Ū = {float(U_BAR):+.5f}; denominators ≤ A_M, with A_M → A* ≈ +1.31751 as M → ∞"
          f" (A_200 ≈ +1.34959); A_200 + Ū ≈ -0.01741")

    print()
    if failures:
        print(f"{len(failures)} check(s) FAILED")
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
