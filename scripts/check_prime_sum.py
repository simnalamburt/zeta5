# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "gmpy2"]
# ///
"""Phase 0: the normalisation m_{K,M} of §5 at admissible (K, M).

For M = 40 the hypotheses K ≥ 200M² of Theorem 2.1 are met from K = 320000 on, so the exponents
L_p(K, M) of (5.1) can be computed exactly from (4.4)-(4.8), (4.14) and (5.3).  This script

* checks the side conditions used in the proofs of Propositions 4.1 and 4.3 (nonnegativity of the
  dimensions L_a, degree bounds ≤ p + 1, (4.9)) and that γ_p^in, γ_p^out are integers;
* measures the O_M(1) errors in (5.7) and in the outer limiting formula of §5.2, i.e. how far
  γ_p^in, v_p(S_K), γ_p^out are from pΓ(K/p), pN(K/p), -K(R₀(p/K) - d(p/K));
* computes K⁻² log m_{K,M} exactly and compares it with the limit I_out + 6λ/M + ∫_3^M R x⁻³ dx of
  (5.11) and with the paper's bound A_M of (5.20).

Run: `uv run scripts/check_prime_sum.py [K] [M]` (default K = 320000, M = 40).
"""

import math
import sys
from fractions import Fraction as Fr

import gmpy2
import numpy as np

from check_constants import (A_M, I_OUT, LAMBDA, Gamma, Nfun, R0, R_def, drank, inner_breakpoints,
                             integrate_affine_over_x3)


def primes_upto(m):
    sieve = np.ones(m + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return [int(p) for p in np.nonzero(sieve)[0]]


def vp_factorial(m, p):
    s, q = 0, p
    while q <= m:
        s += m // q
        q *= p
    return s


def vp_int(x, p):
    return int(gmpy2.remove(gmpy2.mpz(x), p)[1]) if x else None


def floor_log(p, x):
    k, q = 0, p
    while q <= x:
        k += 1
        q *= p
    return k


def vp_SK(K, N, h, p):
    """(5.3).  Σ_{i<h} v_p((2i)!) is summed in closed form: Σ_{i=1}^{h-1} ⌊2i/q⌋."""
    def sum_floor_2i(q):
        # Σ_{i=1}^{h-1} ⌊2i/q⌋ = Σ_{k≥1} #{1 ≤ i ≤ h-1 : 2i ≥ kq}
        s, k = 0, 1
        while k * q <= 2 * (h - 1):
            s += (h - 1) - (k * q + 1) // 2 + 1
            k += 1
        return s
    r = 2 * h * vp_factorial(K, p) - 12 * h * vp_factorial(N, p)
    q = p
    while q <= 2 * (h - 1):
        r -= 2 * sum_floor_2i(q)
        q *= p
    return r + (h - 1) * (vp_int(4, p) or 0)


def ell_vec(A, p):
    """ℓ_A(a) for a = 1..(p-1)/2: #{1 ≤ j ≤ A : j ≡ ±a (mod p)}."""
    a = np.arange(1, (p - 1) // 2 + 1, dtype=np.int64)
    cnt = lambda r: np.where(A >= r, (A - r) // p + 1, 0)
    return cnt(a) + cnt(p - a)


def gamma_in(p, K, N, h, M):
    """(4.4)-(4.8).  Returns (γ_p^in, side-condition report)."""
    m = (p - 1) // 2
    L0 = 4 * M + 10
    lK, lN = ell_vec(K, p), ell_vec(N, p)
    mN, mK = N // p, K // p
    T, E = divmod(h - L0 + 3 * (N - mN), m)
    b = 3 * lN
    # the first E classes in decreasing order of ℓ_K get ε = 1; ℓ_K takes two consecutive values
    order = np.argsort(-lK, kind="stable")
    eps = np.zeros(m, dtype=np.int64)
    eps[order[:E]] = 1
    L = T - b + eps
    Z = T + eps
    # 2 Σ_{i<L_a} (i + b_a - (ℓ_K(a)+4)/2) = L_a (L_a - 1) + L_a (2 b_a - ℓ_K(a) - 4)
    ordinary = int(np.sum(L * (L - 1) + L * (2 * b - lK - 4)))
    # zero block (4.7): w_{0,i} = min(2i + 6m_N - m_K + 1/2, min_c (Z_c - (ℓ_K(c)+4)/2)); doubled
    Wstar2 = int(np.min(2 * Z - lK - 4))
    zero = sum(min(4 * i + 12 * mN - 2 * mK + 1, Wstar2) for i in range(L0))
    report = dict(
        L_nonneg=bool(np.all(L >= 0)),
        dims=L0 + int(np.sum(L)) == h,
        deg_ordinary=int(np.max(2 * Z)) <= p + 1,
        deg_zero=5 + 4 * L0 + 12 * mN <= p + 1,
        # at the zero source every ordinary row has half-weight 2L₀ + 6m_N - m_K + 1/2, which must
        # dominate every ordinary assigned weight
        zero_source=2 * (2 * L0 + 6 * mN - mK) + 1 >= int(np.max(2 * (Z - 1) - lK - 4)),
    )
    return ordinary + zero, report


def gamma_out(p, K, N):
    """(4.14)."""
    v = K - p * (K // p)
    u = max(0, N + v - p + 1)
    tp = min(N, v) + u
    rp = max(0, K + 4 * N - 2 * p + 2)
    if K < 2 * p:
        return -7 * (K - p) + 6 * tp - 1 - min(rp, p - 1 - N + u)
    return -7 * (K - p) + 3 + 12 * N + 5 * tp - min(rp, p + u)


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 320000
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    assert K % 40 == 0 and M >= 40
    n = K // 40
    N, h = 3 * n, 37 * n
    print(f"K = {K}, M = {M}, N = {N}, h = {h};  K ≥ 200M²: {K >= 200 * M * M}")
    ps = primes_upto(2 * h)

    small = inner = outer = 0.0
    err_in, err_S_in, err_out, err_S_out = [], [], [], []
    side = dict(L_nonneg=True, dims=True, deg_ordinary=True, deg_zero=True, zero_source=True, c49=True)
    for p in ps:
        vS = vp_SK(K, N, h, p)
        if p * M <= K:
            Lp = -6 * h * floor_log(p, 5 * K) - h * (vp_int(24, p) or 0)
            small += -Lp * math.log(p)
        elif 3 * p <= K:
            g, rep = gamma_in(p, K, N, h, M)
            for k, v in rep.items():
                side[k] &= v
            Lp = vS + g
            inner += -Lp * math.log(p)
            x = Fr(K, p)
            err_in.append(g - p * Gamma(x))
            err_S_in.append(vS - p * Nfun(x))
        else:
            g = gamma_out(p, K, N) if p <= K else 0
            if p <= K:
                side["c49"] &= (p >= 7 and p <= K < 3 * p and p * p > 2 * K and 2 * N < p
                                and 5 * N <= 2 * p - 2)
                y = Fr(p, K)
                if y not in (Fr(1, 2), Fr(1)):
                    err_out.append(-g - K * (R0(y) - drank(y)))
                    scal = -2 * LAMBDA * (K // p) + sum(max(Fr(0), 2 * LAMBDA - j * y) for j in range(1, 6))
                    err_S_out.append(-vS - K * scal)
            Lp = vS + g
            outer += -Lp * math.log(p)

    print("\n== Side conditions in the proofs of Propositions 4.1 and 4.3")
    for k, v in side.items():
        print(f"[{'OK' if v else 'FAIL'}] {k}")

    print("\n== O_M(1) errors of the limiting formulas (max |error| over the range)")
    fmt = lambda xs: f"min {float(min(xs)):+.2f}, max {float(max(xs)):+.2f}, #primes {len(xs)}"
    print(f"   γ_p^in  - pΓ(K/p)          : {fmt(err_in)}")
    print(f"   v_p(S_K) - pN(K/p)  (inner): {fmt(err_S_in)}")
    print(f"   -γ_p^out - K(R₀ - d)(p/K)  : {fmt(err_out)}")
    print(f"   -v_p(S_K) - K(…)(p/K) (outer): {fmt(err_S_out)}")

    print("\n== K⁻² log m_{K,M} against (5.11) and (5.20)")
    K2 = K * K
    inner_int, _ = integrate_affine_over_x3(R_def, inner_breakpoints(3, M))
    limit = I_OUT + 6 * LAMBDA / M + inner_int
    print(f"   small primes p ≤ K/M : {small / K2:.6f}   (limit 6λ/M = {float(6 * LAMBDA / M):.6f})")
    print(f"   inner K/M < p ≤ K/3  : {inner / K2:.6f}   (limit ∫_3^M R x⁻³ = {float(inner_int):.6f})")
    print(f"   outer p > K/3        : {outer / K2:.6f}   (limit I_out = {float(I_OUT):.6f})")
    total = (small + inner + outer) / K2
    print(f"   total K⁻² log m      : {total:.6f}   (limit {float(limit):.6f}, A_M = {float(A_M(M)):.6f})")


if __name__ == "__main__":
    main()
