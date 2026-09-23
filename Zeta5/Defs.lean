/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The objects of Theorem 2.1

This file defines the objects of §2.1, §4 and §5 of A. Fauzan, *ζ(5) is irrational*
(17 September 2026, `ZETA5_IS_IRRATIONAL.pdf`). Equation numbers refer to the paper. Nothing is
proved here beyond basic bookkeeping; the definitions are checked against the exact reference
implementation `scripts/zeta5_defs.py` in `Zeta5Test/Defs.lean`.

## Conventions

* Everything is indexed by `n`, with `K = 40n`, `N = 3n` and `h = 37n` as in (2.1). The paper's `h`
  is called `dim` here, to keep `h` free for hypotheses.
* The paper works with two polynomial variables: `t` for the rational functions fed to the
  functional, and `X` for the slot that is later specialised to `ζ(5)`. Both are the variable of
  `ℚ[X]` here; the type of each definition says which one is meant.
* A rational function with simple poles at `t = -j²` is represented by its numerator `A` and the
  finite set `S` of `j`, i.e. `A / ∏_{j ∈ S} (t + j²)`. The functional `μ_X` of (2.2), (2.3) is
  extended to such a representation by polynomial division and simple partial fractions, as the
  paper says after (2.3). That this agrees with the integral representation of Proposition 2.2 is
  proved separately.
* The weights of §4 are half-integers. We work with twice the weights, which are integers, and
  record the relation to the paper's weights in `Inner.gammaIn_eq`.

## Main definitions

* `Zeta5.mu`, `Zeta5.muPole`, `Zeta5.muX`: the functional of (2.2), (2.3).
* `Zeta5.G`, `Zeta5.Δ`, `Zeta5.S`, `Zeta5.F`: the matrix (2.4), its determinant, and (2.5).
* `Zeta5.Inner.gammaIn`, `Zeta5.Outer.gammaOut`: the exponents (4.8) and (4.14).
* `Zeta5.Lexp`, `Zeta5.normFactor`, `Zeta5.Q`: the exponents (5.1), the factor `m_{K,M}` of (5.2),
  and the polynomial `Q_{K,M}` of (2.6).
-/

open Polynomial

namespace Zeta5

/-! ### Parameters (2.1) -/

/-- `K = 40n`. -/
def K (n : ℕ) : ℕ := 40 * n

/-- `N = 3n`. -/
def N (n : ℕ) : ℕ := 3 * n

/-- The paper's `h = 37n`: the size of the Hankel matrix and the degree of `Q_{K,M}`. -/
def dim (n : ℕ) : ℕ := 37 * n

/-- `α = 3/40 = N/K`. -/
def alpha : ℚ := 3 / 40

/-- `λ = 37/40 = h/K`. -/
def lambda : ℚ := 37 / 40

/-- `H = 1 + 2α = 23/20`. -/
def bigH : ℚ := 1 + 2 * alpha

theorem N_eq_alpha_mul_K (n : ℕ) : (N n : ℚ) = alpha * K n := by
  simp only [N, K, alpha]; push_cast; ring

theorem dim_eq_lambda_mul_K (n : ℕ) : (dim n : ℚ) = lambda * K n := by
  simp only [dim, K, lambda]; push_cast; ring

theorem bigH_eq : bigH = 23 / 20 := by norm_num [bigH, alpha]

/-! ### The functional (2.2), (2.3) -/

/-- `∏_{j ∈ S} (t + j²)`, the denominator of a rational function with simple poles at `-j²`. -/
noncomputable def poleDen (S : Finset ℕ) : ℚ[X] := ∏ j ∈ S, (X + C ((j : ℚ) ^ 2))

/-- `D_m(t) = ∏_{j=1}^{m} (t + j²)`; in particular `D_0 = 1`. -/
noncomputable def D (m : ℕ) : ℚ[X] := poleDen (Finset.Icc 1 m)

/-- `H_j^{(5)} = ∑_{v=1}^{j} v⁻⁵`; in particular `H_0^{(5)} = 0`. -/
def H5 (j : ℕ) : ℚ := ∑ v ∈ Finset.Icc 1 j, 1 / (v : ℚ) ^ 5

/-- (2.2): `μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`. Only even Bernoulli numbers occur, so
the convention for `B₁` is irrelevant; Mathlib's `bernoulli` has `B₁ = -1/2` like the paper. -/
def muMon (e : ℕ) : ℚ :=
  (-1) ^ e * bernoulli (2 * e + 2) * ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)) / 24

/-- The functional `μ` on polynomials in `t`, extended linearly from (2.2). -/
noncomputable def mu : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun e => muMon e • LinearMap.id

/-- (2.3): `μ_X(1/(t + j²)) = j⁴ (X - H_j^{(5)}) - 1/4 + 1/(2j)`, a polynomial in `X`. -/
noncomputable def muPole (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (H5 j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

/-- The residue of `A / poleDen S` at the simple pole `t = -j²`, namely `A(-j²) / poleDen'(-j²)`. -/
noncomputable def residue (A : ℚ[X]) (S : Finset ℕ) (j : ℕ) : ℚ :=
  A.eval (-(j : ℚ) ^ 2) / (derivative (poleDen S)).eval (-(j : ℚ) ^ 2)

/-- `μ_X(A / ∏_{j ∈ S} (t + j²))`, by polynomial division and simple partial fractions:
the quotient `A /ₘ poleDen S` is sent to `μ`, and each simple pole to its residue times (2.3). The
result is a polynomial in `X` of degree at most one. -/
noncomputable def muX (A : ℚ[X]) (S : Finset ℕ) : ℚ[X] :=
  C (mu (A /ₘ poleDen S)) + ∑ j ∈ S, C (residue A S j) * muPole j

/-! ### The matrix and its determinant (2.4), (2.5) -/

/-- (2.4): `G_K(X) = [μ_X(D_N(t)⁶ t^{i+j} / D_K(t))]_{0 ≤ i, j < h}`. -/
noncomputable def G (n : ℕ) : Matrix (Fin (dim n)) (Fin (dim n)) ℚ[X] :=
  Matrix.of fun i j => muX (D (N n) ^ 6 * X ^ ((i : ℕ) + j)) (Finset.Icc 1 (K n))

/-- (2.4): `Δ_K(X) = det G_K(X)`. -/
noncomputable def Δ (n : ℕ) : ℚ[X] := (G n).det

/-- (2.5): `S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)`. -/
def S (n : ℕ) : ℚ :=
  ((K n).factorial : ℚ) ^ (2 * dim n) * 4 ^ (dim n - 1) /
    (((N n).factorial : ℚ) ^ (12 * dim n) *
      ∏ i ∈ Finset.Icc 1 (dim n - 1), ((2 * i).factorial : ℚ) ^ 2)

/-- (2.5): `F_K = S_K Δ_K`. -/
noncomputable def F (n : ℕ) : ℚ[X] := C (S n) * Δ n

/-! ### The inner exponent (4.4)-(4.8)

Throughout, `p` is an odd prime in the inner range `K/M < p ≤ K/3`. The ordinary square classes
are `a = 1, …, m` with `m = (p - 1)/2`; the class `a = 0` is the zero class. -/

namespace Inner

variable (p n M : ℕ)

/-- The ordinary classes `1 ≤ a ≤ m = (p - 1)/2`. -/
def classes : Finset ℕ := Finset.Icc 1 ((p - 1) / 2)

/-- `ℓ_A(a) = #{1 ≤ j ≤ A | j ≡ a or -a (mod p)}`. -/
def ell (A a : ℕ) : ℕ :=
  ((Finset.Icc 1 A).filter fun j => j ≡ a [MOD p] ∨ j + a ≡ 0 [MOD p]).card

/-- `L₀ = 4M + 10`, the number of basis rows assigned to the zero class. -/
def L0 : ℤ := 4 * M + 10

/-- `b_a = 3 ℓ_N(a)`. -/
def b (a : ℕ) : ℤ := 3 * ell p (N n) a

/-- The right-hand side `h - L₀ + 3(N - m_N)` of (4.4), where `m_N = ⌊N/p⌋`. -/
def rhs : ℤ := dim n - L0 M + 3 * ((N n : ℤ) - (N n / p : ℕ))

/-- (4.4): `mT + E = h - L₀ + 3(N - m_N)` with `0 ≤ E < m`. -/
def T : ℤ := rhs p n M / ((p - 1) / 2 : ℕ)

/-- (4.4): `mT + E = h - L₀ + 3(N - m_N)` with `0 ≤ E < m`. -/
def E : ℤ := rhs p n M % ((p - 1) / 2 : ℕ)

/-- The position of the class `a` when the classes are listed in decreasing order of `ℓ_K`, ties
broken by `a` (the paper allows any tie-breaking). -/
def rank (a : ℕ) : ℕ :=
  ((classes p).filter fun c =>
    ell p (K n) a < ell p (K n) c ∨ (ell p (K n) c = ell p (K n) a ∧ c < a)).card

/-- `ϵ_a = 1` for the first `E` classes in decreasing order of `ℓ_K(a)`, and `0` otherwise. -/
def eps (a : ℕ) : ℤ := if (rank p n a : ℤ) < E p n M then 1 else 0

/-- `L_a = T - b_a + ϵ_a`, the number of basis rows assigned to the class `a ≥ 1`. -/
def L (a : ℕ) : ℤ := T p n M - b p n a + eps p n M a

/-- `Z_a = L_a + b_a = T + ϵ_a`. -/
def Z (a : ℕ) : ℤ := T p n M + eps p n M a

/-- (4.6): the weight `w_{a,i} = i + b_a - (ℓ_K(a) + 4)/2` of the row `(a, i)`, `a ≥ 1`. -/
def w (a i : ℕ) : ℚ := i + b p n a - (ell p (K n) a + 4 : ℚ) / 2

/-- Twice the weight (4.6), an integer. -/
def w2 (a i : ℕ) : ℤ := 2 * i + 2 * b p n a - ell p (K n) a - 4

/-- Twice `min_{1 ≤ c ≤ m} (Z_c - (ℓ_K(c) + 4)/2)`, the second argument of the minimum in (4.7).
Zero if there are no ordinary classes (`p ≤ 2`), which never happens in the inner range. -/
def zeroCap2 : ℤ :=
  if hc : (classes p).Nonempty then
    (classes p).inf' hc fun c => 2 * Z p n M c - ell p (K n) c - 4
  else 0

/-- (4.7): the weight `w_{0,i} = min(2i + 6m_N - m_K + 1/2, min_c (Z_c - (ℓ_K(c) + 4)/2))` of the
row `(0, i)` of the zero class, where `m_A = ⌊A/p⌋`. -/
def w0 (i : ℕ) : ℚ :=
  min (2 * i + 6 * (N n / p : ℕ) - (K n / p : ℕ) + 1 / 2 : ℚ) ((zeroCap2 p n M : ℚ) / 2)

/-- Twice the weight (4.7), an integer. -/
def w02 (i : ℕ) : ℤ :=
  min (4 * i + 12 * (N n / p : ℕ) - 2 * (K n / p : ℕ) + 1 : ℤ) (zeroCap2 p n M)

/-- (4.8): `γ_p^in = 2 ∑_{a=0}^{m} ∑_{i=0}^{L_a - 1} w_{a,i}`, computed with doubled weights. -/
def gammaIn : ℤ :=
  (∑ a ∈ classes p, ∑ i ∈ Finset.range (L p n M a).toNat, w2 p n a i) +
    ∑ i ∈ Finset.range (L0 M).toNat, w02 p n M i

theorem w2_eq (a i : ℕ) : (w2 p n a i : ℚ) = 2 * w p n a i := by
  simp only [w2, w]; push_cast; ring

theorem w02_eq (i : ℕ) : (w02 p n M i : ℚ) = 2 * w0 p n M i := by
  simp only [w02, w0, Int.cast_min, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_one]
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 2)]
  congr 1 <;> ring

/-- The integer `gammaIn` is the paper's `γ_p^in = 2 ∑ w_{a,i}` with the half-integer weights
(4.6), (4.7). -/
theorem gammaIn_eq : (gammaIn p n M : ℚ) =
    2 * ((∑ a ∈ classes p, ∑ i ∈ Finset.range (L p n M a).toNat, w p n a i) +
      ∑ i ∈ Finset.range (L0 M).toNat, w0 p n M i) := by
  simp only [gammaIn, mul_add, Finset.mul_sum]
  push_cast
  simp only [w2_eq, w02_eq]

/-- `zeroCap2` is twice the minimum over the ordinary classes in (4.7). -/
theorem zeroCap2_eq (hc : (classes p).Nonempty) :
    (zeroCap2 p n M : ℚ) / 2 =
      (classes p).inf' hc fun c => (Z p n M c : ℚ) - (ell p (K n) c + 4 : ℚ) / 2 := by
  simp only [zeroCap2, hc, ↓reduceDIte]
  rw [Finset.apply_inf'_eq_inf'_comp hc (fun x : ℤ => (x : ℚ) / 2)]
  · congr 1
    ext c
    simp only [Function.comp_apply]
    push_cast
    ring
  · intro x y
    rw [Int.cast_min, min_div_div_right (by norm_num : (0 : ℚ) ≤ 2)]

end Inner

/-! ### The outer exponent (4.14) -/

namespace Outer

variable (p n : ℕ)

/-- `v = K - p⌊K/p⌋`. -/
def v : ℤ := (K n % p : ℕ)

/-- `u = max(0, N + v - p + 1)`. -/
def u : ℤ := max 0 ((N n : ℤ) + v p n - p + 1)

/-- `t_p = min(N, v) + u`. -/
def t : ℤ := min (N n : ℤ) (v p n) + u p n

/-- (4.10): the rank bound `r_p = max(0, K + 4N - 2p + 2)` of the polynomial correction. -/
def r : ℤ := max 0 ((K n : ℤ) + 4 * N n - 2 * p + 2)

/-- (4.14), together with the convention `γ_p^out = 0` for `p > K` stated before (5.1). -/
def gammaOut : ℤ :=
  if K n < p then 0
  else if K n < 2 * p then
    -7 * ((K n : ℤ) - p) + 6 * t p n - 1 - min (r p n) ((p : ℤ) - 1 - N n + u p n)
  else
    -7 * ((K n : ℤ) - p) + 3 + 12 * N n + 5 * t p n - min (r p n) ((p : ℤ) + u p n)

end Outer

/-! ### The normalisation (5.1), (5.2) and the polynomial (2.6) -/

/-- (5.1): the exponent `L_p(K, M)`. -/
noncomputable def Lexp (p n M : ℕ) : ℤ :=
  if p * M ≤ K n then
    -6 * (dim n : ℤ) * Nat.log p (5 * K n) - dim n * padicValNat p 24
  else if 3 * p ≤ K n then padicValRat p (S n) + Inner.gammaIn p n M
  else padicValRat p (S n) + Outer.gammaOut p n

/-- (5.2): `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`, the product over primes. -/
noncomputable def normFactor (n M : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range (2 * dim n + 1)).filter Nat.Prime, (p : ℚ) ^ (-Lexp p n M)

/-- (2.6): `Q_{K,M} = m_{K,M} F_K`. -/
noncomputable def Q (n M : ℕ) : ℚ[X] := C (normFactor n M) * F n

/-! ### Basic facts -/

theorem poleDen_monic (S : Finset ℕ) : (poleDen S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem natDegree_poleDen (S : Finset ℕ) : (poleDen S).natDegree = S.card := by
  rw [poleDen, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem D_monic (m : ℕ) : (D m).Monic := poleDen_monic _

theorem natDegree_D (m : ℕ) : (D m).natDegree = m := by
  simp [D, natDegree_poleDen]

theorem mu_apply (P : ℚ[X]) : mu P = P.sum fun e c => muMon e * c := by
  simp [mu, lsum_apply]

theorem mu_monomial (e : ℕ) (c : ℚ) : mu (monomial e c) = muMon e * c := by
  simp [mu_apply]

theorem S_pos (n : ℕ) : 0 < S n := by
  unfold S
  positivity

theorem normFactor_pos (n M : ℕ) : 0 < normFactor n M := by
  unfold normFactor
  refine Finset.prod_pos fun p hp => zpow_pos ?_ _
  exact_mod_cast (Finset.mem_filter.1 hp).2.pos

end Zeta5
