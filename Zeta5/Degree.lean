/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Zeta5.Defs

/-!
# The degree of `Q_{K,M}` (§2.3)

Every entry of `G_K(X)` is affine in `X`, so `G_K(X) = X • B + A` for rational matrices `A`, `B`,
and `[X^h] Δ_K = det B`. After cancellation only the poles `-j²` with `N < j ≤ K` contribute to `B`,
and there are exactly `h` of them, so `B = Vᵀ diag(c) V` with a square Vandermonde matrix
`V_{kj} = (-(N+1+k)²)^j`. Hence `det B = (det V)² ∏ c_k ≠ 0`, and `Δ_K`, `F_K` and `Q_{K,M}` all
have degree exactly `h`. This is (2.9) of the paper, up to the explicit value of the leading
coefficient, which is not needed.

## Main results

* `Zeta5.coeff_Δ_dim`: `[X^h] Δ_K = det B`.
* `Zeta5.det_Glin_ne_zero`: `det B ≠ 0`.
* `Zeta5.natDegree_Q`: `deg Q_{K,M} = h`.
-/

open Polynomial Matrix

namespace Zeta5

/-! ### Every entry of `G_K(X)` is affine in `X` -/

theorem muPole_eq (j : ℕ) :
    muPole j = C ((j : ℚ) ^ 4) * X + C (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * j)) := by
  simp only [muPole, map_add, map_sub, map_mul, map_neg]
  ring

theorem natDegree_muPole_le (j : ℕ) : (muPole j).natDegree ≤ 1 := by
  rw [muPole_eq]
  compute_degree

theorem natDegree_muX_le (A : ℚ[X]) (S : Finset ℕ) : (muX A S).natDegree ≤ 1 := by
  rw [muX]
  refine natDegree_add_le_of_degree_le (by simp) ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact natDegree_C_mul_le _ _ |>.trans (natDegree_muPole_le j)

theorem coeff_muPole_one (j : ℕ) : (muPole j).coeff 1 = (j : ℚ) ^ 4 := by
  rw [muPole_eq, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem coeff_muX_one (A : ℚ[X]) (S : Finset ℕ) :
    (muX A S).coeff 1 = ∑ j ∈ S, residue A S j * (j : ℚ) ^ 4 := by
  simp [muX, finsetSum_coeff, coeff_muPole_one]

/-- The constant term `A` of `G_K(X) = X • B + A`. -/
noncomputable def Gconst (n : ℕ) : Matrix (Fin (dim n)) (Fin (dim n)) ℚ :=
  (G n).map fun p => p.coeff 0

/-- The coefficient `B` of `X` in `G_K(X) = X • B + A`. -/
noncomputable def Glin (n : ℕ) : Matrix (Fin (dim n)) (Fin (dim n)) ℚ :=
  (G n).map fun p => p.coeff 1

theorem G_eq (n : ℕ) : G n = (X : ℚ[X]) • (Glin n).map C + (Gconst n).map C := by
  ext i j : 1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Glin, Gconst, G, of_apply,
    smul_eq_mul]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (natDegree_muX_le _ _)]
  ring

theorem natDegree_Δ_le (n : ℕ) : (Δ n).natDegree ≤ dim n := by
  rw [Δ, G_eq]
  simpa using natDegree_det_X_add_C_le (Glin n) (Gconst n)

theorem coeff_Δ_dim (n : ℕ) : (Δ n).coeff (dim n) = (Glin n).det := by
  rw [Δ, G_eq]
  simpa using coeff_det_X_add_C_card (Glin n) (Gconst n)

/-! ### The Vandermonde factorisation of `B` -/

/-- The `k`-th surviving pole `j = N + 1 + k`, for `0 ≤ k < h`. -/
def pole (n : ℕ) (k : Fin (dim n)) : ℕ := N n + 1 + k

/-- The node `-j²` of the surviving pole `j = N + 1 + k`. -/
def node (n : ℕ) (k : Fin (dim n)) : ℚ := -((pole n k : ℕ) : ℚ) ^ 2

/-- The weight `j⁴ · Res_{t = -j²} D_N(t)⁶ / D_K(t)` of the surviving pole `j = N + 1 + k`. -/
noncomputable def weight (n : ℕ) (k : Fin (dim n)) : ℚ :=
  residue (D (N n) ^ 6) (Finset.Icc 1 (K n)) (pole n k) * ((pole n k : ℕ) : ℚ) ^ 4

theorem residue_mul_X_pow (A : ℚ[X]) (S : Finset ℕ) (j s : ℕ) :
    residue (A * X ^ s) S j = residue A S j * (-(j : ℚ) ^ 2) ^ s := by
  simp only [residue, eval_mul, eval_pow, eval_X]
  ring

theorem eval_D_eq_zero {m j : ℕ} (hj : j ∈ Finset.Icc 1 m) : (D m).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [D, poleDen, eval_prod]
  exact Finset.prod_eq_zero hj (by simp)

theorem eval_D_ne_zero {m j : ℕ} (hj : m < j) : (D m).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [D, poleDen, eval_prod, Finset.prod_ne_zero_iff]
  intro i hi
  have hi' : i < j := (Finset.mem_Icc.1 hi).2.trans_lt hj
  have : (i : ℚ) ^ 2 < (j : ℚ) ^ 2 := by
    have : (i : ℚ) < j := by exact_mod_cast hi'
    nlinarith [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)]
  simp only [eval_add, eval_X, eval_C]
  linarith

theorem Glin_apply (n : ℕ) (i j : Fin (dim n)) :
    Glin n i j = ∑ k : Fin (dim n), node n k ^ (i : ℕ) * weight n k * node n k ^ (j : ℕ) := by
  rw [Glin, map_apply, G, of_apply, coeff_muX_one]
  -- the poles `j ≤ N` do not contribute
  have hsub : Finset.Icc (N n + 1) (K n) ⊆ Finset.Icc 1 (K n) :=
    Finset.Icc_subset_Icc (by omega) le_rfl
  rw [← Finset.sum_subset hsub fun k hk hk' => ?_]
  · have hlen : K n + 1 - (N n + 1) = dim n := by simp only [K, N, dim]; omega
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, hlen,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [weight, node, pole, residue_mul_X_pow]
    push_cast
    ring
  · have : k ≤ N n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
      omega
    have h0 := eval_D_eq_zero (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hk).1, this⟩)
    simp [residue, h0]

theorem Glin_eq (n : ℕ) :
    Glin n = (vandermonde (node n))ᵀ * diagonal (weight n) * vandermonde (node n) := by
  ext i j
  rw [Glin_apply, mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_diagonal, vandermonde_apply]

theorem det_Glin (n : ℕ) :
    (Glin n).det = (vandermonde (node n)).det ^ 2 * ∏ k, weight n k := by
  rw [Glin_eq, det_mul, det_mul, det_transpose, det_diagonal]
  ring

theorem node_injective (n : ℕ) : Function.Injective (node n) := by
  intro k l h
  simp only [node, pole, neg_inj] at h
  have h' : ((N n + 1 + k : ℕ) : ℚ) = (N n + 1 + l : ℕ) :=
    (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).1 h
  exact Fin.ext (by exact_mod_cast (Nat.add_left_cancel (Nat.cast_injective h')))

/-- `D_K` has simple roots, so its derivative does not vanish at a root. -/
theorem eval_derivative_D_ne_zero {m j : ℕ} (hj : j ∈ Finset.Icc 1 m) :
    (derivative (D m)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  have hsep : (D m).Separable := by
    have : D m = ∏ i ∈ Finset.Icc 1 m, (X - C (-(i : ℚ) ^ 2)) := by
      simp [D, poleDen, sub_eq_add_neg]
    rw [this, separable_prod_X_sub_C_iff']
    intro x _ y _ hxy
    have : (x : ℚ) ^ 2 = (y : ℚ) ^ 2 := neg_inj.1 hxy
    exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg x) (Nat.cast_nonneg y)).1 this
  exact hsep.eval₂_derivative_ne_zero (RingHom.id ℚ) (x := -(j : ℚ) ^ 2) (eval_D_eq_zero hj)

theorem weight_ne_zero (n : ℕ) (k : Fin (dim n)) : weight n k ≠ 0 := by
  have hk := k.isLt
  have hpole : pole n k ∈ Finset.Icc 1 (K n) := by
    simp only [pole, Finset.mem_Icc, K, N, dim] at hk ⊢
    omega
  have hN : N n < pole n k := by simp [pole]; omega
  simp only [weight, residue, eval_pow]
  refine mul_ne_zero (div_ne_zero (pow_ne_zero _ (eval_D_ne_zero hN)) ?_) ?_
  · exact eval_derivative_D_ne_zero (by simpa [D] using hpole)
  · have := (Finset.mem_Icc.1 hpole).1
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))

theorem det_Glin_ne_zero (n : ℕ) : (Glin n).det ≠ 0 := by
  rw [det_Glin]
  refine mul_ne_zero (pow_ne_zero _ (det_vandermonde_ne_zero_iff.2 (node_injective n))) ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => weight_ne_zero n k

/-! ### The degree -/

theorem natDegree_Δ (n : ℕ) : (Δ n).natDegree = dim n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_Δ_le n)
    (by rw [coeff_Δ_dim]; exact det_Glin_ne_zero n)

theorem natDegree_F (n : ℕ) : (F n).natDegree = dim n := by
  rw [F, natDegree_C_mul (S_pos n).ne', natDegree_Δ]

/-- (2.9): `deg Q_{K,M} = h`, for every `n` and `M`. -/
theorem natDegree_Q (n M : ℕ) : (Q n M).natDegree = dim n := by
  rw [Q, natDegree_C_mul (normFactor_pos n M).ne', natDegree_F]

end Zeta5
