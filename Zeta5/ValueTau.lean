/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Binom
import Zeta5.LocalTau

/-!
# Bounding `τ_X` by values on a window

The value bound (3.9) holds for any `D` consecutive integers, not only for `0, …, D - 1`: the
binomial basis shifted by an integer has integral coordinates in the unshifted one.

Combined with partial fractions this bounds `τ_X(N / ∏ (x - r))` through the residues and the values
`N(n) / ∏ (n - r)` on a window of integers avoiding the poles. In the inner range this replaces the
distribution formula of Lemma 3.2: every residue at a pole `r` of the class `c` has valuation at
least `E_c + 1`, and every value at a point of the class `c` at least `E_c`, where `E_c - 4` is the
bound (4.2), (4.3) for the source `c`. The window lies within `p²` of every pole, so each
`1/(n - r)` loses at most one `p`, and each `H⁽⁵⁾_{d(r)}` at most five.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `[x⁴] C(x + y, j)` has `v_p ≥ -4 ⌊log_p D⌋` for `j ≤ D`. -/
theorem VGe_coeff4_binomP_comp {j D : ℕ} (hj : j ≤ D) (y : ℤ) :
    VGe p (-4 * Nat.log p D) (((binomP j).comp (X + C (y : ℚ))).coeff 4) := by
  set P := (binomP j).comp (X + C (y : ℚ))
  have hP : P.natDegree < D + 1 := by
    refine (natDegree_comp_le).trans_lt ?_
    rw [natDegree_binomP, natDegree_X_add_C, mul_one]; omega
  rw [newton P hP, finsetSum_coeff]
  refine VGe_sum _ fun k hk => ?_
  rw [coeff_C_mul]
  have hk' : k ≤ D := by have := mem_range.1 hk; omega
  have h1 : VGe p 0 (fdiff P k) := by
    rw [fdiff_eq_sum]
    refine VGe_sum _ fun i _ => ?_
    have hv : P.eval (i : ℚ) = ((Ring.choose ((i : ℤ) + y) j : ℤ) : ℚ) := by
      rw [eval_comp, eval_add, eval_X, eval_C, show (i : ℚ) + y = (((i : ℤ) + y : ℤ) : ℚ) by
        push_cast; ring, binomP_eval_int]
    rw [hv]
    simpa using VGe_intCast (p := p) ((-1 : ℤ) ^ (k - i) * k.choose i * Ring.choose ((i : ℤ) + y) j)
  have h2 := CoeffBnd_binomP (p := p) k 4
  have hlog : Nat.log p k ≤ Nat.log p D := Nat.log_mono_right hk'
  refine (h1.mul h2).mono ?_
  push_cast
  omega

/-- (3.9) on the window `a, a + 1, …, a + D - 1`. -/
theorem taup_VGe_of_values_shift (Q : ℚ[X]) {D : ℕ} (hD : Q.natDegree < D) (a : ℤ) {A : ℤ}
    (hv : ∀ n : ℕ, n < D → VGe p (-A) (Q.eval ((a + n : ℤ) : ℚ))) :
    VGe p (-A - 4 * Nat.log p D) (taup Q) := by
  set Q' := Q.comp (X + C (a : ℚ))
  have hQ' : Q'.natDegree < D := by
    refine (natDegree_comp_le).trans_lt ?_
    rw [natDegree_X_add_C, mul_one]; exact hD
  set F := antidiff Q' - C ((antidiff Q').eval 0) with hF
  have hΔ : F.comp (X + 1) - F = Q' := by
    have := antidiff_spec Q'
    rw [hF, sub_comp, C_comp]; linear_combination this
  have hdeg : F.natDegree < D + 1 := by
    have := natDegree_antidiff_le Q'
    have h2 : F.natDegree ≤ (antidiff Q').natDegree := by
      rw [hF]; exact (natDegree_sub_le _ _).trans (by simp)
    omega
  have hval : ∀ n : ℕ, F.eval (n : ℚ) = ∑ i ∈ range n, Q'.eval (i : ℚ) := by
    intro n
    induction n with
    | zero => simp [hF]
    | succ n ih =>
      rw [sum_range_succ, ← ih, ← hΔ]
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one]
      push_cast; ring
  have hFv : ∀ n : ℕ, n ≤ D → VGe p (-A) (F.eval (n : ℚ)) := fun n hn => by
    rw [hval]
    refine VGe_sum _ fun i hi => ?_
    have := hv i (by have := mem_range.1 hi; omega)
    simp only [Q', eval_comp, eval_add, eval_X, eval_C]
    push_cast at this
    rwa [add_comm]
  -- `G(x) = F(x - a)` satisfies `ΔG = Q`
  set G := F.comp (X + C (-(a : ℚ)))
  have hG : G.comp (X + 1) - G = Q := by
    have e1 : G.comp (X + 1) = (F.comp (X + 1)).comp (X + C (-(a : ℚ))) := by
      simp only [G, comp_assoc, add_comp, X_comp, C_comp, one_comp]; ring_nf
    rw [e1, ← sub_comp, hΔ]
    simp only [Q', comp_assoc, add_comp, X_comp, C_comp]
    rw [show X + C (-(a : ℚ)) + C (a : ℚ) = X by rw [C_neg]; ring, comp_X]
  have hc : G.coeff 4 =
      ∑ j ∈ range (D + 1), fdiff F j * ((binomP j).comp (X + C ((-a : ℤ) : ℚ))).coeff 4 := by
    conv_lhs => rw [show G = F.comp (X + C (-(a : ℚ))) from rfl, newton F hdeg]
    rw [Polynomial.sum_comp, finsetSum_coeff]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_comp, C_comp, coeff_C_mul]
    push_cast; rfl
  rw [← hG, taup_delta, hc]
  refine VGe_sum _ fun j hj => ?_
  have hjD : j ≤ D := by have := mem_range.1 hj; omega
  have h1 : VGe p (-A) (fdiff F j) := by
    rw [fdiff_eq_sum]
    refine VGe_sum _ fun k hk => ?_
    have := (VGe_intCast (p := p) ((-1 : ℤ) ^ (j - k) * j.choose k)).mul
      (hFv k (by have := mem_range.1 hk; omega))
    simpa using this
  have h2 := VGe_coeff4_binomP_comp (p := p) hjD (-a)
  refine (h1.mul h2).mono ?_
  omega

/-- Partial fractions at a point `y` that is not a pole:
`Q(y) = N(y)/∏(y - r) - ∑_r Res_r / (y - r)`. -/
theorem eval_divByMonic_poleProd {R : Finset ℤ} (N : ℚ[X]) {y : ℚ}
    (hy : (poleProd R).eval y ≠ 0) :
    (N /ₘ poleProd R).eval y =
      N.eval y / (poleProd R).eval y - ∑ r ∈ R, resid R N r * (y - r)⁻¹ := by
  have h := congrArg (eval y) (modByMonic_add_div N (poleProd R))
  rw [modByMonic_poleProd, eval_add, eval_finsetSum, eval_mul] at h
  have hrr : ∀ r ∈ R, (poleProd (R.erase r)).eval y = (poleProd R).eval y * (y - r)⁻¹ := by
    intro r hr
    have hyr : y - r ≠ 0 := by
      intro h0
      rw [poleProd_eq_mul_erase hr, eval_mul] at hy
      simp [h0] at hy
    rw [poleProd_eq_mul_erase hr, eval_mul]
    simp only [eval_sub, eval_X, eval_C]
    field_simp
  have e : ∑ r ∈ R, resid R N r * (y - r)⁻¹ =
      (∑ r ∈ R, (C (resid R N r) * poleProd (R.erase r)).eval y) / (poleProd R).eval y := by
    rw [sum_div]
    refine sum_congr rfl fun r hr => ?_
    rw [eval_mul, eval_C, hrr r hr]; field_simp
  rw [e, ← h]
  field_simp
  ring

/-- The value form of the local estimate (see the module docstring). -/
theorem PolyVGe_tauR_of_values {R : Finset ℤ} {N : ℚ[X]} {E : ℤ} {a : ℤ} {D : ℕ}
    (hD : (N /ₘ poleProd R).natDegree < D) (hlog : Nat.log p D ≤ 1)
    (hres : ∀ r ∈ R, VGe p (E + 5) (resid R N r))
    (hwin : ∀ n : ℕ, n < D → (poleProd R).eval ((a + n : ℤ) : ℚ) ≠ 0 ∧
      VGe p (E + 4) (N.eval ((a + n : ℤ) : ℚ) / (poleProd R).eval ((a + n : ℤ) : ℚ)))
    (hsep : ∀ n : ℕ, n < D → ∀ r ∈ R, VGe p (-1) ((((a + n : ℤ) : ℚ) - r)⁻¹))
    (hH : ∀ r ∈ R, VGe p (-5) (H5 (dd r))) :
    PolyVGe p E (tauR R N) := by
  refine PolyVGe_tauR (VGe.add ?_ (VGe_sum _ fun r hr => ?_)) ?_
  · have h := taup_VGe_of_values_shift (p := p) _ hD a (A := -(E + 4)) fun n hn => by
      rw [eval_divByMonic_poleProd N (hwin n hn).1, neg_neg]
      refine (hwin n hn).2.sub (VGe_sum _ fun r hr => ?_)
      exact ((hres r hr).mul (hsep n hn r hr)).mono (by omega)
    refine h.mono ?_
    omega
  · simpa using (hres r hr).mul (hH r hr)
  · exact VGe_sum _ fun r hr => (hres r hr).mono (by omega)

end Zeta5
