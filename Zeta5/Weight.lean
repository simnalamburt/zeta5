/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.ZetaValues
import Zeta5.Defs

/-!
# The weight of Proposition 2.2 and its moments

The weight (2.10) is `w(y) = (2π)⁴ y⁵ / 12 ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}` on `(0, ∞)`. Its even moments are
the values (2.2) of the functional on monomials:
`∫_0^∞ y^{2e} w(y) dy = (2e + 5)! ζ(2e + 2) / (12 (2π)^{2e+2}) = μ(t^e)`,
by the Gamma integral and Euler's formula for `ζ(2e + 2)`.

## Main results

* `Zeta5.integral_pow_mul_wt`: `∫_0^∞ y^{2e} w(y) dy = μ(t^e)`.
-/

open Real MeasureTheory Set

namespace Zeta5

/-- The term `(2πℓ)⁴ y⁵ e^{-2πℓy} / 12` of the weight (2.10), for `ℓ ≥ 1` written as `ℓ + 1`. -/
noncomputable def wTerm (ℓ : ℕ) (y : ℝ) : ℝ :=
  (2 * π * (ℓ + 1)) ^ 4 / 12 * (y ^ 5 * exp (-((2 * π * (ℓ + 1)) * y)))

/-- (2.10): `w(y) = (2π)⁴ y⁵ / 12 ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`. -/
noncomputable def wt (y : ℝ) : ℝ := ∑' ℓ : ℕ, wTerm ℓ y

/-! ### The Gamma integral -/

theorem integrableOn_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ m * exp (-(c * y))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := m) (p := 1) (b := c)
    (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]) one_pos hc
  refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp [rpow_natCast]

theorem integral_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi 0, y ^ m * exp (-(c * y)) = m.factorial / c ^ (m + 1) := by
  have := integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (r := c) (by positivity) hc
  rw [Gamma_nat_eq_factorial, show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
    rpow_natCast, one_div_pow] at this
  rw [div_eq_mul_one_div, mul_comm, ← this]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [show ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) by push_cast; ring, rpow_natCast]

/-! ### The moments -/

theorem integral_pow_mul_wTerm (e ℓ : ℕ) :
    ∫ y in Ioi 0, y ^ (2 * e) * wTerm ℓ y =
      (2 * e + 5).factorial / (12 * (2 * π) ^ (2 * e + 2)) * (1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2)) := by
  have hc : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity
  have h := integral_pow_mul_exp (2 * e + 5) hc
  simp only [wTerm]
  have : (fun y : ℝ => y ^ (2 * e) * ((2 * π * (ℓ + 1)) ^ 4 / 12 *
      (y ^ 5 * exp (-((2 * π * (ℓ + 1)) * y))))) =
      fun y => (2 * π * (ℓ + 1)) ^ 4 / 12 * (y ^ (2 * e + 5) * exp (-((2 * π * (ℓ + 1)) * y))) := by
    ext y; ring
  rw [this, integral_const_mul, h, show 2 * e + 5 + 1 = 4 + (2 * e + 2) by ring, pow_add,
    mul_pow (2 * π), mul_pow 2 π]
  field_simp
  rw [← mul_pow]

theorem integrableOn_pow_mul_wTerm (e ℓ : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * wTerm ℓ y) (Ioi 0) := by
  have hc : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity
  refine IntegrableOn.congr_fun ((integrableOn_pow_mul_exp (2 * e + 5) hc).const_mul
    ((2 * π * (ℓ + 1)) ^ 4 / 12)) (fun y _ => ?_) measurableSet_Ioi
  simp only [wTerm]
  ring

theorem wTerm_nonneg (ℓ : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wTerm ℓ y := by
  unfold wTerm
  positivity

/-- Euler's formula:
`∑_{ℓ ≥ 1} ℓ^{-(2e+2)} = (-1)^e 2^{2e+1} π^{2e+2} B_{2e+2} / (2e+2)!`. -/
theorem hasSum_zeta_even (e : ℕ) :
    HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2))
      ((-1 : ℝ) ^ e * 2 ^ (2 * e + 1) * π ^ (2 * e + 2) * bernoulli (2 * e + 2) /
        (2 * e + 2).factorial) := by
  have h := hasSum_zeta_nat (k := e + 1) (by omega)
  rw [show 2 * (e + 1) = 2 * e + 2 by ring, show 2 * e + 2 - 1 = 2 * e + 1 by omega,
    ← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    zero_pow (by omega : 2 * e + 2 ≠ 0), div_zero, sub_zero] at h
  convert h using 3
  ring

/-- The value `(2e + 5)! ζ(2e + 2) / (12 (2π)^{2e+2})` of the `2e`-th moment of `w`. -/
noncomputable def momentValue (e : ℕ) : ℝ :=
  (2 * e + 5).factorial / (12 * (2 * π) ^ (2 * e + 2)) *
    ((-1 : ℝ) ^ e * 2 ^ (2 * e + 1) * π ^ (2 * e + 2) * bernoulli (2 * e + 2) /
      (2 * e + 2).factorial)

theorem hasSum_integral_pow_mul_wTerm (e : ℕ) :
    HasSum (fun ℓ : ℕ => ∫ y in Ioi 0, y ^ (2 * e) * wTerm ℓ y) (momentValue e) := by
  simp only [integral_pow_mul_wTerm, momentValue]
  exact (hasSum_zeta_even e).mul_left _

theorem momentValue_pos (e : ℕ) : 0 < momentValue e := by
  have h := hasSum_zeta_even e
  have hv : 0 < (-1 : ℝ) ^ e * 2 ^ (2 * e + 1) * π ^ (2 * e + 2) * bernoulli (2 * e + 2) /
      (2 * e + 2).factorial := by
    rw [← h.tsum_eq]
    exact h.summable.tsum_pos (fun ℓ => by positivity) 0 (by positivity)
  exact mul_pos (by positivity) hv

theorem integral_pow_mul_wt_eq_momentValue (e : ℕ) :
    ∫ y in Ioi 0, y ^ (2 * e) * wt y = momentValue e := by
  have hint := hasSum_integral_of_summable_integral_norm
    (F := fun ℓ y => y ^ (2 * e) * wTerm ℓ y) (μ := volume.restrict (Ioi 0))
    (fun ℓ => integrableOn_pow_mul_wTerm e ℓ) ?_
  · simp only [wt, ← tsum_mul_left]
    exact hint.unique (hasSum_integral_pow_mul_wTerm e)
  · refine (hasSum_integral_pow_mul_wTerm e).summable.congr fun ℓ => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    simp only [Real.norm_eq_abs]
    exact (abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hy) _)
      (wTerm_nonneg ℓ (le_of_lt hy)))).symm

theorem integrableOn_pow_mul_wt (e : ℕ) : IntegrableOn (fun y => y ^ (2 * e) * wt y) (Ioi 0) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_pow_mul_wt_eq_momentValue]; exact (momentValue_pos e).ne')

/-- (2.2) via Proposition 2.2: `∫_0^∞ y^{2e} w(y) dy = μ(t^e)`. -/
theorem integral_pow_mul_wt (e : ℕ) : ∫ y in Ioi 0, y ^ (2 * e) * wt y = muMon e := by
  rw [integral_pow_mul_wt_eq_momentValue, momentValue, muMon]
  have hf : ((2 * e + 5).factorial : ℝ) =
      (2 * e + 2).factorial * ((2 * e + 3) * (2 * e + 4) * (2 * e + 5)) := by
    rw [show 2 * e + 5 = (2 * e + 2) + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  rw [hf, mul_pow, pow_succ 2 (2 * e + 1)]
  push_cast
  field_simp
  ring

theorem integrableOn_wt : IntegrableOn wt (Ioi 0) := by
  simpa using integrableOn_pow_mul_wt 0

/-! ### Positivity -/

theorem summable_wTerm {y : ℝ} (hy : 0 < y) : Summable fun ℓ => wTerm ℓ y := by
  have hq1 : ‖exp (-(2 * π * y))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_lt_one_iff]
    have := pi_pos
    nlinarith
  have hs : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * exp (-(2 * π * y)) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hq1)
  refine (hs.mul_left ((2 * π) ^ 4 / 12 * y ^ 5)).congr fun ℓ => ?_
  have he : exp (-((2 * π * ((ℓ : ℝ) + 1)) * y)) = exp (-(2 * π * y)) ^ (ℓ + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [wTerm, he]
  push_cast
  ring

theorem wt_pos {y : ℝ} (hy : 0 < y) : 0 < wt y :=
  (summable_wTerm hy).tsum_pos (fun ℓ => wTerm_nonneg ℓ hy.le) 0 (by unfold wTerm; positivity)

theorem wt_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wt y :=
  tsum_nonneg fun ℓ => wTerm_nonneg ℓ hy

end Zeta5
