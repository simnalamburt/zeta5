/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Zeta5.Weight

/-!
# The external field and the elementary bounds of §6.2

* `Zeta5.Vfield`: the field (6.1), `V(t) = 2π√t + ∫_0^1 log(t + u²) du - 6 ∫_0^α log(t + u²) du`.
* `Zeta5.sum_log_ge`, `Zeta5.sum_log_le`: the Riemann sum comparison (6.12), in the form
  `K ∫_0^{m/K} log(t + u²) du ≤ ∑_{j ≤ m} log(t + (j/K)²)` and
  `∑_{j ≤ m} log(t + (j/K)²) ≤ K ∫_0^{m/K} … + log(t + 1) + 2 log K + 2`
  for `t > 0` and `m < K`. (The paper's upper bound `2 log K + 2` is sharper; the extra
  `log(t + 1)` only contributes a polynomial factor to the integrand.)
* `Zeta5.wt_le`: the weight bound (6.11), `w(y) ≤ 32π⁴ (1 + y)⁵ e^{-2πy}`.
-/

open Real MeasureTheory Set intervalIntegral

namespace Zeta5

/-- `J(t, c) = ∫_0^c log(t + u²) du`. -/
noncomputable def Jlog (t c : ℝ) : ℝ := ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2)

/-- (6.1): `V(t) = 2π√t + ∫_0^1 log(t + u²) du - 6 ∫_0^α log(t + u²) du`. -/
noncomputable def Vfield (t : ℝ) : ℝ := 2 * π * √t + Jlog t 1 - 6 * Jlog t alpha

/-! ### Riemann sums (6.12) -/

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ i ∈ Finset.range m, f (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem continuous_log_add_sq {t : ℝ} (ht : 0 < t) (K : ℝ) :
    Continuous fun v : ℝ => Real.log (t + (v / K) ^ 2) :=
  Continuous.log (by fun_prop) fun v => by positivity

theorem monotoneOn_log_add_sq {t K : ℝ} (ht : 0 < t) (hK : 0 < K) :
    MonotoneOn (fun v : ℝ => Real.log (t + (v / K) ^ 2)) (Ici 0) := by
  intro a ha b hb hab
  refine Real.log_le_log (by positivity) ?_
  have : a / K ≤ b / K := div_le_div_of_nonneg_right hab hK.le
  have ha' : 0 ≤ a / K := div_nonneg ha hK.le
  nlinarith

theorem integral_log_add_sq_eq {t K : ℝ} (hK : 0 < K) (m : ℝ) :
    ∫ v in (0 : ℝ)..m, Real.log (t + (v / K) ^ 2) = K * Jlog t (m / K) := by
  rw [Jlog, intervalIntegral.integral_comp_div (fun u => Real.log (t + u ^ 2)) hK.ne',
    zero_div, smul_eq_mul]

/-- The lower half of (6.12): `K ∫_0^{m/K} log(t + u²) du ≤ ∑_{j=1}^m log(t + (j/K)²)`. -/
theorem sum_log_ge {t K : ℝ} (ht : 0 < t) (hK : 0 < K) (m : ℕ) :
    K * Jlog t (m / K) ≤ ∑ j ∈ Finset.Icc 1 m, Real.log (t + (j / K) ^ 2) := by
  have h := MonotoneOn.integral_le_sum (x₀ := 0) (a := m)
    ((monotoneOn_log_add_sq ht hK).mono (Icc_subset_Ici_self))
  rw [zero_add, integral_log_add_sq_eq hK] at h
  refine h.trans_eq ?_
  rw [sum_Icc_one_eq_sum_range (fun j => Real.log (t + (j / K) ^ 2))]
  simp only [zero_add, Nat.cast_add, Nat.cast_one]

/-- The upper half of (6.12), with an extra `log(t + ((m+1)/K)²)`. -/
theorem sum_log_le {t K : ℝ} (ht : 0 < t) (hK : 1 ≤ K) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, Real.log (t + (j / K) ^ 2) ≤
      K * Jlog t (m / K) + Real.log (t + ((m + 1) / K) ^ 2) + 2 * Real.log K + 2 := by
  have hK0 : 0 < K := by linarith
  set g := fun v : ℝ => Real.log (t + (v / K) ^ 2) with hg
  have hmono := monotoneOn_log_add_sq ht hK0
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    (continuous_log_add_sq ht K).intervalIntegrable a b
  -- `∑_{j=1}^m g(j) ≤ ∫_1^{m+1} g`
  have h1 := MonotoneOn.sum_le_integral (x₀ := 1) (a := m) (hmono.mono (by
    intro x hx; exact le_trans zero_le_one hx.1))
  have hsum : ∑ j ∈ Finset.Icc 1 m, g j = ∑ i ∈ Finset.range m, g (1 + i) := by
    rw [sum_Icc_one_eq_sum_range (fun j => g j)]
    simp only [Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)]
  -- split `∫_1^{m+1} = ∫_0^m + ∫_m^{m+1} - ∫_0^1`
  have hsplit : ∫ v in (1 : ℝ)..1 + m, g v =
      (∫ v in (0 : ℝ)..m, g v) + (∫ v in (m : ℝ)..m + 1, g v) - ∫ v in (0 : ℝ)..1, g v := by
    have e1 := integral_add_adjacent_intervals (hint 0 m) (hint m (m + 1))
    have e2 := integral_add_adjacent_intervals (hint 0 1) (hint 1 (m + 1))
    rw [add_comm (1 : ℝ) m]
    linarith
  -- `∫_m^{m+1} g ≤ g(m+1)`
  have htop : ∫ v in (m : ℝ)..m + 1, g v ≤ g (m + 1) := by
    have := intervalIntegral.integral_mono_on (by linarith) (hint m (m + 1))
      (intervalIntegrable_const (c := g (m + 1))) fun v hv =>
        hmono (le_trans (Nat.cast_nonneg m) hv.1) (by positivity : (0 : ℝ) ≤ m + 1) hv.2
    simpa using this
  -- `∫_0^1 g ≥ -2 log K - 2`
  have hbot : -2 * Real.log K - 2 ≤ ∫ v in (0 : ℝ)..1, g v := by
    have hlow : ∫ v in (0 : ℝ)..1, (2 * Real.log v - 2 * Real.log K) ≤ ∫ v in (0 : ℝ)..1, g v := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
        ((intervalIntegral.intervalIntegrable_log').const_mul 2 |>.sub intervalIntegrable_const)
        (hint 0 1) fun v hv => ?_
      rw [hg]
      calc 2 * Real.log v - 2 * Real.log K = Real.log ((v / K) ^ 2) := by
            rw [Real.log_pow, Real.log_div hv.1.ne' hK0.ne']; push_cast; ring
        _ ≤ Real.log (t + (v / K) ^ 2) :=
            Real.log_le_log (by have := hv.1; positivity) (by linarith)
    have hval : ∫ v in (0 : ℝ)..1, (2 * Real.log v - 2 * Real.log K) = -2 - 2 * Real.log K := by
      rw [intervalIntegral.integral_sub ((intervalIntegral.intervalIntegrable_log').const_mul 2)
        intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_log,
        intervalIntegral.integral_const]
      simp
    linarith
  rw [hsum]
  have := h1.trans_eq hsplit
  rw [integral_log_add_sq_eq hK0] at this
  simp only [hg] at this htop hbot ⊢
  linarith

/-! ### The weight bound (6.11) -/

theorem pow_four_le_choose (ℓ : ℕ) : ((ℓ : ℝ) + 1) ^ 4 ≤ 24 * ((ℓ + 4).choose 4 : ℕ) := by
  have h : (ℓ + 4).descFactorial 4 = Nat.factorial 4 * (ℓ + 4).choose 4 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (ℓ + 4).descFactorial 4 = (ℓ + 4) * (ℓ + 3) * (ℓ + 2) * (ℓ + 1) := by
    simp [Nat.descFactorial_succ]
    ring
  have h3 : ((ℓ + 4).choose 4 : ℝ) * 24 = (ℓ + 4) * (ℓ + 3) * (ℓ + 2) * (ℓ + 1) := by
    have := congr_arg (fun x : ℕ => (x : ℝ)) (h.symm.trans h2)
    simp only [Nat.factorial, Nat.cast_mul] at this
    push_cast at this
    linarith
  nlinarith [sq_nonneg ((ℓ : ℝ) + 1)]

/-- (6.11): `w(y) ≤ 32π⁴ (1 + y)⁵ e^{-2πy}` for `y > 0`. -/
theorem wt_le {y : ℝ} (hy : 0 < y) : wt y ≤ 32 * π ^ 4 * (1 + y) ^ 5 * exp (-(2 * π * y)) := by
  set q := exp (-(2 * π * y)) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]; have := pi_pos; nlinarith
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 4
    (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have hterm : ∀ ℓ : ℕ, wTerm ℓ y ≤ 2 * (2 * π) ^ 4 * y ^ 5 * q *
      (((ℓ + 4).choose 4 : ℕ) * q ^ ℓ) := by
    intro ℓ
    have he : exp (-((2 * π * ((ℓ : ℝ) + 1)) * y)) = q * q ^ ℓ := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [wTerm, he]
    have := pow_four_le_choose ℓ
    have hp : 0 ≤ (2 * π) ^ 4 / 12 * y ^ 5 * q * q ^ ℓ := by positivity
    calc (2 * π * ((ℓ : ℝ) + 1)) ^ 4 / 12 * (y ^ 5 * (q * q ^ ℓ))
        = (2 * π) ^ 4 / 12 * y ^ 5 * q * q ^ ℓ * ((ℓ : ℝ) + 1) ^ 4 := by ring
      _ ≤ (2 * π) ^ 4 / 12 * y ^ 5 * q * q ^ ℓ * (24 * ((ℓ + 4).choose 4 : ℕ)) := by gcongr
      _ = _ := by ring
  have hsum : wt y ≤ 2 * (2 * π) ^ 4 * y ^ 5 * q * (1 / (1 - q) ^ (4 + 1)) := by
    rw [wt, ← (hgeo.mul_left (2 * (2 * π) ^ 4 * y ^ 5 * q)).tsum_eq]
    exact (summable_wTerm hy).tsum_le_tsum hterm (hgeo.summable.mul_left _)
  -- `y / (1 - q) ≤ (1 + 2πy) / (2π)`
  have hx : 0 < 2 * π * y := by positivity
  have h1q : 2 * π * y / (1 + 2 * π * y) ≤ 1 - q := by
    have h := Real.add_one_le_exp (2 * π * y)
    have : q ≤ 1 / (1 + 2 * π * y) := by
      rw [hq, Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have : 1 / (1 + 2 * π * y) = 1 - 2 * π * y / (1 + 2 * π * y) := by field_simp; ring
    linarith
  have hyq : y / (1 - q) ≤ (1 + 2 * π * y) / (2 * π) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have := mul_le_mul_of_nonneg_left h1q (by positivity : (0 : ℝ) ≤ (1 + 2 * π * y) * y)
    have e : (1 + 2 * π * y) * y * (2 * π * y / (1 + 2 * π * y)) = 2 * π * y * y := by
      field_simp
    nlinarith
  have hpi : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.two_le_pi]
  have hlin : 1 + 2 * π * y ≤ 2 * π * (1 + y) := by nlinarith
  calc wt y ≤ 2 * (2 * π) ^ 4 * y ^ 5 * q * (1 / (1 - q) ^ (4 + 1)) := hsum
    _ = 2 * (2 * π) ^ 4 * q * (y / (1 - q)) ^ 5 := by
        rw [div_pow, mul_one_div]
        ring
    _ ≤ 2 * (2 * π) ^ 4 * q * ((1 + 2 * π * y) / (2 * π)) ^ 5 := by
        gcongr
    _ ≤ 2 * (2 * π) ^ 4 * q * (2 * π * (1 + y) / (2 * π)) ^ 5 := by gcongr
    _ = 32 * π ^ 4 * (1 + y) ^ 5 * q := by
        have : (2 * π) ≠ 0 := by positivity
        field_simp
        ring

end Zeta5
