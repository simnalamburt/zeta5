/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Zeta5.Constants
import Zeta5.Gram
import Zeta5.LogDelta
import Zeta5.LogS

/-!
# The real bound (Proposition 6.3)

Proposition 6.3 of the paper states `log F_K(ζ(5)) ≤ Ū K² + 24 K log K + 200 K` for every
`K ∈ 40ℤ_{>0}`. The irrationality proof only uses the leading term, so we prove the asymptotic
form: for every `ε > 0`, eventually `log F_K(ζ(5)) ≤ (Ū + ε) K²`. This lets all lower order terms
of §6 be treated as `o(K²)`.
-/

open Polynomial Filter

namespace Zeta5

/-! ### The constants -/

/-- A lower bound of `I(ρ)`, from rational enclosures of the sixteen logarithms (A.10). -/
def IrhoLo : ℚ := ∑ j, ∑ k, wgtQ j * wgtQ k * Enclose.logLo 14 60 (radQ (max j k) / 2)

theorem IrhoLo_le : (IrhoLo : ℝ) ≤ Irho := by
  unfold IrhoLo Irho
  push_cast
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  rw [wgtQ_cast, wgtQ_cast]
  refine mul_le_mul_of_nonneg_left ?_ (mul_pos (wgt_pos j) (wgt_pos k)).le
  have := Enclose.logLo_le 14 60 (x := radQ (max j k) / 2)
    (by have := radQ_pos (max j k); positivity)
  push_cast at this
  rwa [radQ_cast] at this

/-- An upper bound of `C*` (A.10). -/
def CstarHi : ℚ :=
  -2 * lambda + 12 * alpha * lambda * (1 - Enclose.logLo 14 60 alpha) + 3 * lambda ^ 2 -
    2 * lambda ^ 2 * Enclose.logLo 14 60 (2 * lambda)

theorem Cstar_le : Cstar ≤ CstarHi := by
  have h1 := Enclose.logLo_le 14 60 (x := alpha) (by norm_num [alpha])
  have h2 := Enclose.logLo_le 14 60 (x := 2 * lambda) (by norm_num [lambda])
  have hα : (0 : ℝ) ≤ 12 * alpha * lambda := by rw [alpha_real, lambda_real]; norm_num
  have hl : (0 : ℝ) ≤ 2 * lambda ^ 2 := by positivity
  have e1 := mul_le_mul_of_nonneg_left h1 hα
  have e2 := mul_le_mul_of_nonneg_left h2 hl
  unfold Cstar CstarHi
  push_cast at e2 ⊢
  linarith

/-- (6.4): `λM₀ - I(ρ) + C* ≤ Ū`. -/
theorem energy_const_le : (lambda : ℝ) * M0 - Irho + Cstar ≤ Ubar := by
  have h : lambda * M0 - IrhoLo + CstarHi ≤ Ubar := by decide +kernel
  have h' : ((lambda * M0 - IrhoLo + CstarHi : ℚ) : ℝ) ≤ Ubar := by exact_mod_cast h
  push_cast at h'
  linarith [IrhoLo_le, Cstar_le]

/-! ### Lower order terms -/

/-- `a K log K + b K ≤ ε K²` for all large `n`. -/
theorem eventually_lin_log_le (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a * K n * Real.log (K n) + b * K n ≤ ε * (K n : ℝ) ^ 2 := by
  have hK : Tendsto (fun n : ℕ => (K n : ℝ)) atTop atTop := by
    simp only [K, Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog := hK.eventually ((Real.isLittleO_log_id_atTop.bound
    (show 0 < ε / (2 * (|a| + 1)) by positivity)))
  have hlin := hK.eventually_ge_atTop (2 * (|b| + 1) / ε)
  filter_upwards [hlog, hlin, hK.eventually_ge_atTop 1] with n hl hb h1
  simp only [Real.norm_eq_abs, id] at hl
  have hK0 : (0 : ℝ) < K n := by linarith
  rw [abs_of_pos hK0] at hl
  have hl' : Real.log (K n) ≤ ε / (2 * (|a| + 1)) * K n := (le_abs_self _).trans hl
  have hL0 : 0 ≤ Real.log (K n) := Real.log_nonneg h1
  have h1' : a * K n * Real.log (K n) ≤ ε / 2 * (K n : ℝ) ^ 2 := by
    calc a * K n * Real.log (K n) ≤ |a| * K n * Real.log (K n) := by
          gcongr; exact le_abs_self a
      _ ≤ (|a| + 1) * K n * (ε / (2 * (|a| + 1)) * K n) := by gcongr; linarith
      _ = ε / 2 * (K n : ℝ) ^ 2 := by field_simp
  have h2' : b * K n ≤ ε / 2 * (K n : ℝ) ^ 2 := by
    have e : |b| + 1 = ε / 2 * (2 * (|b| + 1) / ε) := by field_simp
    have hb' : |b| + 1 ≤ ε / 2 * K n := by
      rw [e]; exact mul_le_mul_of_nonneg_left hb (by positivity)
    calc b * K n ≤ (|b| + 1) * K n := by nlinarith [le_abs_self b]
      _ ≤ ε / 2 * K n * K n := mul_le_mul_of_nonneg_right hb' hK0.le
      _ = ε / 2 * (K n : ℝ) ^ 2 := by ring
  linarith

/-! ### The two halves of Proposition 6.3 -/

/-- (6.15), asymptotic form: `log S_K ≤ (2λ - 12αλ - 2λ²) K² log K + (C* + ε) K²`. -/
theorem logS_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (S n) ≤
      (2 * lambda - 12 * alpha * lambda - 2 * lambda ^ 2 : ℝ) * (K n : ℝ) ^ 2 * Real.log (K n) +
        (Cstar + ε) * (K n : ℝ) ^ 2 := by
  filter_upwards [eventually_lin_log_le 5 10 hε, eventually_ge_atTop 1] with n h hn
  have := log_S_le hn
  linarith

/-- (6.14), asymptotic form: `log Δ_K(ζ(5)) ≤ 2h(h + 6N - K) log K + (λM₀ - I(ρ) + ε) K²`. -/
theorem logΔ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (aeval (riemannZeta 5).re (Δ n)) ≤
      (2 * lambda * (lambda + 6 * alpha - 1) : ℝ) * (K n : ℝ) ^ 2 * Real.log (K n) +
        ((lambda : ℝ) * M0 - Irho + ε) * (K n : ℝ) ^ 2 := by
  set C2 : ℝ := Real.log (2 ^ 17 * (1 + (17).factorial)) with hC2
  have hC1 : 0 ≤ C1 := by
    have h2 : (2 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) Real.two_le_pi 4
    have := Real.log_nonneg (show (1 : ℝ) ≤ 32 * Real.pi ^ 4 by linarith)
    rw [C1]; linarith
  have hC2' : 0 ≤ C2 := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (17).factorial := by positivity
    nlinarith)
  filter_upwards [energy_bound (half_pos hε), eventually_lin_log_le 30 (C1 + C2) (half_pos hε),
    eventually_ge_atTop 1] with n hE hlin hn
  have hΔ := log_Δ_le_Bexp hn (E := (lambda : ℝ) * M0 - Irho + ε / 2) hE
  have hK0 := K_pos hn
  have hK1 : (1 : ℝ) ≤ K n := by
    simp only [K]; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hL := Real.log_nonneg hK1
  have hlog2 : Real.log (2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18)) ≤
      C2 + 18 * Real.log (K n) := by
    have hle : 2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18) ≤
        2 ^ 17 * (1 + (17).factorial) * (K n : ℝ) ^ 18 := by
      have : (K n : ℝ) ≤ (K n : ℝ) ^ 18 := le_self_pow₀ hK1 (by norm_num)
      nlinarith
    calc _ ≤ Real.log (2 ^ 17 * (1 + (17).factorial) * (K n : ℝ) ^ 18) :=
          Real.log_le_log (by positivity) hle
      _ = C2 + 18 * Real.log (K n) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast
          ring
  have hh : (dim n : ℝ) = 37 / 40 * K n := by simp only [dim, K]; push_cast; ring
  have hN : (N n : ℝ) = 3 / 40 * K n := by simp only [N, K]; push_cast; ring
  rw [Bexp, hh, hN] at hΔ
  have h37 := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ 37 / 40 * K n by positivity)
  have hlam : (lambda : ℝ) = 37 / 40 := by rw [lambda]; push_cast; ring
  have halp : (alpha : ℝ) = 3 / 40 := by rw [alpha]; push_cast; ring
  rw [hlam, halp]
  rw [hlam] at hΔ
  nlinarith [mul_nonneg hK0.le hL, mul_nonneg (add_nonneg hC1 hC2') hK0.le]

/-- Proposition 6.3, asymptotic form. -/
theorem realBound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (aeval (riemannZeta 5).re (F n)) ≤ ((Ubar : ℝ) + ε) * (K n : ℝ) ^ 2 := by
  filter_upwards [logS_le (half_pos hε), logΔ_le (half_pos hε)] with n hS hΔ
  have hSpos : (0 : ℝ) < S n := by exact_mod_cast S_pos n
  have hΔpos := aeval_Δ_pos n
  rw [F, map_mul, aeval_C, eq_ratCast, Real.log_mul hSpos.ne' hΔpos.ne']
  have hc := energy_const_le
  have hK2 : (0 : ℝ) ≤ (K n : ℝ) ^ 2 := by positivity
  have hcancel : (2 * lambda - 12 * alpha * lambda - 2 * lambda ^ 2 : ℝ) +
      2 * lambda * (lambda + 6 * alpha - 1) = 0 := by ring
  have := mul_le_mul_of_nonneg_right hc hK2
  nlinarith [mul_nonneg hK2 (le_refl (0 : ℝ))]

end Zeta5
