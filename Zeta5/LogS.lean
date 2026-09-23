/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Zeta5.Defs

/-!
# The size of `S_K` (6.15)

`log S_K ≤ (2λ - 12αλ - 2λ²) K² log K + C* K² + 5 K log K + 6 K` for `K = 40n`, `n ≥ 1`, where
`C* = -2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. The proof uses Stirling's bounds
`n log n - n ≤ log n! ≤ n log n - n + (log n)/2 + 1` and a telescoping lower bound for
`∑_{i < h} log (2i)!`.
-/

open Real

namespace Zeta5

/-- Stirling's upper bound `log n! ≤ n log n - n + (log n)/2 + 1`. -/
theorem log_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log n.factorial ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at h
  set x : ℝ := ((m + 1 : ℕ) : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  rw [Real.log_div hx0.ne' (exp_pos 1).ne', Real.log_exp, Real.log_mul two_ne_zero hx0.ne'] at h
  linarith

/-- Stirling's lower bound `n log n - n ≤ log n!`. -/
theorem log_factorial_ge (n : ℕ) : n * Real.log n - n ≤ Real.log n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Stirling.le_log_factorial_stirling hn.ne'
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

/-- `G(x) = x² log(2x) - 3x²/2`, a primitive of `g(x) = 2x log(2x) - 2x`. -/
noncomputable def Gprim (x : ℝ) : ℝ := x ^ 2 * Real.log (2 * x) - 3 / 2 * x ^ 2

/-- `G(i) - G(i - 1) ≤ 2i log(2i) - 2i` for `i ≥ 2`, using only `log x ≤ x - 1`. -/
theorem Gprim_sub_le {i : ℝ} (hi : 2 ≤ i) :
    Gprim i - Gprim (i - 1) ≤ 2 * i * Real.log (2 * i) - 2 * i := by
  have hi1 : 0 < i - 1 := by linarith
  have hlog : Real.log (2 * (i - 1)) = Real.log (2 * i) - Real.log (i / (i - 1)) := by
    rw [Real.log_div (by linarith) hi1.ne', Real.log_mul two_ne_zero (by linarith : i ≠ 0),
      Real.log_mul two_ne_zero hi1.ne']
    ring
  have hu : Real.log (i / (i - 1)) ≤ 1 / (i - 1) := by
    have := Real.log_le_sub_one_of_pos (show 0 < i / (i - 1) by positivity)
    have e : i / (i - 1) - 1 = 1 / (i - 1) := by field_simp; ring
    linarith
  have hu0 : 0 ≤ Real.log (i / (i - 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hi1]; linarith)
  have h2 : 1 / 2 ≤ Real.log (2 * i) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 * i by linarith)
    have : (2 * i)⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  simp only [Gprim]
  rw [hlog]
  have hsq : (i - 1) ^ 2 * Real.log (i / (i - 1)) ≤ (i - 1) ^ 2 * (1 / (i - 1)) :=
    mul_le_mul_of_nonneg_left hu (sq_nonneg _)
  have e : (i - 1) ^ 2 * (1 / (i - 1)) = i - 1 := by field_simp
  nlinarith

/-- `∑_{i=1}^{m} (2i log(2i) - 2i) ≥ G(m)` for `m ≥ 1`. -/
theorem Gprim_le_sum {m : ℕ} (hm : 1 ≤ m) :
    Gprim m ≤ ∑ i ∈ Finset.Icc 1 m, (2 * (i : ℝ) * Real.log (2 * i) - 2 * i) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton, Gprim, Nat.cast_one]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 * 1 by norm_num)
    norm_num at this ⊢
    linarith
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := Gprim_sub_le (i := (m : ℝ) + 1) (by linarith)
    push_cast at this ⊢
    simp only [add_sub_cancel_right] at this
    linarith

/-- The constant (6.3), `C* = -2λ + 12αλ(1 - log α) + 3λ² - 2λ² log(2λ)`. -/
noncomputable def Cstar : ℝ :=
  -2 * lambda + 12 * alpha * lambda * (1 - Real.log alpha) + 3 * lambda ^ 2 -
    2 * lambda ^ 2 * Real.log (2 * lambda)

theorem log_S_eq (n : ℕ) :
    Real.log (S n) = 2 * dim n * Real.log (K n).factorial + (dim n - 1 : ℕ) * Real.log 4 -
      12 * dim n * Real.log (N n).factorial -
        2 * ∑ i ∈ Finset.Icc 1 (dim n - 1), Real.log (2 * i).factorial := by
  have hf : ∀ m : ℕ, (m.factorial : ℝ) ≠ 0 := fun m => by positivity
  simp only [S]
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_prod (fun i _ => by positivity)]
  simp only [Real.log_pow]
  rw [Finset.mul_sum]
  push_cast
  ring_nf

/-- (6.15): `log S_K ≤ (2λ - 12αλ - 2λ²) K² log K + C* K² + 5 K log K + 10 K`. -/
theorem log_S_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (S n) ≤ (2 * lambda - 12 * alpha * lambda - 2 * lambda ^ 2 : ℝ) * (K n : ℝ) ^ 2 *
      Real.log (K n) + Cstar * (K n : ℝ) ^ 2 + 5 * K n * Real.log (K n) + 10 * K n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the three Stirling bounds
  have hK := log_factorial_le (n := K n) (by simp only [K]; omega)
  have hN := log_factorial_ge (N n)
  have hh : 2 ≤ dim n := by simp only [dim]; omega
  have hsum : Gprim (dim n : ℝ) - (2 * (dim n : ℝ) * Real.log (2 * dim n) - 2 * dim n) ≤
      ∑ i ∈ Finset.Icc 1 (dim n - 1), Real.log (2 * i).factorial := by
    have h1 := Gprim_sub_le (i := (dim n : ℝ)) (by exact_mod_cast hh)
    have h2 := Gprim_le_sum (m := dim n - 1) (by omega)
    have h3 : ∑ i ∈ Finset.Icc 1 (dim n - 1), (2 * (i : ℝ) * Real.log (2 * i) - 2 * i) ≤
        ∑ i ∈ Finset.Icc 1 (dim n - 1), Real.log (2 * i).factorial := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := log_factorial_ge (2 * i)
      push_cast at this
      linarith
    have e : ((dim n - 1 : ℕ) : ℝ) = dim n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [e] at h2
    linarith
  rw [log_S_eq]
  -- express everything through `L = log K`
  set L := Real.log (K n) with hL
  have hKr : (K n : ℝ) = 40 * n := by simp [K]
  have hNr : (N n : ℝ) = alpha * K n := by rw [hKr]; simp [N, alpha]; ring
  have hhr : (dim n : ℝ) = lambda * K n := by rw [hKr]; simp [dim, lambda]; ring
  have hK0 : (0 : ℝ) < K n := by rw [hKr]; positivity
  have hlogN : Real.log (N n) = Real.log alpha + L := by
    rw [hNr, Real.log_mul (by norm_num [alpha]) hK0.ne']
  have hlog2h : Real.log (2 * dim n) = Real.log (2 * lambda) + L := by
    rw [hhr, ← mul_assoc, Real.log_mul (by norm_num [lambda]) hK0.ne']
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [hKr]; linarith)
  have hlog4 : Real.log 4 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlam : Real.log (2 * lambda) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * lambda by norm_num [lambda])
    norm_num [lambda] at this ⊢; linarith
  have hlam0 : 0 ≤ Real.log (2 * lambda) := Real.log_nonneg (by norm_num [lambda])
  have hcast : ((dim n - 1 : ℕ) : ℝ) = dim n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  rw [hlogN] at hN
  rw [hlog2h] at hsum
  simp only [Gprim] at hsum
  rw [hlog2h] at hsum
  -- the main algebra
  have hbound : 2 * (dim n : ℝ) * Real.log (K n).factorial + (dim n - 1) * Real.log 4 -
      12 * dim n * Real.log (N n).factorial -
        2 * ∑ i ∈ Finset.Icc 1 (dim n - 1), Real.log (2 * i).factorial ≤
      2 * dim n * (K n * L - K n + L / 2 + 1) + (dim n - 1) * Real.log 4 -
        12 * dim n * (N n * (Real.log alpha + L) - N n) -
        2 * ((dim n : ℝ) ^ 2 * (Real.log (2 * lambda) + L) - 3 / 2 * (dim n : ℝ) ^ 2 -
          (2 * dim n * (Real.log (2 * lambda) + L) - 2 * dim n)) := by
    have hd : (0 : ℝ) ≤ dim n := by positivity
    have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 2 * dim n)
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 12 * dim n)
    linarith
  refine hbound.trans ?_
  rw [hNr, hhr]
  simp only [Cstar]
  have hl : (lambda : ℝ) = 37 / 40 := by norm_num [lambda]
  have ha : (alpha : ℝ) = 3 / 40 := by norm_num [alpha]
  set c2 := Real.log (2 * (lambda : ℝ))
  set ca := Real.log (alpha : ℝ)
  rw [hl, ha]
  have hKL := mul_nonneg hK0.le hL0
  have hK4 : (K n : ℝ) * Real.log 4 ≤ 4 * K n := by nlinarith
  have hKc : (K n : ℝ) * c2 ≤ K n := by nlinarith
  have hKc0 : 0 ≤ (K n : ℝ) * c2 := mul_nonneg hK0.le hlam0
  nlinarith

end Zeta5
