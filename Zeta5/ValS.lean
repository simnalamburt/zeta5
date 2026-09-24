/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.RFun
import Zeta5.SmallPrimes

/-!
# The valuation of `S_K` at a large prime

For an odd prime `p` with `p² > 2h`, Legendre's formula has one term for every factorial in (2.5),
so `v_p(S_K) = 2h⌊K/p⌋ - 12h⌊N/p⌋ - 2∑_{i<h} ⌊2i/p⌋`. The last sum is at most `p J(h/p)` with
`J(u) = mu - m(m+1)/4`, `m = ⌊2u⌋`, so `v_p(S_K) ≥ p N(K/p)` with `N` of (5.5)
(`Zeta5.p_mul_N_le`).
-/

open Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(m!) = ⌊m/p⌋` for `m < p²`. -/
theorem padicValRat_factorial_of_lt {m : ℕ} (hm : m < p ^ 2) :
    padicValRat p (m.factorial : ℚ) = (m / p : ℕ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  rw [padicValRat_factorial m (B := 2) (Nat.log_lt_of_lt_pow hm0.ne' hm)]
  simp

omit hp in
/-- `∑_{i<h} ⌊2i/p⌋ ≤ m h - p m(m+1)/4` with `m = ⌊2h/p⌋`: the sum is at most `p J(h/p)`. -/
theorem sum_div_le (hp3 : 3 ≤ p) (h : ℕ) :
    (∑ i ∈ range h, ((2 * i / p : ℕ) : ℚ)) ≤
      ((2 * h / p : ℕ) : ℚ) * h - p * ((2 * h / p : ℕ) * ((2 * h / p : ℕ) + 1)) / 4 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ]
    set m := 2 * h / p
    set m' := 2 * (h + 1) / p
    have hp0 : 0 < p := by omega
    have e1 : p * m + 2 * h % p = 2 * h := Nat.div_add_mod _ _
    have e2 : p * m' + 2 * (h + 1) % p = 2 * (h + 1) := Nat.div_add_mod _ _
    have r1 := Nat.mod_lt (2 * h) hp0
    have r2 := Nat.mod_lt (2 * (h + 1)) hp0
    have hmm : m ≤ m' := Nat.div_le_div_right (by omega)
    have hm1 : m' ≤ m + 1 := by
      by_contra hc
      have h3 : p * m + p * 2 ≤ p * m' := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hpm : (p : ℚ) * m' ≤ 2 * (h + 1) := by
      have : p * m' ≤ 2 * (h + 1) := by omega
      exact_mod_cast this
    rcases Nat.eq_or_lt_of_le hm1 with h1 | h1
    · have : (m' : ℚ) = m + 1 := by exact_mod_cast h1
      rw [this] at hpm ⊢
      push_cast
      nlinarith
    · have : m' = m := by omega
      rw [this]
      push_cast
      nlinarith

/-- (2.5): `v_p(S_K) = 2h⌊K/p⌋ - 12h⌊N/p⌋ - 2∑_{i=1}^{h-1} ⌊2i/p⌋` for odd `p` with `p² > 2h`. -/
theorem padicValRat_S {n : ℕ} (hp2 : p ≠ 2) (hsq : 2 * dim n < p ^ 2) :
    padicValRat p (S n) = 2 * dim n * (K n / p : ℕ) - 12 * dim n * (N n / p : ℕ) -
      2 * ∑ i ∈ Icc 1 (dim n - 1), ((2 * i / p : ℕ) : ℤ) := by
  have hK : K n < p ^ 2 := by simp only [K, dim] at hsq ⊢; omega
  have hN : N n < p ^ 2 := by simp only [N, dim] at hsq ⊢; omega
  have hf : ∀ m : ℕ, (m.factorial : ℚ) ≠ 0 := fun m => by positivity
  have h4 : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    have : ¬p ∣ 4 := by
      intro h
      have h' : p ∣ 2 ^ 2 := by norm_num; exact h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h'))
    simp [padicValNat.eq_zero_of_not_dvd this]
  unfold S
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.mul (by positivity) (by positivity), padicValRat.pow,
    padicValRat.pow, padicValRat.pow, h4,
    padicValRat_prod _ _ fun i _ => by positivity, padicValRat_factorial_of_lt hK,
    padicValRat_factorial_of_lt hN]
  rw [mul_sum]
  have : ∀ i ∈ Icc 1 (dim n - 1), padicValRat p (((2 * i).factorial : ℚ) ^ 2) =
      2 * ((2 * i / p : ℕ) : ℤ) := by
    intro i hi
    have := (mem_Icc.1 hi).2
    rw [padicValRat.pow, padicValRat_factorial_of_lt (by omega)]
    push_cast; ring
  rw [sum_congr rfl this]
  push_cast
  ring

/-- `v_p(S_K) ≥ p N(K/p)`, where `N(x) = 2λx⌊x⌋ - 12λx⌊αx⌋ - 2J(λx)` is (5.5). -/
theorem p_mul_N_le {n : ℕ} (hp2 : p ≠ 2) (hsq : 2 * dim n < p ^ 2) :
    (p : ℚ) * RFun.eN.eval ((K n : ℚ) / p) ≤ padicValRat p (S n) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  rw [padicValRat_S hp2 hsq]
  have e1 : (37 / 20 : ℚ) * ((K n : ℚ) / p) = ((2 * dim n : ℕ) : ℚ) / p := by
    simp only [K, dim]; push_cast; ring
  have e2 : (3 / 40 : ℚ) * ((K n : ℚ) / p) = ((N n : ℕ) : ℚ) / p := by
    simp only [K, N]; push_cast; ring
  simp only [RFun.eN, RFun.eJ, RFun.c, RFun.x, Ex.eval_sub, Ex.eval_mul, Ex.eval_cst,
    Ex.eval_var, Ex.eval_floor, Ex.eval_add, e1, e2, Rat.floor_natCast_div_natCast,
    ← Int.natCast_div, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sum]
  have hsum := sum_div_le hp3 (dim n)
  have hrange : ∑ i ∈ range (dim n), ((2 * i / p : ℕ) : ℚ) =
      ∑ i ∈ Icc 1 (dim n - 1), ((2 * i / p : ℕ) : ℚ) := by
    rcases Nat.eq_zero_or_pos (dim n) with h0 | h0
    · rw [h0]; simp
    · rw [sum_range_eq_add_Ico _ h0]
      have : Icc 1 (dim n - 1) = Ico 1 (dim n) := by ext; simp; omega
      simp [this]
  rw [hrange] at hsum
  have hp' : (p : ℚ) ≠ 0 := hp0.ne'
  set kk : ℚ := ((K n / p : ℕ) : ℚ)
  set kN : ℚ := ((N n / p : ℕ) : ℚ)
  set m : ℚ := ((2 * dim n / p : ℕ) : ℚ)
  set sm := ∑ i ∈ Icc 1 (dim n - 1), ((2 * i / p : ℕ) : ℚ)
  have hK40 : (K n : ℚ) = 40 * n := by simp [K]
  have hd : (dim n : ℚ) = 37 * n := by simp [dim]
  have key : (p : ℚ) * ((2 * (dim n : ℚ)) / p * kk - 111 / 10 * ((K n : ℚ) / p) * kN -
      2 * (m * (37 / 40 * ((K n : ℚ) / p)) - m * (m + 1) * (1 / 4))) =
      2 * dim n * kk - 12 * dim n * kN - 2 * (m * dim n - p * (m * (m + 1)) / 4) := by
    rw [hK40, hd]; field_simp; ring
  have e3 : ((2 * dim n : ℕ) : ℚ) = 2 * (dim n : ℚ) := by push_cast; ring
  rw [e3]
  linarith [key]

end Zeta5
