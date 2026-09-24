/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.ValS

/-!
# The outer exponent against its limit

For a prime `p > K/3`, `-L_p(K, M) = -v_p(S_K) - γ_p^out ≤ p R(K/p) + 3`: the exponent (4.14) is
an explicit piecewise linear function of `K, N, p` up to `O(1)`, and it is `p` times the outer part
`Zeta5.RFun.eG1` (`K/2 < p ≤ K`) or `Zeta5.RFun.eG2` (`K/3 < p ≤ K/2`) of `R`. For `p > K`,
`γ_p^out = 0`. This is (5.8), (5.9) with the rank term `min(r_p, ·) ≤ r_p` bounded crudely for
`K/2 < p ≤ K`, as in the paper.
-/

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

namespace Outer

theorem mul_min_div {a b : ℚ} (P : ℚ) (hP : 0 < P) : P * min a b = min (P * a) (P * b) :=
  mul_min_of_nonneg _ _ hP.le

/-- (5.8)–(5.10): `-L_p(K, M) ≤ p R(K/p) + 3` for `K/3 < p`. -/
theorem neg_Lexp_le {n M : ℕ} (hn : 1 ≤ n) (hM : 3 ≤ M) (hp3 : K n < 3 * p) :
    -(Lexp p n M : ℚ) ≤ p * Rx ((K n : ℚ) / p) + 3 := by
  have hpM : ¬p * M ≤ K n := by intro h; nlinarith
  have hLexp : Lexp p n M = padicValRat p (S n) + gammaOut p n := by
    simp only [Lexp, if_neg hpM, if_neg (not_le.2 hp3)]
  have hKn : K n = 40 * n := rfl
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hsq : 2 * dim n < p ^ 2 := by simp only [dim]; nlinarith
  have hS := p_mul_N_le (n := n) hp2 hsq
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hpx : (p : ℚ) * ((K n : ℚ) / p) = K n := by field_simp
  have hN : (N n : ℚ) = 3 / 40 * K n := by simp only [N, K]; push_cast; ring
  rw [hLexp, Rx]
  push_cast
  rcases lt_or_ge (K n) p with h1 | h1
  · have hx : (K n : ℚ) / p < 1 := by rw [div_lt_one hp0]; exact_mod_cast h1
    rw [RFun.eR_eval_of_lt_one _ hx]
    have : gammaOut p n = 0 := by simp only [gammaOut, if_pos h1]
    rw [this]
    push_cast
    linarith
  rcases lt_or_ge (K n) (2 * p) with h2 | h2
  · have hx1 : 1 ≤ (K n : ℚ) / p := by rw [one_le_div hp0]; exact_mod_cast h1
    have hx2 : (K n : ℚ) / p < 2 := by rw [div_lt_iff₀ hp0]; exact_mod_cast h2
    rw [RFun.eR_eval_of_lt_two _ hx1 hx2, RFun.eG1_eval]
    have hv : v p n = K n - p := by
      simp only [v]
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
      push_cast [h1]; ring
    have ht : min (N n : ℤ) (K n - p) + max 0 ((N n : ℤ) + K n - 2 * p) ≤ t p n := by
      simp only [t, u, hv]
      have : max 0 ((N n : ℤ) + K n - 2 * p) ≤ max 0 ((N n : ℤ) + (K n - p) - p + 1) :=
        max_le_max le_rfl (by omega)
      linarith
    have hr : r p n ≤ max 0 ((K n : ℤ) + 4 * N n - 2 * p) + 2 := by
      simp only [r]
      rcases le_total 0 ((K n : ℤ) + 4 * N n - 2 * p + 2) with h | h
      · rw [max_eq_right h]; have := le_max_right 0 ((K n : ℤ) + 4 * N n - 2 * p); omega
      · rw [max_eq_left h]; have := le_max_left 0 ((K n : ℤ) + 4 * N n - 2 * p); omega
    have hγ : -(gammaOut p n : ℤ) ≤ 7 * ((K n : ℤ) - p) - 6 * t p n + 1 + r p n := by
      simp only [gammaOut, if_neg (not_lt.2 h1), if_pos h2]
      have := min_le_left (r p n) ((p : ℤ) - 1 - N n + u p n)
      linarith
    have ht' : (min (N n : ℚ) (K n - p) + max 0 ((N n : ℚ) + K n - 2 * p) : ℚ) ≤ t p n := by
      exact_mod_cast ht
    have hr' : (r p n : ℚ) ≤ max 0 ((K n : ℚ) + 4 * N n - 2 * p) + 2 := by exact_mod_cast hr
    have hγ' : -(gammaOut p n : ℚ) ≤ 7 * ((K n : ℚ) - p) - 6 * t p n + 1 + r p n := by
      exact_mod_cast hγ
    have e1 : (p : ℚ) * min (3 / 40 * ((K n : ℚ) / p)) ((K n : ℚ) / p - 1) =
        min (N n : ℚ) (K n - p) := by
      rw [mul_min_div _ hp0]
      congr 1
      · rw [hN]; linear_combination (3 / 40 : ℚ) * hpx
      · linear_combination hpx
    have e2 : (p : ℚ) * max (43 / 40 * ((K n : ℚ) / p) - 2) 0 =
        max 0 ((N n : ℚ) + K n - 2 * p) := by
      rw [mul_max_of_nonneg _ _ hp0.le, mul_zero, max_comm]
      congr 1
      rw [hN]; linear_combination (43 / 40 : ℚ) * hpx
    have e3 : (p : ℚ) * max (13 / 10 * ((K n : ℚ) / p) - 2) 0 =
        max 0 ((K n : ℚ) + 4 * N n - 2 * p) := by
      rw [mul_max_of_nonneg _ _ hp0.le, mul_zero, max_comm]
      congr 1
      rw [hN]; linear_combination (13 / 10 : ℚ) * hpx
    have e4 : (p : ℚ) * (7 * ((K n : ℚ) / p - 1)) = 7 * ((K n : ℚ) - p) := by
      linear_combination 7 * hpx
    linarith [e1, e2, e3, e4]
  · have hx1 : 2 ≤ (K n : ℚ) / p := by rw [le_div_iff₀ hp0]; exact_mod_cast (by omega : 2 * p ≤ K n)
    have hx2 : (K n : ℚ) / p < 3 := by rw [div_lt_iff₀ hp0]; exact_mod_cast hp3
    rw [RFun.eR_eval_of_lt_three _ hx1 hx2, RFun.eG2_eval]
    have hv : v p n = K n - 2 * p := by
      simp only [v]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have : 2 * p ≤ K n := h2
      push_cast [show p ≤ K n - p by omega, h1]; ring
    have ht : min (N n : ℤ) (K n - 2 * p) + max 0 ((N n : ℤ) + K n - 3 * p) ≤ t p n := by
      simp only [t, u, hv]
      have : max 0 ((N n : ℤ) + K n - 3 * p) ≤ max 0 ((N n : ℤ) + (K n - 2 * p) - p + 1) :=
        max_le_max le_rfl (by omega)
      linarith
    have hmr : min (r p n) (p + u p n) ≤
        min (max 0 ((K n : ℤ) + 4 * N n - 2 * p)) (p + max 0 ((N n : ℤ) + K n - 3 * p)) + 2 := by
      simp only [r, u, hv]
      rw [← min_add_add_right]
      refine min_le_min ?_ ?_
      · rcases le_total 0 ((K n : ℤ) + 4 * N n - 2 * p + 2) with h | h
        · rw [max_eq_right h]; have := le_max_right 0 ((K n : ℤ) + 4 * N n - 2 * p); omega
        · rw [max_eq_left h]; have := le_max_left 0 ((K n : ℤ) + 4 * N n - 2 * p); omega
      · have : max 0 ((N n : ℤ) + (K n - 2 * p) - p + 1) ≤
            max 0 ((N n : ℤ) + K n - 3 * p) + 1 := by
          rcases le_total 0 ((N n : ℤ) + (K n - 2 * p) - p + 1) with h | h
          · rw [max_eq_right h]; have := le_max_right 0 ((N n : ℤ) + K n - 3 * p); omega
          · rw [max_eq_left h]; have := le_max_left 0 ((N n : ℤ) + K n - 3 * p); omega
        omega
    have hγ : -(gammaOut p n : ℤ) = 7 * ((K n : ℤ) - p) - 3 - 12 * N n - 5 * t p n +
        min (r p n) (p + u p n) := by
      simp only [gammaOut, if_neg (not_lt.2 h1), if_neg (not_lt.2 h2)]
      ring
    have ht' : (min (N n : ℚ) (K n - 2 * p) + max 0 ((N n : ℚ) + K n - 3 * p) : ℚ) ≤ t p n := by
      exact_mod_cast ht
    have hmr' : (min (r p n) (p + u p n) : ℚ) ≤
        min (max 0 ((K n : ℚ) + 4 * N n - 2 * p)) (p + max 0 ((N n : ℚ) + K n - 3 * p)) + 2 := by
      exact_mod_cast hmr
    have hγ' : -(gammaOut p n : ℚ) = 7 * ((K n : ℚ) - p) - 3 - 12 * N n - 5 * t p n +
        min (r p n : ℚ) (p + u p n) := by exact_mod_cast hγ
    have e1 : (p : ℚ) * min (3 / 40 * ((K n : ℚ) / p)) ((K n : ℚ) / p - 2) =
        min (N n : ℚ) (K n - 2 * p) := by
      rw [mul_min_div _ hp0]
      congr 1
      · rw [hN]; linear_combination (3 / 40 : ℚ) * hpx
      · linear_combination hpx
    have e2 : (p : ℚ) * max (43 / 40 * ((K n : ℚ) / p) - 3) 0 =
        max 0 ((N n : ℚ) + K n - 3 * p) := by
      rw [mul_max_of_nonneg _ _ hp0.le, mul_zero, max_comm]
      congr 1
      rw [hN]; linear_combination (43 / 40 : ℚ) * hpx
    have e3 : (p : ℚ) * min (max (13 / 10 * ((K n : ℚ) / p) - 2) 0)
        (1 + max (43 / 40 * ((K n : ℚ) / p) - 3) 0) =
        min (max 0 ((K n : ℚ) + 4 * N n - 2 * p)) (p + max 0 ((N n : ℚ) + K n - 3 * p)) := by
      rw [mul_min_div _ hp0, mul_add, mul_one, e2, mul_max_of_nonneg _ _ hp0.le, mul_zero,
        max_comm]
      congr 2
      rw [hN]; linear_combination (13 / 10 : ℚ) * hpx
    have e4 : (p : ℚ) * (7 * ((K n : ℚ) / p - 1) - 9 / 10 * ((K n : ℚ) / p)) =
        7 * ((K n : ℚ) - p) - 12 * N n := by
      rw [hN]; linear_combination (61 / 10 : ℚ) * hpx
    linarith [e1, e2, e3, e4]

end Outer

end Zeta5
