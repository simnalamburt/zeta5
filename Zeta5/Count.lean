/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Factorization
import Zeta5.PBound

/-!
# Counting multiples and `p`-adic valuations of products of integers

The small prime estimates of §3.3 count roots modulo `p^j`. We use:

* `Zeta5.mcnt a b q`, the number of multiples of `q` in `(a, b]`, and the bounds
  `⌊L/q⌋ ≤ mcnt a (a + L) q ≤ ⌈L/q⌉`;
* `Zeta5.padicValInt_prod_eq_sum_card`: `v_p(∏ nᵢ) = ∑_{j ≥ 1} #{i | p^j ∣ nᵢ}` (Legendre's
  counting, for any finite family of nonzero integers).
-/

open Finset

namespace Zeta5

/-! ### Multiples of `q` in an interval -/

/-- The number of multiples of `q` in `(a, b]`. -/
def mcnt (a b : ℤ) (q : ℕ) : ℕ := #{x ∈ Ioc a b | (q : ℤ) ∣ x}

theorem mcnt_eq (a b : ℤ) {q : ℕ} (hq : 0 < q) :
    (mcnt a b q : ℤ) = max (⌊(b : ℚ) / q⌋ - ⌊(a : ℚ) / q⌋) 0 := by
  rw [mcnt, Int.Ioc_filter_dvd_card a b (by exact_mod_cast hq)]
  push_cast; rfl

theorem mcnt_ge (a : ℤ) (L : ℕ) {q : ℕ} (hq : 0 < q) : L / q ≤ mcnt a (a + L) q := by
  have h := mcnt_eq a (a + L) hq
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  set F1 := ⌊((a + L : ℤ) : ℚ) / q⌋
  set F0 := ⌊(a : ℚ) / q⌋
  have h1 : ((a + L : ℤ) : ℚ) / q < F1 + 1 := Int.lt_floor_add_one _
  have h2 : (F0 : ℚ) ≤ a / q := Int.floor_le _
  have h3 : ((L / q : ℕ) : ℚ) ≤ (L : ℚ) / q := Nat.cast_div_le
  have h4 : ((L / q : ℕ) : ℚ) < F1 - F0 + 1 := by
    push_cast at h1
    have : (L : ℚ) / q = ((a : ℚ) + L) / q - a / q := by rw [← sub_div]; ring_nf
    linarith
  have h5 : ((L / q : ℕ) : ℤ) ≤ F1 - F0 := by
    have : ((L / q : ℕ) : ℤ) < F1 - F0 + 1 := by
      have h4' : (((L / q : ℕ) : ℤ) : ℚ) < ((F1 - F0 + 1 : ℤ) : ℚ) := by push_cast; exact h4
      exact_mod_cast h4'
    omega
  have : ((L / q : ℕ) : ℤ) ≤ (mcnt a (a + L) q : ℤ) := by rw [h]; exact le_max_of_le_left h5
  exact_mod_cast this

theorem mcnt_le (a : ℤ) (L : ℕ) {q : ℕ} (hq : 0 < q) : mcnt a (a + L) q ≤ (L + q - 1) / q := by
  have h := mcnt_eq a (a + L) hq
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  set F1 := ⌊((a + L : ℤ) : ℚ) / q⌋
  set F0 := ⌊(a : ℚ) / q⌋
  have h1 : (F1 : ℚ) ≤ ((a + L : ℤ) : ℚ) / q := Int.floor_le _
  have h2 : (a : ℚ) / q < F0 + 1 := Int.lt_floor_add_one _
  have h3 : ((F1 - F0 - 1 : ℤ) : ℚ) * q < L := by
    push_cast at h1 ⊢
    have e1 : (F1 : ℚ) * q ≤ a + L := by rwa [le_div_iff₀ hq'] at h1
    have e2 : (a : ℚ) < (F0 + 1) * q := by rwa [div_lt_iff₀ hq'] at h2
    nlinarith
  have h4 : (F1 - F0 - 1) * (q : ℤ) < L := by exact_mod_cast h3
  have h5 : F1 - F0 ≤ ((L + q - 1) / q : ℕ) := by
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have key : (F1 - F0 - 1) * (q : ℤ) ≤ (L : ℤ) - 1 := by omega
    have : ((L + q - 1 : ℕ) : ℤ) = (L : ℤ) - 1 + q := by omega
    have hdiv : ((L + q - 1) / q : ℕ) = ((L + q - 1 : ℕ) : ℤ) / q := by push_cast; rfl
    rw [hdiv, this]
    rw [Int.le_ediv_iff_mul_le (by omega)]
    nlinarith
  have : (mcnt a (a + L) q : ℤ) ≤ ((L + q - 1) / q : ℕ) := by
    rw [h]; exact max_le h5 (by positivity)
  exact_mod_cast this

theorem mcnt_add {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ) :
    mcnt a c q = mcnt a b q + mcnt b c q := by
  rw [mcnt, mcnt, mcnt, ← Ioc_union_Ioc_eq_Ioc hab hbc, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl))]

theorem mcnt_self (y : ℤ) (q : ℕ) : mcnt (y - 1) y q = if (q : ℤ) ∣ y then 1 else 0 := by
  have : Ioc (y - 1) y = {y} := by ext x; simp; omega
  rw [mcnt, this, filter_singleton]
  split_ifs <;> simp

end Zeta5
