/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Data.Int.CardIntervalMod
import Zeta5.InnerCount

/-!
# The square classes in the outer range

The remaining poles `J_c = {N < j ≤ K | j² ≡ c²}` of the classes `0 ≤ c ≤ m` partition `(N, K]`.
For `1 ≤ c ≤ m` there are exactly `ℓ_K(c) = 2⌊K/p⌋ + [c ≤ v] + [c ≥ p - v]` poles `j ≤ K` in the
class, `v = K mod p`.
-/

open Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

namespace Outer

/-- The remaining poles `N < j ≤ K` of the class `c`. -/
def J (p Nn Kn c : ℕ) : Finset ℕ :=
  (Ioc Nn Kn).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) ^ 2 - (c : ℤ) ^ 2

omit hp in
theorem mem_J {Nn Kn c j : ℕ} :
    j ∈ J p Nn Kn c ↔ (Nn < j ∧ j ≤ Kn) ∧ (p : ℤ) ∣ (j : ℤ) ^ 2 - (c : ℤ) ^ 2 := by
  simp [J]

/-- Every integer lies in exactly one class `c ≤ m`. -/
theorem card_class_eq_one (hp2 : p ≠ 2) (y : ℤ) :
    #((range ((p - 1) / 2 + 1)).filter fun c : ℕ => (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) = 1 := by
  obtain ⟨c, hcm, hc⟩ := exists_sq_class hp2 y
  rw [card_eq_one]
  refine ⟨c, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨mem_range.2 (by omega), hc⟩, ?_⟩⟩
  intro c' hc'
  have hc'' := mem_filter.1 hc'
  refine sq_class_unique (by have := mem_range.1 hc''.1; omega) hcm ?_
  have := dvd_sub hc hc''.2
  rwa [show y ^ 2 - (c : ℤ) ^ 2 - (y ^ 2 - (c' : ℤ) ^ 2) = (c' : ℤ) ^ 2 - (c : ℤ) ^ 2 by ring]
    at this

theorem J_disjoint {Nn Kn c c' : ℕ} (hc : c ≤ (p - 1) / 2) (hc' : c' ≤ (p - 1) / 2) (hne : c ≠ c') :
    Disjoint (J p Nn Kn c) (J p Nn Kn c') := by
  rw [disjoint_left]
  intro j h1 h2
  have h1 := (mem_J.1 h1).2
  have h2 := (mem_J.1 h2).2
  apply hne
  refine sq_class_unique hc hc' ?_
  have := dvd_sub h2 h1
  rwa [show (j : ℤ) ^ 2 - (c' : ℤ) ^ 2 - ((j : ℤ) ^ 2 - (c : ℤ) ^ 2) = (c : ℤ) ^ 2 - (c' : ℤ) ^ 2 by
    ring] at this

/-- The classes partition `(N, K]`. -/
theorem sum_card_J (hp2 : p ≠ 2) (Nn Kn : ℕ) :
    ∑ c ∈ range ((p - 1) / 2 + 1), #(J p Nn Kn c) = Kn - Nn := by
  simp only [J, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have : ∀ j ∈ Ioc Nn Kn, (∑ c ∈ range ((p - 1) / 2 + 1),
      if (p : ℤ) ∣ (j : ℤ) ^ 2 - (c : ℤ) ^ 2 then 1 else 0) = 1 := by
    intro j _
    rw [← sum_filter, ← card_eq_sum_ones, card_class_eq_one hp2]
  rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_one, Nat.card_Ioc]

theorem sdiff_J (hp2 : p ≠ 2) {Nn Kn c : ℕ} (hc : c ≤ (p - 1) / 2) :
    Ioc Nn Kn \ J p Nn Kn c = ((range ((p - 1) / 2 + 1)).erase c).biUnion (J p Nn Kn) := by
  ext j
  simp only [mem_sdiff, mem_Ioc, mem_biUnion, mem_erase, mem_range, mem_J]
  constructor
  · rintro ⟨hj, hnot⟩
    obtain ⟨c', hc'm, hc'⟩ := exists_sq_class hp2 (j : ℤ)
    refine ⟨c', ⟨fun h => hnot ⟨hj, h ▸ hc'⟩, by omega⟩, hj, hc'⟩
  · rintro ⟨c', ⟨hne, hc'm⟩, hj, hc'⟩
    refine ⟨hj, fun ⟨_, h⟩ => hne (sq_class_unique (by omega) hc ?_)⟩
    have := dvd_sub h hc'
    rwa [show (j : ℤ) ^ 2 - (c : ℤ) ^ 2 - ((j : ℤ) ^ 2 - (c' : ℤ) ^ 2) = (c' : ℤ) ^ 2 - (c : ℤ) ^ 2
      by ring] at this

/-- `ℓ_K(c) = ℓ_N(c) + #J_c`. -/
theorem ell_eq_add_card_J {Nn Kn c : ℕ} (hNK : Nn ≤ Kn) :
    Inner.ell p Kn c = Inner.ell p Nn c + #(J p Nn Kn c) := by
  rw [ell_eq, ell_eq, J, ← card_union_of_disjoint]
  · congr 1
    rw [← filter_union]
    congr 1
    ext j; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  · exact disjoint_filter_filter (by
      rw [disjoint_left]; intro j h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)

/-! ### Exact class sizes -/

/-- `#{1 ≤ j ≤ A | j ≡ a} = ⌊A/p⌋ + [a ≤ A mod p]` for `0 < a < p`. -/
theorem card_Icc_modEq {A a : ℕ} (ha : 0 < a) (hap : a < p) :
    #{j ∈ Icc 1 A | j ≡ a [MOD p]} = A / p + if a ≤ A % p then 1 else 0 := by
  have hp0 := hp.out.pos
  have e1 : {j ∈ Icc 1 A | j ≡ a [MOD p]} = {j ∈ range (A + 1) | j ≡ a [MOD p]} := by
    ext j
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨_, h⟩, hm⟩; exact ⟨by omega, hm⟩
    · rintro ⟨h, hm⟩
      refine ⟨⟨?_, by omega⟩, hm⟩
      by_contra h0
      have : j = 0 := by omega
      subst this
      have := hm.symm
      rw [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt hap] at this
      omega
  rw [e1, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hp0, Nat.mod_eq_of_lt hap]
  have hdm := Nat.mod_add_div A p
  have hlt := Nat.mod_lt A hp0
  by_cases hA : A % p + 1 < p
  · have h1 : (A + 1) / p = A / p ∧ (A + 1) % p = A % p + 1 :=
      (Nat.div_mod_unique hp0).2 ⟨by linarith, hA⟩
    rw [h1.1, h1.2]
    congr 1
    split_ifs <;> omega
  · have h1 : (A + 1) / p = A / p + 1 ∧ (A + 1) % p = 0 :=
      (Nat.div_mod_unique hp0).2 ⟨by rw [mul_add, mul_one]; omega, hp0⟩
    rw [h1.1, h1.2]
    have : a ≤ A % p := by omega
    simp [this]

/-- `ℓ_A(c) = 2⌊A/p⌋ + [c ≤ A mod p] + [p - c ≤ A mod p]` for `1 ≤ c ≤ m`. -/
theorem ell_exact (hp2 : p ≠ 2) {A c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    Inner.ell p A c = 2 * (A / p) + (if c ≤ A % p then 1 else 0) +
      (if p - c ≤ A % p then 1 else 0) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hsplit : Inner.ell p A c =
      #{j ∈ Icc 1 A | j ≡ c [MOD p]} + #{j ∈ Icc 1 A | j ≡ p - c [MOD p]} := by
    rw [Inner.ell, ← card_union_of_disjoint, ← filter_or]
    · congr 1
      refine filter_congr fun j _ => ?_
      have : j + c ≡ 0 [MOD p] ↔ j ≡ p - c [MOD p] := by
        constructor
        · intro h
          have := Nat.ModEq.add_right (p - c) h
          rwa [add_assoc, Nat.add_sub_cancel' (by omega), zero_add,
            Nat.ModEq, Nat.add_mod_right] at this
        · intro h
          have := Nat.ModEq.add_right c h
          rw [Nat.sub_add_cancel (by omega)] at this
          exact this.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
      rw [this]
    · refine disjoint_filter_filter' _ _ ?_
      intro q h1 h2 j hj
      have hq1 := h1 j hj
      have hq2 := h2 j hj
      have := hq1.symm.trans hq2
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
  rw [hsplit, card_Icc_modEq (by omega) (by omega), card_Icc_modEq (by omega) (by omega)]
  ring

end Outer

end Zeta5
