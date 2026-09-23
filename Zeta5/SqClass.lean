/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Data.Int.GCD
import Zeta5.Count
import Zeta5.SmallPrimes
import Zeta5.BigPrimes

/-!
# Square classes modulo `p`

For an odd prime `p` every integer `y` has a unique class `c ∈ [0, (p-1)/2]` with `y² ≡ c²`, i.e.
`y ≡ ±c (mod p)`. The counts `ℓ_A(c) = #{1 ≤ j ≤ A | j ≡ ±c}` of §4 count the `j` of the class `c`;
for `c = 0` this is `m_A = ⌊A/p⌋`.

The pulled back numerators are products of factors `c'² - y²`, `j² - y²` and `y`; at `y` of the
class `c` only the factors of the class `c` are divisible by `p`, each at least once, and at least
twice if `c = 0`. We write `κ(c) = 2` if `c = 0` and `κ(c) = 1` otherwise. The poles
`±1, …, ±K` congruent to `y` number exactly `κ(c) ℓ_K(c)`.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `κ(c)`: the multiplicity of `p` in `c'² - y²` for `c'`, `y` in the class `c`. -/
def kap (c : ℕ) : ℕ := if c = 0 then 2 else 1

theorem prime_dvd_sq_sub_sq_iff {x y : ℤ} :
    (p : ℤ) ∣ x ^ 2 - y ^ 2 ↔ (p : ℤ) ∣ x - y ∨ (p : ℤ) ∣ x + y := by
  rw [sq_sub_sq, mul_comm]
  exact (Nat.prime_iff_prime_int.mp hp.out).dvd_mul

/-- Two classes `c, c' ≤ (p-1)/2` with `c² ≡ c'²` coincide. -/
theorem sq_class_unique {c c' : ℕ} (hc : c ≤ (p - 1) / 2) (hc' : c' ≤ (p - 1) / 2)
    (h : (p : ℤ) ∣ (c : ℤ) ^ 2 - (c' : ℤ) ^ 2) : c = c' := by
  have hp1 := hp.out.two_le
  rcases prime_dvd_sq_sub_sq_iff.1 h with h | h
  · obtain ⟨k, hk⟩ := h
    have : k = 0 := by
      by_contra hk0
      have : (p : ℤ) ≤ |(p : ℤ) * k| := by
        rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < p)]
        exact le_mul_of_one_le_right (by omega) (Int.one_le_abs hk0)
      rw [← hk] at this
      have := abs_sub_lt_iff.2 ⟨(by omega : (c : ℤ) - c' < p), (by omega : (c' : ℤ) - c < p)⟩
      omega
    subst this; simp at hk; omega
  · obtain ⟨k, hk⟩ := h
    have : k = 0 := by
      by_contra hk0
      have h1 : (c : ℤ) + c' < p := by omega
      have h2 : (0 : ℤ) ≤ c + c' := by omega
      rcases lt_or_gt_of_ne hk0 with hk' | hk'
      · nlinarith
      · nlinarith
    subst this; simp at hk; omega

/-- Every integer has a class. -/
theorem exists_sq_class (hp2 : p ≠ 2) (y : ℤ) :
    ∃ c : ℕ, c ≤ (p - 1) / 2 ∧ (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2 := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  set r := y % p
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hp0.ne'
  have hrp : r < p := Int.emod_lt_of_pos _ hp0
  have hyr : (p : ℤ) ∣ y - r := Int.dvd_self_sub_emod
  rcases le_or_gt r ((p - 1) / 2 : ℕ) with h | h
  · refine ⟨r.toNat, by omega, prime_dvd_sq_sub_sq_iff.2 (Or.inl ?_)⟩
    rwa [Int.toNat_of_nonneg hr0]
  · refine ⟨(p - r).toNat, by omega, prime_dvd_sq_sub_sq_iff.2 (Or.inr ?_)⟩
    rw [Int.toNat_of_nonneg (by omega)]
    have : y + (p - r) = (y - r) + p := by ring
    rw [this]
    exact dvd_add hyr (dvd_refl _)

theorem ell_mem_iff (a j : ℕ) :
    (j ≡ a [MOD p] ∨ j + a ≡ 0 [MOD p]) ↔ (p : ℤ) ∣ (j : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
  rw [prime_dvd_sq_sub_sq_iff, Nat.modEq_iff_dvd, Nat.modEq_zero_iff_dvd, ← dvd_neg, neg_sub]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)

/-- `ℓ_A(c) = #{1 ≤ j ≤ A | j² ≡ c²}`. -/
theorem ell_eq (A c : ℕ) :
    Inner.ell p A c = #((Icc 1 A).filter fun j : ℕ => (p : ℤ) ∣ (j : ℤ) ^ 2 - (c : ℤ) ^ 2) := by
  unfold Inner.ell
  exact congrArg Finset.card (filter_congr fun j _ => ell_mem_iff (p := p) c j)

omit hp in
theorem dvd_sq_sub_of_class {y : ℤ} {c : ℕ} (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) (x : ℤ) :
    (p : ℤ) ∣ x ^ 2 - (c : ℤ) ^ 2 ↔ (p : ℤ) ∣ x ^ 2 - y ^ 2 := by
  constructor
  · intro h; have := dvd_sub h hc; rwa [show x ^ 2 - (c : ℤ) ^ 2 - (y ^ 2 - (c : ℤ) ^ 2) =
      x ^ 2 - y ^ 2 by ring] at this
  · intro h; have := dvd_add h hc; rwa [show x ^ 2 - y ^ 2 + (y ^ 2 - (c : ℤ) ^ 2) =
      x ^ 2 - (c : ℤ) ^ 2 by ring] at this

theorem dvd_of_class_zero {y : ℤ} (hc : (p : ℤ) ∣ y ^ 2 - ((0 : ℕ) : ℤ) ^ 2) : (p : ℤ) ∣ y := by
  have : (p : ℤ) ∣ y ^ 2 := by simpa using hc
  exact (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow this

/-- At `y` of the class `c`, a factor `x² - y²` with `x` of the class `c` has `v_p ≥ κ(c)`. -/
theorem VGe_sq_sub_sq {y : ℤ} {c : ℕ} (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) {x : ℤ}
    (hx : (p : ℤ) ∣ x ^ 2 - (c : ℤ) ^ 2) : VGe p (kap c) (((x ^ 2 - y ^ 2 : ℤ)) : ℚ) := by
  unfold kap
  split_ifs with h0
  · subst h0
    have hy := dvd_of_class_zero hc
    have hx' := dvd_of_class_zero hx
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hx'
    have : (((p : ℤ) * b) ^ 2 - ((p : ℤ) * a) ^ 2 : ℤ) = (p : ℤ) ^ 2 * (b ^ 2 - a ^ 2) := by ring
    rw [this]
    have := (VGe_p_pow (p := p) 2).mul (VGe_intCast (p := p) (b ^ 2 - a ^ 2))
    push_cast at this ⊢
    simpa using this
  · exact VGe_of_dvd_int ((dvd_sq_sub_of_class hc x).1 hx)

/-- The poles `s ∈ {±1, …, ±K}` with `s ≡ y` number `κ(c) ℓ_K(c)`. -/
theorem card_RK_dvd (hp2 : p ≠ 2) {K : ℕ} {y : ℤ} {c : ℕ} (hcm : c ≤ (p - 1) / 2)
    (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) :
    #{s ∈ RK K | (p : ℤ) ∣ y - s} = kap c * Inner.ell p K c := by
  classical
  have hsplit : {s ∈ RK K | (p : ℤ) ∣ y - s} =
      ((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y - (j : ℤ))).image (fun j : ℕ => (j : ℤ)) ∪
        ((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y + (j : ℤ))).image (fun j : ℕ => -(j : ℤ)) := by
    ext s
    simp only [mem_filter, RK, mem_erase, mem_Icc, mem_union, mem_image]
    constructor
    · rintro ⟨⟨hs0, hs1, hs2⟩, hd⟩
      rcases le_or_gt 0 s with h | h
      · exact Or.inl ⟨s.toNat, ⟨⟨by omega, by omega⟩, by rwa [Int.toNat_of_nonneg h]⟩,
          Int.toNat_of_nonneg h⟩
      · exact Or.inr ⟨(-s).toNat, ⟨⟨by omega, by omega⟩, by
          rwa [Int.toNat_of_nonneg (by omega), show y + -s = y - s by ring]⟩, by omega⟩
    · rintro (⟨j, ⟨⟨h1, h2⟩, hd⟩, rfl⟩ | ⟨j, ⟨⟨h1, h2⟩, hd⟩, rfl⟩)
      · exact ⟨⟨by omega, by omega, by omega⟩, hd⟩
      · exact ⟨⟨by omega, by omega, by omega⟩, by rwa [show y - -(j : ℤ) = y + j by ring]⟩
  have hdisj : Disjoint
      (((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y - (j : ℤ))).image (fun j : ℕ => (j : ℤ)))
      (((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y + (j : ℤ))).image (fun j : ℕ => -(j : ℤ))) := by
    rw [disjoint_left]
    intro s h1 h2
    simp only [mem_image, mem_filter, mem_Icc] at h1 h2
    obtain ⟨i, ⟨⟨hi, _⟩, _⟩, rfl⟩ := h1
    obtain ⟨j, ⟨⟨hj, _⟩, _⟩, hij⟩ := h2
    omega
  rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injective _ Nat.cast_injective,
    card_image_of_injective _ (fun a b h => by simpa using h), ell_eq]
  unfold kap
  split_ifs with h0
  · subst h0
    have hy := dvd_of_class_zero hc
    have e1 : ∀ j : ℕ, (p : ℤ) ∣ y - j ↔ (p : ℤ) ∣ (j : ℤ) ^ 2 - ((0 : ℕ) : ℤ) ^ 2 := by
      intro j
      rw [show (j : ℤ) ^ 2 - ((0 : ℕ) : ℤ) ^ 2 = j * j by push_cast; ring]
      constructor
      · intro h; exact Dvd.dvd.mul_right (by simpa using dvd_sub hy h) _
      · intro h
        rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_mul.1 h with h | h <;>
          exact dvd_sub hy h
    have e2 : ∀ j : ℕ, (p : ℤ) ∣ y + j ↔ (p : ℤ) ∣ (j : ℤ) ^ 2 - ((0 : ℕ) : ℤ) ^ 2 := by
      intro j
      rw [← e1]
      constructor
      · intro h; have := dvd_sub (dvd_mul_of_dvd_right hy 2) h
        rw [show 2 * y - (y + j) = y - j by ring] at this; exact this
      · intro h; have := dvd_sub (dvd_mul_of_dvd_right hy 2) h
        rw [show 2 * y - (y - j) = y + j by ring] at this; exact this
    rw [filter_congr fun j _ => e1 j, filter_congr fun j _ => e2 j]
    ring
  · have hdisj' : Disjoint ((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y - (j : ℤ)))
        ((Icc 1 K).filter (fun j : ℕ => (p : ℤ) ∣ y + (j : ℤ))) := by
      rw [disjoint_filter]
      intro j _ h1 h2
      have h2y : (p : ℤ) ∣ 2 * y := by have := dvd_add h1 h2; rwa [show y - j + (y + j) = 2 * y by
        ring] at this
      have hy : (p : ℤ) ∣ y := by
        rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_mul.1 h2y with h | h
        · have := Int.le_of_dvd (by norm_num) h
          have := hp.out.two_le
          have : p = 2 := by omega
          exact absurd this hp2
        · exact h
      have hc2 : (p : ℤ) ∣ (c : ℤ) ^ 2 := by
        have := dvd_sub (dvd_pow hy (by norm_num : 2 ≠ 0)) hc
        rwa [show y ^ 2 - (y ^ 2 - (c : ℤ) ^ 2) = (c : ℤ) ^ 2 by ring] at this
      have hc0 := (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hc2
      have := Int.le_of_dvd (by omega) hc0
      omega
    rw [one_mul, ← card_union_of_disjoint hdisj', ← filter_or]
    congr 1
    refine filter_congr fun j _ => ?_
    rw [dvd_sq_sub_of_class hc, prime_dvd_sq_sub_sq_iff, ← dvd_neg, neg_sub]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by rwa [add_comm])
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by rwa [add_comm])

end Zeta5
