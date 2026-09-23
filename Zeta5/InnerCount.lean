/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.SqClass

/-!
# The allocation (4.4)–(4.7)

Counting facts for the inner range:

* `p ℓ_A(a) ≤ 2A + p` and `ℓ_K(a) ≥ 2 m_K` for the ordinary classes `1 ≤ a ≤ (p-1)/2`;
* the ranks of the classes in decreasing order of `ℓ_K` are a bijection onto `0, …, m-1`, so
  exactly `E` classes get an extra row, and a class with an extra row has `ℓ_K` at least that of a
  class without one;
* `∑_{a=1}^m ℓ_N(a) = N - m_N`.
-/

open Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The counts `ℓ_A(a)` -/

omit hp in
theorem ell_eq_zero_class (A : ℕ) : Inner.ell p A 0 = A / p := by
  rw [Inner.ell, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc, add_zero, Nat.modEq_zero_iff_dvd, or_self]
  omega

omit hp in
theorem ell_le_filter_add (A a : ℕ) :
    Inner.ell p A a ≤ #{j ∈ Icc 1 A | j % p = a % p} + #{j ∈ Icc 1 A | (j + a) % p = 0} := by
  rw [Inner.ell, filter_or]
  exact card_union_le _ _

theorem card_mod_eq_mul_le {A a : ℕ} (hap : a < p) :
    #{j ∈ Icc 1 A | j % p = a % p} * p + a ≤ A + p := by
  have hp0 := hp.out.pos
  rw [Nat.mod_eq_of_lt hap]
  by_cases hA : a ≤ A
  · have hle : #{j ∈ Icc 1 A | j % p = a} ≤ #(range ((A - a) / p + 1)) := by
      refine card_le_card_of_injOn (fun j => j / p) (fun j hj => ?_) (fun i hi j hj h => ?_)
      · simp only [mem_coe, mem_filter, mem_Icc] at hj
        simp only [mem_coe, mem_range]
        have := Nat.div_add_mod j p
        rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hp0]
        rw [hj.2] at this
        have := Nat.mul_comm p (j / p)
        omega
      · simp only [mem_coe, mem_filter, mem_Icc] at hi hj
        have h1 := Nat.div_add_mod i p
        have h2 := Nat.div_add_mod j p
        simp only at h
        rw [hi.2] at h1; rw [hj.2] at h2
        rw [← h1, ← h2, h]
    rw [card_range] at hle
    have := Nat.div_mul_le_self (A - a) p
    have := Nat.mul_le_mul_right p hle
    rw [add_mul, one_mul] at this
    omega
  · have : #{j ∈ Icc 1 A | j % p = a} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro j hj h
      have := Nat.mod_le j p
      simp only [mem_Icc] at hj
      omega
    rw [this]; omega

theorem card_add_mod_mul_le {A a : ℕ} :
    #{j ∈ Icc 1 A | (j + a) % p = 0} * p ≤ A + a := by
  have hp0 := hp.out.pos
  have hle : #{j ∈ Icc 1 A | (j + a) % p = 0} ≤ #(range ((A + a) / p)) := by
    refine card_le_card_of_injOn (fun j => (j + a) / p - 1) (fun j hj => ?_) (fun i hi j hj h => ?_)
    · simp only [mem_coe, mem_filter, mem_Icc] at hj
      simp only [mem_coe, mem_range]
      have h1 : 1 ≤ (j + a) / p := by
        rw [Nat.le_div_iff_mul_le hp0, one_mul]
        exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hj.2)
      have h2 : (j + a) / p ≤ (A + a) / p := Nat.div_le_div_right (by omega)
      omega
    · simp only [mem_coe, mem_filter, mem_Icc] at hi hj
      have h1 := Nat.div_add_mod (i + a) p
      have h2 := Nat.div_add_mod (j + a) p
      rw [hi.2] at h1; rw [hj.2] at h2
      have hi1 : 1 ≤ (i + a) / p := by
        rw [Nat.le_div_iff_mul_le hp0, one_mul]
        exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hi.2)
      have hj1 : 1 ≤ (j + a) / p := by
        rw [Nat.le_div_iff_mul_le hp0, one_mul]
        exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hj.2)
      simp only at h
      have : (i + a) / p = (j + a) / p := by omega
      have : i + a = j + a := by rw [← h1, ← h2, this]
      omega
  rw [card_range] at hle
  have := Nat.div_mul_le_self (A + a) p
  have := Nat.mul_le_mul_right p hle
  omega

/-- `p ℓ_A(a) ≤ 2A + p` for `0 < a < p`. -/
theorem ell_mul_le {A a : ℕ} (hap : a < p) : Inner.ell p A a * p ≤ 2 * A + p := by
  have h := ell_le_filter_add (p := p) A a
  have h1 := card_mod_eq_mul_le (p := p) (A := A) hap
  have h2 := card_add_mod_mul_le (p := p) (A := A) (a := a)
  nlinarith

/-- `ℓ_A(a) ≥ 2 m_A` for `1 ≤ a ≤ (p-1)/2`. -/
theorem two_mul_div_le_ell {A a : ℕ} (ha : 1 ≤ a) (ham : a ≤ (p - 1) / 2) :
    2 * (A / p) ≤ Inner.ell p A a := by
  have hp0 := hp.out.pos
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set m := A / p
  have hmA : m * p ≤ A := Nat.div_mul_le_self A p
  set f : ℕ ⊕ ℕ → ℕ := fun x => Sum.elim (fun k => a + k * p) (fun k => (k + 1) * p - a) x
  have himg : ((range m).disjSum (range m)).image f ⊆
      {j ∈ Icc 1 A | j ≡ a [MOD p] ∨ j + a ≡ 0 [MOD p]} := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hj
    rcases x with k | k
    · simp only [inl_mem_disjSum, mem_range] at hx
      simp only [f, Sum.elim_inl, mem_filter, mem_Icc]
      refine ⟨⟨by omega, ?_⟩, Or.inl ?_⟩
      · have : (k + 1) * p ≤ m * p := Nat.mul_le_mul_right _ hx
        rw [add_mul, one_mul] at this
        omega
      · simp [Nat.ModEq, Nat.add_mul_mod_self_right]
    · simp only [inr_mem_disjSum, mem_range] at hx
      simp only [f, Sum.elim_inr, mem_filter, mem_Icc]
      have h1 : (k + 1) * p ≤ m * p := Nat.mul_le_mul_right _ hx
      have h2 : p ≤ (k + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      refine ⟨⟨by omega, by omega⟩, Or.inr ?_⟩
      rw [Nat.sub_add_cancel (by omega), Nat.modEq_zero_iff_dvd]
      exact Dvd.intro_left _ rfl
  have hinj : Set.InjOn f ((range m).disjSum (range m) : Set (ℕ ⊕ ℕ)) := by
    intro x hx y hy h
    rcases x with k | k <;> rcases y with l | l <;> simp only [f, Sum.elim_inl, Sum.elim_inr] at h
    · have : k * p = l * p := by omega
      simp [Nat.eq_of_mul_eq_mul_right hp0 this]
    · -- `a + kp ≡ a` but `(l+1)p - a ≡ -a`
      exfalso
      have h1 : p ≤ (l + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      have : (a + k * p + a) % p = 0 := by
        rw [h, Nat.sub_add_cancel (by omega)]; simp
      rw [show a + k * p + a = 2 * a + k * p by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)] at this
      omega
    · exfalso
      have h1 : p ≤ (k + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      have : (a + l * p + a) % p = 0 := by
        rw [← h, Nat.sub_add_cancel (by omega)]; simp
      rw [show a + l * p + a = 2 * a + l * p by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)] at this
      omega
    · have h1 : p ≤ (k + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : p ≤ (l + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      have : (k + 1) * p = (l + 1) * p := by omega
      have := Nat.eq_of_mul_eq_mul_right hp0 this
      simp; omega
  have := card_le_card himg
  rw [card_image_of_injOn hinj, card_disjSum, card_range] at this
  rw [Inner.ell]; omega

/-! ### The ranks -/

section Rank

variable (s : Finset ℕ) (ℓ : ℕ → ℕ)

/-- `c ≺ a`: `c` comes before `a` in decreasing order of `ℓ`, ties by index. -/
def Prec (c a : ℕ) : Prop := ℓ a < ℓ c ∨ (ℓ c = ℓ a ∧ c < a)

/-- The position of `a` in decreasing order of `ℓ`. -/
def rk (a : ℕ) : ℕ := #{c ∈ s | ℓ a < ℓ c ∨ (ℓ c = ℓ a ∧ c < a)}

variable {s ℓ}

theorem rk_lt_rk {c a : ℕ} (hc : c ∈ s) (h : Prec ℓ c a) : rk s ℓ c < rk s ℓ a := by
  unfold rk Prec at *
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have := hsub (mem_filter.2 ⟨hc, h⟩)
    simp only [mem_filter] at this
    omega

theorem rk_injOn : Set.InjOn (rk s ℓ) s := by
  intro a ha c hc h
  by_contra hne
  have : Prec ℓ c a ∨ Prec ℓ a c := by unfold Prec; omega
  rcases this with h' | h'
  · exact absurd h.symm (rk_lt_rk hc h').ne
  · exact absurd h (rk_lt_rk ha h').ne

theorem rk_lt_card {a : ℕ} (ha : a ∈ s) : rk s ℓ a < #s := by
  refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
  have := h ha
  simp only [mem_filter] at this
  omega

theorem image_rk : s.image (rk s ℓ) = range #s := by
  refine eq_of_subset_of_card_le (fun k hk => ?_) ?_
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hk
    exact mem_range.2 (rk_lt_card ha)
  · rw [card_range, card_image_of_injOn rk_injOn]

/-- Exactly `E` classes have rank `< E`. -/
theorem card_rk_lt {E : ℕ} (hE : E ≤ #s) : #{a ∈ s | rk s ℓ a < E} = E := by
  have : #{a ∈ s | rk s ℓ a < E} = #((s.image (rk s ℓ)).filter (· < E)) := by
    rw [filter_image, card_image_of_injOn (rk_injOn.mono (filter_subset _ _))]
  rw [this, image_rk]
  have : (range #s).filter (· < E) = range E := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

end Rank

omit hp in
theorem rank_eq_rk (n a : ℕ) :
    Inner.rank p n a = rk (Inner.classes p) (Inner.ell p (K n)) a := rfl

/-! ### The sum of `ℓ_N` over the ordinary classes -/

theorem card_classes_of_mem (hp2 : p ≠ 2) (j : ℕ) :
    #{a ∈ Inner.classes p | j ≡ a [MOD p] ∨ j + a ≡ 0 [MOD p]} = if p ∣ j then 0 else 1 := by
  simp_rw [ell_mem_iff (p := p)]
  split_ifs with hdvd
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro a ha h
    have ha' := mem_Icc.1 ha
    have hj2 : (p : ℤ) ∣ (j : ℤ) ^ 2 := dvd_pow (by exact_mod_cast hdvd) (by norm_num)
    have : (p : ℤ) ∣ (a : ℤ) ^ 2 := by
      have := dvd_sub hj2 h; rwa [sub_sub_cancel] at this
    have := (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow this
    have := Int.le_of_dvd (by omega) this
    omega
  · obtain ⟨c, hcm, hc⟩ := exists_sq_class hp2 (j : ℤ)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hdvd (by exact_mod_cast dvd_of_class_zero hc)
    rw [card_eq_one]
    refine ⟨c, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨by omega, hcm⟩, hc⟩, ?_⟩⟩
    intro a ha
    have ha' := mem_filter.1 ha
    have hmem := mem_Icc.1 ha'.1
    refine sq_class_unique hmem.2 hcm ?_
    have := dvd_sub hc ha'.2
    rwa [show (j : ℤ) ^ 2 - (c : ℤ) ^ 2 - ((j : ℤ) ^ 2 - (a : ℤ) ^ 2) = (a : ℤ) ^ 2 - (c : ℤ) ^ 2 by
      ring] at this

/-- `∑_{a=1}^m ℓ_N(a) = N - m_N`. -/
theorem sum_ell_classes (hp2 : p ≠ 2) (A : ℕ) :
    ∑ a ∈ Inner.classes p, Inner.ell p A a = A - A / p := by
  simp only [Inner.ell, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have : ∀ j ∈ Icc 1 A, (∑ a ∈ Inner.classes p,
      if j ≡ a [MOD p] ∨ j + a ≡ 0 [MOD p] then 1 else 0) = if p ∣ j then 0 else 1 := by
    intro j hj
    rw [← sum_filter, ← card_eq_sum_ones, card_classes_of_mem hp2 j]
  rw [sum_congr rfl this, sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one,
    filter_not, card_sdiff_of_subset (filter_subset _ _), Nat.card_Icc]
  have := Nat.Ioc_filter_dvd_card_eq_div A p
  have e : Icc 1 A = Ioc 0 A := by ext; simp; omega
  rw [e, this]
  omega

end Zeta5
