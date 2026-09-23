/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Count
import Zeta5.Binom
import Zeta5.LocalTau

/-!
# Small primes: Lemma 3.3

For `R_K = {-K, …, K} \ {0}` and an integer-valued polynomial `A` of degree `< 5K`,
`v_p^G(τ_X((K!)² A / ∏_{r ∈ R_K} (x - r))) ≥ -6 ⌊log_p(5K)⌋`. This is (3.10) without the term
`-v_p(24)`, which our form (3.9) of the value bound does not lose.

We expand `A` in the binomial basis `C(x + K, k)`. For `k ≤ 2K` only the simple poles contribute;
their residues are `C(r + K, k) (K!)² / ∏_{s ≠ r} (r - s)` and lose at most `⌊log_p(2K)⌋`. For
`k > 2K` there are no poles, and the polynomial `(K!)² C(x + K, k) / ∏ (x - r)` takes values of
valuation `≥ -2 ⌊log_p k⌋` at the integers, by counting multiples of each `p^j`.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Legendre's counting -/

/-- `v_p(n) = #{1 ≤ j < B | p^j ∣ n}` for a nonzero integer `|n| < p^B`. -/
theorem padicValInt_eq_card {n : ℤ} (hn : n ≠ 0) {B : ℕ} (hB : n.natAbs < p ^ B) :
    (padicValInt p n : ℤ) = #{j ∈ Ico 1 B | (p : ℤ) ^ j ∣ n} := by
  have hv : padicValInt p n < B := by
    have h2 := Int.natAbs_dvd_natAbs.2 (padicValInt_dvd (p := p) n)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.2 hn) h2
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_lt h3 hB)
  have : {j ∈ Ico 1 B | (p : ℤ) ^ j ∣ n} = Icc 1 (padicValInt p n) := by
    ext j
    simp only [mem_filter, mem_Ico, mem_Icc, padicValInt_dvd_iff, hn, false_or]
    omega
  rw [this, Nat.card_Icc]
  simp

theorem padicValRat_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
      (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- Legendre's counting for a product of nonzero integers `|f i| < p^B`. -/
theorem padicValRat_prod_int {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i ≠ 0)
    {B : ℕ} (hB : ∀ i ∈ s, (f i).natAbs < p ^ B) :
    padicValRat p (∏ i ∈ s, (f i : ℚ)) = ∑ j ∈ Ico 1 B, (#{i ∈ s | (p : ℤ) ^ j ∣ f i} : ℤ) := by
  rw [padicValRat_prod _ _ fun i hi => by exact_mod_cast hf i hi]
  simp only [padicValRat.of_int]
  rw [sum_congr rfl fun i hi => padicValInt_eq_card (hf i hi) (hB i hi)]
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]

/-- `v_p(∏_{a < i ≤ b} i) = ∑_j mcnt a b p^j`. -/
theorem padicValRat_prod_Ioc {a b : ℤ} (h0 : (0 : ℤ) ∉ Ioc a b) {B : ℕ}
    (hB : ∀ i ∈ Ioc a b, i.natAbs < p ^ B) :
    padicValRat p (∏ i ∈ Ioc a b, (i : ℚ)) = ∑ j ∈ Ico 1 B, (mcnt a b (p ^ j) : ℤ) := by
  have := padicValRat_prod_int (p := p) _ id (fun i hi h => h0 (h ▸ hi)) hB
  simpa [mcnt] using this

theorem padicValRat_factorial (n : ℕ) {B : ℕ} (hB : Nat.log p n < B) :
    padicValRat p (n.factorial : ℚ) = ∑ j ∈ Ico 1 B, ((n / p ^ j : ℕ) : ℤ) := by
  rw [padicValRat.of_nat, padicValNat_factorial hB]
  push_cast; rfl

/-- `#{1 ≤ j < B | p^j ≤ n} = ⌊log_p n⌋`. -/
theorem card_pow_le {n B : ℕ} (hn : n ≠ 0) (hB : Nat.log p n < B) :
    #{j ∈ Ico 1 B | p ^ j ≤ n} = Nat.log p n := by
  have : {j ∈ Ico 1 B | p ^ j ≤ n} = Icc 1 (Nat.log p n) := by
    ext j
    simp only [mem_filter, mem_Ico, mem_Icc, ← Nat.le_log_iff_pow_le hp.out.one_lt hn]
    omega
  rw [this, Nat.card_Icc]; omega

/-- A sum of per-level bounds `c_j ≥ -e · [p^j ≤ n]`. -/
theorem sum_ge_of_levels {n B : ℕ} (hn : n ≠ 0) (hB : Nat.log p n < B) (e : ℤ) (c : ℕ → ℤ)
    (hc : ∀ j ∈ Ico 1 B, (if p ^ j ≤ n then -e else 0) ≤ c j) :
    -e * Nat.log p n ≤ ∑ j ∈ Ico 1 B, c j := by
  have h := sum_le_sum hc
  rw [sum_ite, sum_const_zero, add_zero, sum_const, card_pow_le hn hB, nsmul_eq_mul] at h
  linarith

/-! ### Reindexing products -/

theorem prod_Ioc_sub (y a b : ℤ) :
    ∏ s ∈ Ioc a b, ((y : ℚ) - s) = ∏ i ∈ Ioc (y - b - 1) (y - a - 1), (i : ℚ) := by
  refine prod_nbij' (fun s => y - s) (fun i => y - i) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [mem_Ioc] at hs ⊢; omega
  · intro s hs; simp only [mem_Ioc] at hs ⊢; omega
  · intro s _; simp
  · intro s _; simp
  · intro s _; push_cast; ring

/-! ### Harmonic numbers -/

theorem VGe_H5 {m K : ℕ} (hm : m ≤ K) : VGe p (-5 * Nat.log p K) (H5 m) := by
  refine VGe_sum _ fun v hv => ?_
  have hv' := mem_Icc.1 hv
  have h := VGe_inv_nat (p := p) (i := v) (by omega)
    (lt_of_le_of_lt (hv'.2.trans hm) (Nat.lt_pow_succ_log_self hp.out.one_lt K))
  have := VGe_prod (p := p) (range 5) (w := fun _ => -(Nat.log p K : ℤ))
    (f := fun _ => (v : ℚ)⁻¹) fun _ _ => h
  simp only [prod_const, card_range, sum_const, smul_neg, nsmul_eq_mul] at this
  rw [one_div, ← inv_pow]
  refine this.mono ?_
  push_cast; omega

/-! ### The values of the polynomial part (Lemma 3.3, `k > 2K`) -/

theorem add_pred_div_le (K q : ℕ) (hq : 0 < q) : (K + q - 1) / q ≤ K / q + 1 := by
  calc (K + q - 1) / q ≤ (K + q) / q := Nat.div_le_div_right (by omega)
    _ = K / q + 1 := Nat.add_div_right K hq

theorem two_mul_div_le (K q : ℕ) (hq : 0 < q) : 2 * K / q ≤ 2 * (K / q) + 1 := by
  have h1 := Nat.lt_div_mul_add (a := K) hq
  refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hq).2 ?_)
  nlinarith

/-- The values `(K!)²/k! · y ∏_{K < s ≤ K + m} (y - s)` (`k = 2K + 1 + m`) of the polynomial part
have valuation `≥ -2 ⌊log_p k⌋`: at each level `p^j ≤ k` the window of length `k` around `y`
contains at least `⌊k/p^j⌋` multiples, of which at most `2 ⌊K/p^j⌋ + 2` are not counted. -/
theorem VGe_Qval (K m : ℕ) (y : ℤ) :
    VGe p (-2 * Nat.log p (2 * K + 1 + m))
      ((K.factorial : ℚ) ^ 2 / (2 * K + 1 + m).factorial *
        ((y : ℚ) * ∏ s ∈ Ioc (K : ℤ) (K + m), ((y : ℚ) - s))) := by
  set k := 2 * K + 1 + m with hk
  rw [prod_Ioc_sub]
  set a := y - (K + m) - 1
  set b := y - K - 1
  by_cases hz : (y : ℚ) * ∏ i ∈ Ioc a b, (i : ℚ) = 0
  · rw [hz, mul_zero]; exact VGe_zero _
  have hy : y ≠ 0 := fun h => hz (by rw [h]; simp)
  have h0 : (0 : ℤ) ∉ Ioc a b := fun h =>
    hz (mul_eq_zero_of_right _ (prod_eq_zero h (by simp)))
  have h0' : (0 : ℤ) ∉ Ioc (y - 1) y := by simp only [mem_Ioc]; omega
  refine VGe_of_padicValRat fun _ => ?_
  set B := y.natAbs + k + 1
  have hpB : B < p ^ B := Nat.lt_pow_self hp.out.one_lt
  have hBi : ∀ i ∈ Ioc a b, i.natAbs < p ^ B := fun i hi => by
    have := mem_Ioc.1 hi; omega
  have hBy : ∀ i ∈ Ioc (y - 1) y, i.natAbs < p ^ B := fun i hi => by
    have := mem_Ioc.1 hi; omega
  have hlogK : Nat.log p K < B := (Nat.log_le_self p K).trans_lt (by omega)
  have hlogk : Nat.log p k < B := (Nat.log_le_self p k).trans_lt (by omega)
  have hyprod : (y : ℚ) = ∏ i ∈ Ioc (y - 1) y, (i : ℚ) := by
    rw [show Ioc (y - 1) y = {y} by ext i; simp only [mem_Ioc, mem_singleton]; omega]; simp
  have hKf : (K.factorial : ℚ) ≠ 0 := by positivity
  have hkf : (k.factorial : ℚ) ≠ 0 := by positivity
  have hprod : ∏ i ∈ Ioc a b, (i : ℚ) ≠ 0 := right_ne_zero_of_mul hz
  rw [padicValRat.mul (div_ne_zero (pow_ne_zero 2 hKf) hkf) hz, padicValRat.div
    (pow_ne_zero 2 hKf) hkf, padicValRat.pow _, padicValRat.mul (by exact_mod_cast hy) hprod,
    hyprod, padicValRat_factorial K hlogK, padicValRat_factorial k hlogk,
    padicValRat_prod_Ioc h0' hBy, padicValRat_prod_Ioc h0 hBi]
  have key : ∑ j ∈ Ico 1 B, (2 * ((K / p ^ j : ℕ) : ℤ) - ((k / p ^ j : ℕ) : ℤ) +
      (mcnt (y - 1) y (p ^ j) + mcnt a b (p ^ j) : ℤ)) =
      (2 : ℕ) * ∑ j ∈ Ico 1 B, ((K / p ^ j : ℕ) : ℤ) - ∑ j ∈ Ico 1 B, ((k / p ^ j : ℕ) : ℤ) +
        (∑ j ∈ Ico 1 B, (mcnt (y - 1) y (p ^ j) : ℤ) + ∑ j ∈ Ico 1 B, (mcnt a b (p ^ j) : ℤ)) := by
    rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, mul_sum]; push_cast; rfl
  rw [← key]
  refine sum_ge_of_levels (by omega) hlogk 2 _ fun j _ => ?_
  have hq : 0 < p ^ j := pow_pos hp.out.pos j
  split_ifs with hjk
  · -- the window `(a, y + K]` of length `k`
    have hw := mcnt_ge a k hq
    rw [show a + (k : ℤ) = y + K by omega] at hw
    have e1 := mcnt_add (show a ≤ b by omega) (show b ≤ y + K by omega) (p ^ j)
    have e2 := mcnt_add (show b ≤ y - 1 by omega) (show y - 1 ≤ y + K by omega) (p ^ j)
    have e3 := mcnt_add (show y - 1 ≤ y by omega) (show y ≤ y + K by omega) (p ^ j)
    have u1 := mcnt_le b K hq
    rw [show b + (K : ℤ) = y - 1 by omega] at u1
    have u2 := mcnt_le y K hq
    have v := add_pred_div_le K (p ^ j) hq
    generalize K / p ^ j = u at *
    generalize k / p ^ j = w at *
    generalize (K + p ^ j - 1) / p ^ j = z at *
    omega
  · have : k / p ^ j = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]
    generalize K / p ^ j = u at *
    omega

/-! ### The residues (Lemma 3.3, `k ≤ 2K`) -/

/-- `R_K = {-K, …, K} \ {0}`, the poles of the pulled back `1 / D_K`. -/
def RK (K : ℕ) : Finset ℤ := (Icc (-(K : ℤ)) K).erase 0

theorem poleSet_Icc (K : ℕ) : poleSet (Icc 1 K) = RK K := by
  ext r
  simp only [poleSet, RK, mem_union, mem_image, mem_Icc, mem_erase]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · intro h
    rcases le_or_gt 0 r with hr | hr
    · exact Or.inl ⟨r.toNat, by omega, by omega⟩
    · exact Or.inr ⟨(-r).toNat, by omega, by omega⟩

/-- For `r ∈ R_K`, `v_p((K!)² / ∏_{s ∈ R_K, s ≠ r} (r - s)) ≥ -⌊log_p(2K)⌋`: the factors `r - s` run
over `[r - K, r + K] \ {0}`, which contains at most `⌊2K/p^j⌋ ≤ 2⌊K/p^j⌋ + 1` multiples of `p^j`. -/
theorem VGe_resid_factor {K : ℕ} {r : ℤ} (hr : r ∈ RK K) :
    VGe p (-Nat.log p (2 * K)) ((K.factorial : ℚ) ^ 2 / ∏ s ∈ (RK K).erase r, ((r : ℚ) - s)) := by
  have hr' := mem_erase.1 hr
  have hr0 : r ≠ 0 := hr'.1
  have hrI := mem_Icc.1 hr'.2
  have hK : 1 ≤ K := by omega
  -- `r ∏_{s ∈ R_K \ {r}} (r - s) = ∏_{i ∈ (r - K - 1, r + K] \ {0}} i`
  have hmul : (r : ℚ) * ∏ s ∈ (RK K).erase r, ((r : ℚ) - s) =
      ∏ i ∈ (Ioc (r - K - 1) (r + K)).erase 0, (i : ℚ) := by
    have h0mem : (0 : ℤ) ∈ (Icc (-(K : ℤ)) K).erase r := mem_erase.2 ⟨hr0.symm, by simp⟩
    have := mul_prod_erase _ (fun s : ℤ => (r : ℚ) - s) h0mem
    simp only [Int.cast_zero, sub_zero] at this
    rw [RK, erase_right_comm, this]
    refine prod_nbij' (fun s => r - s) (fun i => r - i) ?_ ?_ ?_ ?_ ?_
    · intro s hs; simp only [mem_erase, mem_Icc, mem_Ioc] at hs ⊢; omega
    · intro s hs; simp only [mem_erase, mem_Icc, mem_Ioc] at hs ⊢; omega
    · intro s _; simp
    · intro s _; simp
    · intro s _; push_cast; ring
  have hne : ∏ i ∈ (Ioc (r - K - 1) (r + K)).erase 0, (i : ℚ) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi => by exact_mod_cast (mem_erase.1 hi).1
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
  have hKf : (K.factorial : ℚ) ≠ 0 := by positivity
  have heq : (K.factorial : ℚ) ^ 2 / ∏ s ∈ (RK K).erase r, ((r : ℚ) - s) =
      (r : ℚ) * (K.factorial : ℚ) ^ 2 / ∏ i ∈ (Ioc (r - K - 1) (r + K)).erase 0, (i : ℚ) := by
    rw [← hmul, mul_div_mul_left _ _ hrq]
  rw [heq]
  refine VGe_of_padicValRat fun _ => ?_
  set B := 2 * K + r.natAbs + 1
  have hpB : B < p ^ B := Nat.lt_pow_self hp.out.one_lt
  have hlogK : Nat.log p K < B := (Nat.log_le_self p K).trans_lt (by omega)
  have hlog2K : Nat.log p (2 * K) < B := (Nat.log_le_self p _).trans_lt (by omega)
  have hBi : ∀ i ∈ (Ioc (r - K - 1) (r + K)).erase 0, i.natAbs < p ^ B := fun i hi => by
    have := mem_Ioc.1 (mem_of_mem_erase hi); omega
  rw [padicValRat.div (mul_ne_zero hrq (pow_ne_zero 2 hKf)) hne,
    padicValRat.mul hrq (pow_ne_zero 2 hKf), padicValRat.pow _,
    padicValRat_factorial K hlogK]
  have hP := padicValRat_prod_int (p := p) _ id (fun i hi => (mem_erase.1 hi).1) hBi
  simp only [id] at hP
  rw [hP]
  have hr_nonneg : (0 : ℤ) ≤ padicValRat p (r : ℚ) := by
    rw [padicValRat.of_int]; exact Nat.cast_nonneg _
  have hcnt : ∀ j ∈ Ico 1 B, (#{i ∈ (Ioc (r - K - 1) (r + K)).erase 0 | (p : ℤ) ^ j ∣ i} : ℤ)
      ≤ 2 * ((K / p ^ j : ℕ) : ℤ) + (if p ^ j ≤ 2 * K then 1 else 0) := by
    intro j _
    have hq : 0 < p ^ j := pow_pos hp.out.pos j
    rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨by simp only [mem_Ioc]; omega, by simp⟩)]
    have hc := mcnt_le (r - K - 1) (2 * K + 1) hq
    rw [show r - K - 1 + ((2 * K + 1 : ℕ) : ℤ) = r + K by push_cast; ring,
      show 2 * K + 1 + p ^ j - 1 = 2 * K + p ^ j by omega, Nat.add_div_right _ hq] at hc
    have hc' : #{i ∈ Ioc (r - K - 1) (r + K) | (p : ℤ) ^ j ∣ i} =
        mcnt (r - K - 1) (r + K) (p ^ j) := by
      simp [mcnt]
    have hpos : 1 ≤ mcnt (r - K - 1) (r + K) (p ^ j) := by
      rw [← hc']; exact card_pos.2 ⟨0, mem_filter.2 ⟨by simp only [mem_Ioc]; omega, by simp⟩⟩
    rw [hc', Nat.cast_sub hpos]
    split_ifs with hj
    · have := two_mul_div_le K (p ^ j) hq
      generalize K / p ^ j = u at *
      generalize 2 * K / p ^ j = w at *
      omega
    · have : 2 * K / p ^ j = 0 := Nat.div_eq_of_lt (by omega)
      generalize K / p ^ j = u at *
      omega
  have hsum := sum_le_sum hcnt
  rw [sum_add_distrib, ← mul_sum, sum_ite, sum_const_zero, add_zero, sum_const,
    card_pow_le (by omega) hlog2K] at hsum
  simp only [nsmul_eq_mul, mul_one] at hsum
  push_cast at hsum ⊢
  linarith

/-! ### Lemma 3.3 -/

theorem card_RK (K : ℕ) : (RK K).card = 2 * K := by
  rw [RK, card_erase_of_mem (by simp), Int.card_Icc]; omega

theorem descPochhammer_comp_add (K : ℚ) (k : ℕ) :
    (descPochhammer ℚ k).comp (X + C K) = ∏ j ∈ range k, (X - C ((j : ℚ) - K)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_comp, ih, prod_range_succ, sub_comp, X_comp,
      ← C_eq_natCast, C_comp, C_sub]
    ring

/-- `(K!)² C(x + K, k) = ∏_{r ∈ R_K} (x - r) · (K!)²/k! · x ∏_{K < s ≤ K + m} (x - s)` for
`k = 2K + 1 + m`. -/
theorem binomP_comp_eq (K m : ℕ) :
    C ((K.factorial : ℚ) ^ 2) * (binomP (2 * K + 1 + m)).comp (X + C (K : ℚ)) =
      poleProd (RK K) * (C ((K.factorial : ℚ) ^ 2 / (2 * K + 1 + m).factorial) *
        poleProd (insert 0 (Ioc (K : ℤ) (K + m)))) := by
  set k := 2 * K + 1 + m
  have himg : (range k).image (fun j : ℕ => (j : ℤ) - K) =
      RK K ∪ insert 0 (Ioc (K : ℤ) (K + m)) := by
    ext r
    simp only [mem_image, mem_range, RK, mem_union, mem_erase, mem_Icc, mem_insert, mem_Ioc]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro h; exact ⟨(r + K).toNat, by omega, by omega⟩
  have hdisj : Disjoint (RK K) (insert 0 (Ioc (K : ℤ) (K + m))) := by
    rw [disjoint_left]
    intro r hr hr'
    simp only [RK, mem_erase, mem_Icc, mem_insert, mem_Ioc] at hr hr'
    omega
  have hprod : poleProd (RK K) * poleProd (insert 0 (Ioc (K : ℤ) (K + m))) =
      (descPochhammer ℚ k).comp (X + C (K : ℚ)) := by
    rw [descPochhammer_comp_add, poleProd, poleProd, ← prod_union hdisj, ← himg,
      prod_image fun a _ b _ h => by simpa using h]
    push_cast; rfl
  rw [binomP, mul_comp, C_comp, ← hprod, div_eq_mul_inv, C_mul]
  ring

theorem eval_Qk (K m : ℕ) (y : ℚ) :
    (C ((K.factorial : ℚ) ^ 2 / (2 * K + 1 + m).factorial) *
        poleProd (insert 0 (Ioc (K : ℤ) (K + m)))).eval y =
      (K.factorial : ℚ) ^ 2 / (2 * K + 1 + m).factorial *
        (y * ∏ s ∈ Ioc (K : ℤ) (K + m), (y - s)) := by
  rw [eval_mul, eval_C, poleProd, prod_insert (by simp), eval_mul, eval_prod]
  simp

theorem natDegree_Qk (K m : ℕ) :
    (C ((K.factorial : ℚ) ^ 2 / (2 * K + 1 + m).factorial) *
        poleProd (insert 0 (Ioc (K : ℤ) (K + m)))).natDegree ≤ m + 1 := by
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_poleProd, card_insert_of_notMem (by simp), Int.card_Ioc]
  omega

theorem dd_le_of_mem_RK {K : ℕ} {r : ℤ} (hr : r ∈ RK K) : dd r ≤ K := by
  simp only [RK, mem_erase, mem_Icc] at hr
  rcases le_or_gt 0 r with h | h
  · have := dd_of_nonneg h; omega
  · have := dd_of_neg h; omega

/-- Lemma 3.3 for one element `C(x + K, k)` of the binomial basis. -/
theorem lemma33_binom {K : ℕ} (hK : 1 ≤ K) {k : ℕ} (hk : k < 5 * K) :
    PolyVGe p (-6 * Nat.log p (5 * K))
      (tauR (RK K) (C ((K.factorial : ℚ) ^ 2) * (binomP k).comp (X + C (K : ℚ)))) := by
  set N := C ((K.factorial : ℚ) ^ 2) * (binomP k).comp (X + C (K : ℚ))
  have hlog1 : Nat.log p (2 * K) ≤ Nat.log p (5 * K) := Nat.log_mono_right (by omega)
  have hlog2 : Nat.log p K ≤ Nat.log p (5 * K) := Nat.log_mono_right (by omega)
  have hres : ∀ r ∈ RK K, VGe p (-Nat.log p (2 * K)) (resid (RK K) N r) := by
    intro r hr
    have heval : N.eval (r : ℚ) = (K.factorial : ℚ) ^ 2 * (Ring.choose (r + K) k : ℤ) := by
      rw [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C,
        show (r : ℚ) + K = ((r + K : ℤ) : ℚ) by push_cast; ring, binomP_eval_int]
    rw [resid, heval, eval_derivative_poleProd hr, poleProd, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    have h := (VGe_intCast (p := p) (Ring.choose (r + K) k)).mul (VGe_resid_factor (p := p) hr)
    rw [zero_add] at h
    convert h using 1
    ring
  refine PolyVGe_tauR ?_ ?_
  · refine VGe.add ?_ (VGe_sum _ fun r hr => ?_)
    · rcases Nat.lt_or_ge (2 * K) k with hk2 | hk2
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * K + 1 + m := ⟨k - (2 * K + 1), by omega⟩
        rw [show N = _ from binomP_comp_eq K m,
          mul_divByMonic_cancel_left _ (poleProd_monic _)]
        have h := taup_VGe_of_values (p := p) (D := 5 * K) _
          ((natDegree_Qk K m).trans_lt (by omega)) (A := 2 * Nat.log p (2 * K + 1 + m))
          fun n _ => by
            rw [eval_Qk]
            have := VGe_Qval (p := p) K m n
            simp only [Int.cast_natCast] at this
            refine this.mono (by omega)
        refine h.mono ?_
        have : Nat.log p (2 * K + 1 + m) ≤ Nat.log p (5 * K) := Nat.log_mono_right (by omega)
        omega
      · have hdeg : (N /ₘ poleProd (RK K)).natDegree = 0 := by
          rw [natDegree_divByMonic _ (poleProd_monic _), natDegree_poleProd, card_RK]
          have : N.natDegree ≤ k := by
            refine (natDegree_C_mul_le _ _).trans ((natDegree_comp_le).trans ?_)
            rw [natDegree_binomP]
            have : (X + C (K : ℚ)).natDegree ≤ 1 := by
              rw [natDegree_X_add_C]
            nlinarith
          omega
        rw [eq_C_of_natDegree_eq_zero hdeg, taup_C]
        exact VGe_zero _
    · refine ((hres r hr).mul (VGe_H5 (p := p) (dd_le_of_mem_RK hr))).mono ?_
      omega
  · exact VGe_sum _ fun r hr => (hres r hr).mono (by omega)

/-- **Lemma 3.3**: for `A` integer-valued with `deg A < 5K`,
`v_p^G(τ_X((K!)² A / ∏_{r ∈ R_K} (x - r))) ≥ -6 ⌊log_p(5K)⌋`. -/
theorem lemma33 {K : ℕ} (hK : 1 ≤ K) (A : ℚ[X]) (hA : A.natDegree < 5 * K)
    (hval : ∀ y : ℤ, VGe p 0 (A.eval (y : ℚ))) :
    PolyVGe p (-6 * Nat.log p (5 * K)) (tauR (RK K) (C ((K.factorial : ℚ) ^ 2) * A)) := by
  set A' := A.comp (X - C (K : ℚ))
  have hA' : A'.natDegree < 5 * K := by
    refine (natDegree_comp_le).trans_lt ?_
    rw [natDegree_X_sub_C, mul_one]; exact hA
  have hA'' : A = A'.comp (X + C (K : ℚ)) := by
    rw [comp_assoc]; simp
  have hnewton := newton A' hA'
  rw [hA'', hnewton, Polynomial.sum_comp, mul_sum, tauR_sum]
  refine PolyVGe_sum _ fun k hk => ?_
  rw [mul_comp, C_comp, mul_left_comm, tauR_C_mul]
  refine (PolyVGe.C_mul (w := 0) ?_ (lemma33_binom hK (mem_range.1 hk))).mono (by simp)
  rw [fdiff_eq_sum]
  refine VGe_sum _ fun i _ => ?_
  have := (VGe_intCast (p := p) ((-1 : ℤ) ^ (k - i) * k.choose i)).mul
    (hval ((i : ℤ) - K))
  simp only [A', eval_comp, eval_sub, eval_X, eval_C]
  push_cast at this ⊢
  simpa using this

end Zeta5
