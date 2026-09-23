/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.RingTheory.Polynomial.Content

/-!
# Lower bounds for `p`-adic valuations

`Zeta5.VGe p w q` says `v_p(q) ≥ w`, i.e. `‖q‖_p ≤ p^{-w}` (so `0` satisfies every bound), and
`Zeta5.PolyVGe p w P` says this for every coefficient of `P ∈ ℚ[X]`: the Gauss valuation
`v_p^G(P) ≥ w` of §3.

* `Zeta5.PolyVGe.det`: if `v_p^G(M_{ij}) ≥ (w_i + w_j)/2`, then `v_p^G(det M) ≥ ∑ w_i`.
* `Zeta5.exists_intPoly_of_forall_prime`: a polynomial with `v_p^G ≥ 0` at every prime has integer
  coefficients.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(q) ≥ w`. -/
def VGe (p : ℕ) (w : ℤ) (q : ℚ) : Prop := padicNorm p q ≤ (p : ℚ) ^ (-w)

theorem one_lt_p : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt

theorem p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos

theorem VGe_zero (w : ℤ) : VGe p w 0 := by
  simp only [VGe, padicNorm.zero]; exact (zpow_pos p_pos _).le

theorem VGe.mono {w w' : ℤ} {q : ℚ} (h : VGe p w q) (hw : w' ≤ w) : VGe p w' q :=
  h.trans (zpow_le_zpow_right₀ one_lt_p.le (by omega))

theorem VGe.add {w : ℤ} {a b : ℚ} (ha : VGe p w a) (hb : VGe p w b) : VGe p w (a + b) :=
  padicNorm.nonarchimedean.trans (max_le ha hb)

omit hp in
theorem VGe.neg {w : ℤ} {a : ℚ} (ha : VGe p w a) : VGe p w (-a) := by
  rwa [VGe, padicNorm.neg]

theorem VGe.sub {w : ℤ} {a b : ℚ} (ha : VGe p w a) (hb : VGe p w b) : VGe p w (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem VGe.mul {w w' : ℤ} {a b : ℚ} (ha : VGe p w a) (hb : VGe p w' b) :
    VGe p (w + w') (a * b) := by
  rw [VGe, padicNorm.mul, neg_add, zpow_add₀ p_pos.ne']
  exact mul_le_mul ha hb (padicNorm.nonneg _) (zpow_pos p_pos _).le

theorem VGe_sum {ι : Type*} (s : Finset ι) {w : ℤ} {f : ι → ℚ} (h : ∀ i ∈ s, VGe p w (f i)) :
    VGe p w (∑ i ∈ s, f i) :=
  padicNorm.sum_le' h (zpow_pos p_pos _).le

theorem VGe_prod {ι : Type*} (s : Finset ι) {w : ι → ℤ} {f : ι → ℚ}
    (h : ∀ i ∈ s, VGe p (w i) (f i)) : VGe p (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [VGe]
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    exact (h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

theorem VGe_intCast (z : ℤ) : VGe p 0 z := by
  rw [VGe, neg_zero, zpow_zero]; exact padicNorm.of_int z

theorem VGe_natCast (n : ℕ) : VGe p 0 n := by
  have := VGe_intCast (p := p) n; simpa using this

theorem VGe_one : VGe p 0 1 := by simpa using VGe_natCast (p := p) 1

theorem VGe.pow {w : ℤ} {a : ℚ} (ha : VGe p w a) (k : ℕ) : VGe p (k * w) (a ^ k) := by
  induction k with
  | zero => simpa using VGe_one (p := p)
  | succ k ih => rw [pow_succ]; exact (ih.mul ha).mono (by push_cast; ring_nf; rfl)

theorem VGe_iff {w : ℤ} {q : ℚ} (hq : q ≠ 0) : VGe p w q ↔ w ≤ padicValRat p q := by
  rw [VGe, padicNorm.eq_zpow_of_nonzero hq, zpow_le_zpow_iff_right₀ one_lt_p]
  omega

theorem VGe_p_pow (k : ℤ) : VGe p k ((p : ℚ) ^ k) := by
  rw [VGe_iff (zpow_ne_zero _ p_pos.ne'), padicValRat.zpow, padicValRat.self hp.out.one_lt]
  simp

theorem VGe.mul_p_pow {w : ℤ} {a : ℚ} (ha : VGe p w a) (k : ℤ) :
    VGe p (w + k) (a * (p : ℚ) ^ k) := ha.mul (VGe_p_pow k)

theorem VGe_of_padicValRat {w : ℤ} {q : ℚ} (h : q ≠ 0 → w ≤ padicValRat p q) : VGe p w q := by
  by_cases hq : q = 0
  · rw [hq]; exact VGe_zero w
  · exact (VGe_iff hq).2 (h hq)

/-! ### Polynomials -/

/-- `v_p^G(P) ≥ w`: every coefficient of `P` has `v_p ≥ w`. -/
def PolyVGe (p : ℕ) (w : ℤ) (P : ℚ[X]) : Prop := ∀ i, VGe p w (P.coeff i)

theorem PolyVGe.mono {w w' : ℤ} {P : ℚ[X]} (h : PolyVGe p w P) (hw : w' ≤ w) :
    PolyVGe p w' P := fun i => (h i).mono hw

theorem PolyVGe_zero (w : ℤ) : PolyVGe p w (0 : ℚ[X]) := fun i => by simpa using VGe_zero w

theorem PolyVGe_C {w : ℤ} {a : ℚ} (h : VGe p w a) : PolyVGe p w (C a) := by
  intro i
  rw [coeff_C]
  split_ifs
  · exact h
  · exact VGe_zero w

theorem PolyVGe_X : PolyVGe p 0 (X : ℚ[X]) := by
  intro i
  rw [coeff_X]
  split_ifs
  · exact VGe_one
  · exact VGe_zero 0

theorem PolyVGe.add {w : ℤ} {P Q : ℚ[X]} (hP : PolyVGe p w P) (hQ : PolyVGe p w Q) :
    PolyVGe p w (P + Q) := fun i => by rw [coeff_add]; exact (hP i).add (hQ i)

omit hp in
theorem PolyVGe.neg {w : ℤ} {P : ℚ[X]} (hP : PolyVGe p w P) : PolyVGe p w (-P) :=
  fun i => by rw [coeff_neg]; exact (hP i).neg

theorem PolyVGe.sub {w : ℤ} {P Q : ℚ[X]} (hP : PolyVGe p w P) (hQ : PolyVGe p w Q) :
    PolyVGe p w (P - Q) := fun i => by rw [coeff_sub]; exact (hP i).sub (hQ i)

theorem PolyVGe.mul {w w' : ℤ} {P Q : ℚ[X]} (hP : PolyVGe p w P) (hQ : PolyVGe p w' Q) :
    PolyVGe p (w + w') (P * Q) := fun i => by
  rw [coeff_mul]
  exact VGe_sum _ fun x _ => (hP x.1).mul (hQ x.2)

theorem PolyVGe.C_mul {w w' : ℤ} {a : ℚ} {P : ℚ[X]} (ha : VGe p w a) (hP : PolyVGe p w' P) :
    PolyVGe p (w + w') (C a * P) := (PolyVGe_C ha).mul hP

theorem PolyVGe_sum {ι : Type*} (s : Finset ι) {w : ℤ} {f : ι → ℚ[X]}
    (h : ∀ i ∈ s, PolyVGe p w (f i)) : PolyVGe p w (∑ i ∈ s, f i) := fun k => by
  rw [finsetSum_coeff]; exact VGe_sum s fun i hi => h i hi k

theorem PolyVGe_prod {ι : Type*} (s : Finset ι) {w : ι → ℤ} {f : ι → ℚ[X]}
    (h : ∀ i ∈ s, PolyVGe p (w i) (f i)) : PolyVGe p (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty]
    exact PolyVGe_C VGe_one
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    exact (h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

/-! ### Determinants -/

/-- If `v_p^G(M_{ij}) ≥ (w_i + w_j)/2` for all `i, j`, then `v_p^G(det M) ≥ ∑ w_i`. The weights `w`
are twice the half-integer weights of §4. -/
theorem PolyVGe_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ[X]) (w : Fin n → ℤ)
    (e : Fin n → Fin n → ℤ) (he : ∀ i j, w i + w j ≤ 2 * e i j)
    (hM : ∀ i j, PolyVGe p (e i j) (M i j)) : PolyVGe p (∑ i, w i) M.det := by
  rw [Matrix.det_apply]
  refine PolyVGe_sum _ fun σ _ => ?_
  have hprod := PolyVGe_prod (p := p) univ (w := fun i => e (σ i) i) (f := fun i => M (σ i) i)
    fun i _ => hM (σ i) i
  have hsum : ∑ i, w i ≤ ∑ i, e (σ i) i := by
    have h2 : ∑ i, (w (σ i) + w i) ≤ ∑ i, 2 * e (σ i) i := sum_le_sum fun i _ => he (σ i) i
    rw [sum_add_distrib, Equiv.sum_comp σ w, ← mul_sum] at h2
    omega
  intro k
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact (hprod k).mono hsum
  · rw [h, Units.neg_smul, one_smul, coeff_neg]; exact ((hprod k).mono hsum).neg

/-! ### Integrality -/

theorem den_eq_one_of_forall_prime {q : ℚ} (h : ∀ p : ℕ, p.Prime → VGe p 0 q) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp', hpd⟩ := Nat.exists_prime_and_dvd hden
  have : Fact p.Prime := ⟨hp'⟩
  have hq : q ≠ 0 := fun h0 => hden (by simp [h0])
  have h1 := (VGe_iff hq).1 (h p hp')
  have hnum : ¬(p : ℤ) ∣ q.num := by
    intro hdvd
    have h2 : p ∣ q.num.natAbs := Int.natCast_dvd.1 hdvd
    have := Nat.dvd_gcd h2 hpd
    rw [q.reduced] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  have h3 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have h4 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hpd
  rw [padicValRat_def, h3] at h1
  omega

/-- A polynomial with `v_p^G ≥ 0` at every prime has integer coefficients. -/
theorem exists_intPoly_of_forall_prime {P : ℚ[X]} (h : ∀ p : ℕ, p.Prime → PolyVGe p 0 P) :
    ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = P := by
  refine ⟨∑ i ∈ P.support, monomial i (P.coeff i).num, ?_⟩
  have hden : ∀ i, (P.coeff i).den = 1 := fun i => den_eq_one_of_forall_prime fun p hp' => by
    have : Fact p.Prime := ⟨hp'⟩
    exact h p hp' i
  ext i
  simp only [Polynomial.map_sum, map_monomial, eq_intCast, finsetSum_coeff, coeff_monomial]
  by_cases hi : i ∈ P.support
  · rw [sum_eq_single i (fun j _ hji => by simp [hji]) (fun h' => absurd hi h')]
    simp only [ite_true]
    exact_mod_cast Rat.coe_int_num_of_den_eq_one (hden i)
  · rw [sum_eq_zero fun j hj => by
      have : j ≠ i := fun e => hi (e ▸ hj)
      simp [this]]
    rw [notMem_support_iff.1 hi]

end Zeta5
