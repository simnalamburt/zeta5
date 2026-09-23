/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Binomial
import Zeta5.PBound
import Zeta5.Tau

/-!
# Binomial polynomials and the value bound (3.9)

`Zeta5.binomP k = x(x-1)⋯(x-k+1)/k!` is integer-valued, and every polynomial `F` of degree `< D`
is `∑_{j<D} (Δʲ F)(0) binomP j` (Newton's forward difference formula). The coefficient of `xʳ` in
`binomP j` has `v_p ≥ -r ⌊log_p j⌋`, since `binomP j = (x/j) ∏_{i<j} (x/i - 1)`.

Consequently, if `Q` has degree `< D` and `v_p(Q(n)) ≥ -A` for `n < D`, then
`v_p(τ(Q)) ≥ -A - 4 ⌊log_p D⌋` (`Zeta5.taup_VGe_of_values`): write `Q(x) = F(x + 1) - F(x)` with
`F(n) = ∑_{i<n} Q(i)`, so that `τ(Q)` is the coefficient of `x⁴` in `F`. This is the paper's (3.9),
without the factor `v_p(24)`.
-/

open Polynomial Finset

namespace Zeta5

/-- `binomP k = x(x-1)⋯(x-k+1)/k!`. -/
noncomputable def binomP (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

theorem binomP_eval_nat (k n : ℕ) : (binomP k).eval (n : ℚ) = n.choose k := by
  rw [binomP, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem binomP_eval_int (k : ℕ) (y : ℤ) : (binomP k).eval (y : ℚ) = Ring.choose y k := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) y k
  rw [← eval_eq_smeval, nsmul_eq_mul] at h1
  rw [binomP, eval_mul, eval_C, ← descPochhammer_eval_cast, h1]
  push_cast
  field_simp

theorem natDegree_binomP (k : ℕ) : (binomP k).natDegree = k := by
  rw [binomP, natDegree_C_mul (by positivity), descPochhammer_natDegree]

theorem binomP_succ (k : ℕ) :
    binomP (k + 1) = binomP k * (X - C (k : ℚ)) * C (((k : ℚ) + 1)⁻¹) := by
  rw [binomP, binomP, descPochhammer_succ_right, Nat.factorial_succ, ← C_eq_natCast]
  push_cast
  rw [mul_inv, C_mul]
  ring

/-! ### Newton's formula -/

/-- `Δʲ F (0)` for `F` restricted to `ℕ`. -/
noncomputable def fdiff (F : ℚ[X]) (j : ℕ) : ℚ := (fwdDiff 1)^[j] (fun n : ℕ => F.eval (n : ℚ)) 0

theorem fdiff_eq_sum (F : ℚ[X]) (j : ℕ) :
    fdiff F j = ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ (j - k) * j.choose k : ℤ) * F.eval (k : ℚ) := by
  rw [fdiff, fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul]

/-- Newton's forward difference formula for polynomials of degree `< D`. -/
theorem newton (F : ℚ[X]) {D : ℕ} (hD : F.natDegree < D) :
    F = ∑ j ∈ range D, C (fdiff F j) * binomP j := by
  have hinj : Function.Injective fun n : ℕ => (n : ℚ) := Nat.cast_injective
  have hcard : ((range D).image fun n : ℕ => (n : ℚ)).card = D := by
    rw [card_image_of_injective _ hinj, card_range]
  refine eq_of_degrees_lt_of_eval_finset_eq ((range D).image fun n : ℕ => (n : ℚ)) ?_ ?_ ?_
  · rw [hcard]; exact (degree_le_natDegree).trans_lt (by exact_mod_cast hD)
  · rw [hcard]
    refine (degree_sum_le _ _).trans_lt
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have := (natDegree_C_mul_le (fdiff F j) (binomP j)).trans_eq (natDegree_binomP j)
    exact_mod_cast this.trans_lt (mem_range.1 hj)
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hx
    rw [eval_finsetSum]
    have hn' := mem_range.1 hn
    have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) (fun m : ℕ => F.eval (m : ℚ)) n 0
    simp only [zero_add, smul_eq_mul, mul_one] at h
    rw [h, ← sum_range_add_sum_Ico _ (show n + 1 ≤ D by omega)]
    rw [sum_eq_zero (s := Ico (n + 1) D) fun j hj => by
      rw [eval_mul, eval_C, binomP_eval_nat, Nat.choose_eq_zero_of_lt (by
        simp only [mem_Ico] at hj; omega)]
      simp, add_zero]
    refine sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, binomP_eval_nat, fdiff, nsmul_eq_mul, mul_comm]

/-! ### Weighted coefficient bounds -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p([xʳ] P) ≥ -A - r ℓ` for every `r`. -/
def CoeffBnd (p : ℕ) (A : ℤ) (ℓ : ℕ) (P : ℚ[X]) : Prop := ∀ r : ℕ, VGe p (-A - r * ℓ) (P.coeff r)

theorem CoeffBnd.mul {A B : ℤ} {ℓ : ℕ} {P Q : ℚ[X]} (hP : CoeffBnd p A ℓ P)
    (hQ : CoeffBnd p B ℓ Q) :
    CoeffBnd p (A + B) ℓ (P * Q) := fun r => by
  rw [coeff_mul]
  refine VGe_sum _ fun x hx => ?_
  have := (hP x.1).mul (hQ x.2)
  have hr : x.1 + x.2 = r := mem_antidiagonal.1 hx
  refine this.mono (le_of_eq ?_)
  rw [← hr]; push_cast; ring

theorem CoeffBnd_prod {ι : Type*} (s : Finset ι) {ℓ : ℕ} {f : ι → ℚ[X]}
    (h : ∀ i ∈ s, CoeffBnd p 0 ℓ (f i)) : CoeffBnd p 0 ℓ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r
    rw [prod_empty, coeff_one]
    split_ifs with h
    · subst h; simpa using VGe_one (p := p)
    · exact VGe_zero _
  | insert i s hi ih =>
    rw [prod_insert hi]
    have := (h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))
    simpa using this

theorem VGe_inv_nat {i : ℕ} (hi : i ≠ 0) {ℓ : ℕ} (hℓ : i < p ^ (ℓ + 1)) :
    VGe p (-ℓ) ((i : ℚ)⁻¹) := by
  refine VGe_of_padicValRat fun _ => ?_
  rw [padicValRat.inv, padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le]
  have h1 := padicValNat_dvd_iff_le (p := p) hi (n := padicValNat p i) |>.2 le_rfl
  have h2 : p ^ padicValNat p i ≤ i := Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h1
  by_contra hcon
  have : p ^ (ℓ + 1) ≤ p ^ padicValNat p i := Nat.pow_le_pow_right hp.out.pos (by omega)
  omega

theorem CoeffBnd_linear {a b : ℚ} {ℓ : ℕ} (ha : VGe p (-ℓ) a) (hb : VGe p 0 b) :
    CoeffBnd p 0 ℓ (C a * X + C b) := by
  intro r
  rcases r with _ | _ | r
  · simpa using hb
  · simpa using ha
  · simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C]
    simpa using VGe_zero (p := p) _

/-- `binomP j = (x/j) ∏_{1 ≤ i < j} (x/i - 1)`. -/
theorem binomP_eq_prod {j : ℕ} (hj : 1 ≤ j) :
    binomP j = C ((j : ℚ)⁻¹) * X * ∏ i ∈ Finset.Icc 1 (j - 1), (C ((i : ℚ)⁻¹) * X - 1) := by
  induction j, hj using Nat.le_induction with
  | base => simp [binomP, descPochhammer_one]
  | succ j hj ih =>
    rw [binomP_succ, ih, show j + 1 - 1 = (j - 1) + 1 by omega,
      prod_Icc_succ_top (by omega), show j - 1 + 1 = j by omega]
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have key : C ((j : ℚ)⁻¹) * (X - C (j : ℚ)) = C ((j : ℚ)⁻¹) * X - 1 := by
      rw [mul_sub, ← C_mul, inv_mul_cancel₀ hj0, C_1]
    set P := ∏ i ∈ Finset.Icc 1 (j - 1), (C ((i : ℚ)⁻¹) * X - 1)
    have e2 : C ((((j + 1 : ℕ) : ℚ))⁻¹) = C (((j : ℚ) + 1)⁻¹) := by push_cast; rfl
    rw [e2]
    linear_combination (X * P * C (((j : ℚ) + 1)⁻¹)) * key

theorem CoeffBnd_binomP (j : ℕ) : CoeffBnd p 0 (Nat.log p j) (binomP j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · intro r
    simp only [binomP, Nat.factorial_zero, Nat.cast_one, inv_one, C_1, descPochhammer_zero,
      one_mul, coeff_one]
    split_ifs with h
    · subst h; simpa using VGe_one (p := p)
    · exact VGe_zero _
  have hlt : ∀ i ≤ j, i ≠ 0 → i < p ^ (Nat.log p j + 1) := fun i hi _ =>
    lt_of_le_of_lt hi (Nat.lt_pow_succ_log_self hp.out.one_lt j)
  rw [binomP_eq_prod hj]
  have h1 : CoeffBnd p 0 (Nat.log p j) (C ((j : ℚ)⁻¹) * X) := by
    have := CoeffBnd_linear (p := p) (a := (j : ℚ)⁻¹) (b := 0) (ℓ := Nat.log p j)
      (VGe_inv_nat (by omega) (hlt j le_rfl (by omega))) (VGe_zero 0)
    simpa using this
  have h2 : CoeffBnd p 0 (Nat.log p j)
      (∏ i ∈ Finset.Icc 1 (j - 1), (C ((i : ℚ)⁻¹) * X - 1)) := by
    refine CoeffBnd_prod _ fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have := CoeffBnd_linear (p := p) (a := (i : ℚ)⁻¹) (b := -1) (ℓ := Nat.log p j)
      (VGe_inv_nat (by omega) (hlt i (by omega) (by omega))) (by simpa using VGe_one.neg)
    simpa [sub_eq_add_neg] using this
  simpa using h1.mul h2

/-! ### The value bound (3.9) -/

/-- An antidifference with the degree bound: `F(x+1) - F(x) = Q`, `deg F ≤ deg Q + 1`. -/
noncomputable def antidiff (Q : ℚ[X]) : ℚ[X] :=
  ∑ n ∈ range (Q.natDegree + 1), C (Q.coeff n / (n + 1)) * Polynomial.bernoulli (n + 1)

theorem antidiff_spec (Q : ℚ[X]) : (antidiff Q).comp (X + 1) - antidiff Q = Q := by
  conv_rhs => rw [Q.as_sum_range_C_mul_X_pow]
  rw [antidiff, Polynomial.sum_comp, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_comp, C_comp, add_comm X 1, Polynomial.bernoulli_comp_one_add_X, ← mul_sub,
    add_sub_cancel_left, add_tsub_cancel_right, nsmul_eq_mul, ← mul_assoc, ← C_eq_natCast,
    ← C_mul]
  congr 1
  push_cast
  field_simp

theorem natDegree_antidiff_le (Q : ℚ[X]) : (antidiff Q).natDegree ≤ Q.natDegree + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  have : (Polynomial.bernoulli (n + 1)).natDegree ≤ n + 1 := by
    rw [Polynomial.bernoulli]
    exact natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_monomial_le _).trans (by omega)
  exact this.trans (by have := mem_range.1 hn; omega)

/-- (3.9): if `deg Q < D` and `v_p(Q(n)) ≥ -A` for `0 ≤ n < D`, then
`v_p(τ(Q)) ≥ -A - 4 ⌊log_p D⌋`. -/
theorem taup_VGe_of_values (Q : ℚ[X]) {D : ℕ} (hD : Q.natDegree < D) {A : ℤ}
    (hv : ∀ n : ℕ, n < D → VGe p (-A) (Q.eval (n : ℚ))) :
    VGe p (-A - 4 * Nat.log p D) (taup Q) := by
  set F := antidiff Q - C ((antidiff Q).eval 0) with hF
  have hΔ : F.comp (X + 1) - F = Q := by
    have := antidiff_spec Q
    rw [hF, sub_comp, C_comp]; linear_combination this
  have hdeg : F.natDegree < D + 1 := by
    have := natDegree_antidiff_le Q
    have h2 : F.natDegree ≤ (antidiff Q).natDegree := by
      rw [hF]; exact (natDegree_sub_le _ _).trans (by simp)
    omega
  have hval : ∀ n : ℕ, F.eval (n : ℚ) = ∑ i ∈ range n, Q.eval (i : ℚ) := by
    intro n
    induction n with
    | zero => simp [hF]
    | succ n ih =>
      rw [sum_range_succ, ← ih, ← hΔ]
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one]
      push_cast; ring
  have hFv : ∀ n : ℕ, n ≤ D → VGe p (-A) (F.eval (n : ℚ)) := fun n hn => by
    rw [hval]; exact VGe_sum _ fun i hi => hv i (by have := mem_range.1 hi; omega)
  have hc : F.coeff 4 = ∑ j ∈ range (D + 1), fdiff F j * (binomP j).coeff 4 := by
    conv_lhs => rw [newton F hdeg]
    rw [finsetSum_coeff]
    simp only [coeff_C_mul]
  rw [← hΔ, taup_delta, hc]
  refine VGe_sum _ fun j hj => ?_
  have hjD : j ≤ D := by have := mem_range.1 hj; omega
  have h1 : VGe p (-A) (fdiff F j) := by
    rw [fdiff_eq_sum]
    refine VGe_sum _ fun k hk => ?_
    have := (VGe_intCast (p := p) ((-1 : ℤ) ^ (j - k) * j.choose k)).mul
      (hFv k (by have := mem_range.1 hk; omega))
    simpa using this
  have h2 := CoeffBnd_binomP (p := p) j 4
  have hlog : Nat.log p j ≤ Nat.log p D := Nat.log_mono_right hjD
  refine (h1.mul h2).mono ?_
  push_cast
  omega

end Zeta5
