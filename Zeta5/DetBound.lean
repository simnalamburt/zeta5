/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Zeta5.PBound

/-!
# Lemma 4.2

Let `v(A_{ij}) ≥ w_i + w_j` with nonpositive half-integer weights, `z` of them zero, and let `L` be
integral of rank at most `r`, written `L = U L' Uᵀ` with `U` of size `h × r`. Then
`v det(A + p⁻¹ L) ≥ 2 ∑ w_i - min(r, z)`.

We prove the two halves of the minimum separately (weights are doubled throughout):

* `-z`: lowering every zero weight to `-1/2` makes all entries of `p⁻¹ L`, which have valuation
  `≥ -1`, satisfy the weight bound, so the plain determinant bound applies;
* `-r`: `det(A + p⁻¹ U L' Uᵀ)` is the determinant of the block matrix `[[A, -U], [p⁻¹ L' Uᵀ, 1]]`,
  and a determinant bound with separate row and column weights applies to it, with row weight
  `-1` and column weight `0` on the `r` extra indices.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- The determinant bound with separate row weights `ρ` and column weights `κ` (doubled):
if `v(M_{ij}) ≥ (ρ_i + κ_j)/2`, then `v(det M) ≥ (∑ ρ + ∑ κ)/2`. -/
theorem PolyVGe_det_rc {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X])
    (ρ κ : ι → ℤ) (e : ι → ι → ℤ) (he : ∀ i j, ρ i + κ j ≤ 2 * e i j)
    (hM : ∀ i j, PolyVGe p (e i j) (M i j)) {W : ℤ} (hW : 2 * W ≤ ∑ i, ρ i + ∑ i, κ i + 1) :
    PolyVGe p W M.det := by
  rw [Matrix.det_apply]
  refine PolyVGe_sum _ fun σ _ => ?_
  have hprod := PolyVGe_prod (p := p) univ (w := fun i => e (σ i) i) (f := fun i => M (σ i) i)
    fun i _ => hM (σ i) i
  have hsum : W ≤ ∑ i, e (σ i) i := by
    have h2 : ∑ i, (ρ (σ i) + κ i) ≤ ∑ i, 2 * e (σ i) i := sum_le_sum fun i _ => he (σ i) i
    rw [sum_add_distrib, Equiv.sum_comp σ ρ, ← mul_sum] at h2
    omega
  intro k
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact (hprod k).mono hsum
  · rw [h, Units.neg_smul, one_smul, coeff_neg]; exact ((hprod k).mono hsum).neg

theorem PolyVGe_C_inv_p : PolyVGe p (-1) (C ((p : ℚ)⁻¹)) :=
  PolyVGe_C (by simpa using VGe_p_pow (p := p) (-1))

/-- The product `U L Uᵀ` of integral matrices is integral. -/
theorem PolyVGe_ULU {h r : ℕ} (U : Matrix (Fin h) (Fin r) ℚ) (L : Matrix (Fin r) (Fin r) ℚ[X])
    (hU : ∀ i s, VGe p 0 (U i s)) (hL : ∀ s s', PolyVGe p 0 (L s s')) (i j : Fin h) :
    PolyVGe p 0 ((U.map C * L * (U.map C).transpose) i j) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  refine PolyVGe_sum _ fun s' _ => ?_
  have h1 : PolyVGe p 0 (∑ s, C (U i s) * L s s') :=
    PolyVGe_sum _ fun s _ => ((PolyVGe_C (hU i s)).mul (hL s s')).mono (by simp)
  exact (h1.mul (PolyVGe_C (hU j s'))).mono (by simp)

/-- **Lemma 4.2** (with doubled weights `ω`). -/
theorem lemma42 {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X]) (U : Matrix (Fin h) (Fin r) ℚ)
    (L : Matrix (Fin r) (Fin r) ℚ[X]) (ω : Fin h → ℤ) (hω : ∀ i, ω i ≤ 0)
    (hA : ∀ i j, PolyVGe p ((ω i + ω j + 1) / 2) (A i j))
    (hU : ∀ i s, VGe p 0 (U i s)) (hL : ∀ s s', PolyVGe p 0 (L s s')) :
    PolyVGe p (∑ i, ω i - min (r : ℤ) (#{i | ω i = 0} : ℕ))
      (A + C ((p : ℚ)⁻¹) • (U.map C * L * (U.map C).transpose)).det := by
  set z := #{i | ω i = 0}
  rcases le_or_gt (z : ℤ) r with hzr | hzr
  · -- lower the zero weights to `-1/2`
    rw [min_eq_right hzr]
    set ω' : Fin h → ℤ := fun i => if ω i = 0 then -1 else ω i
    have hω' : ∀ i, ω' i ≤ -1 := fun i => by
      simp only [ω']; split_ifs with h0
      · exact le_refl _
      · have := hω i; omega
    have hsum : ∑ i, ω' i = ∑ i, ω i - z := by
      have : ∀ i, ω' i = ω i - if ω i = 0 then 1 else 0 := fun i => by
        simp only [ω']; split_ifs with h0 <;> simp [h0]
      simp only [this, sum_sub_distrib, sum_boole, z]
    rw [← hsum]
    refine PolyVGe_det _ ω' (fun i j => (ω' i + ω' j + 1) / 2) (fun i j => by omega) fun i j => ?_
    have h1 := (hA i j).mono (show (ω' i + ω' j + 1) / 2 ≤ (ω i + ω j + 1) / 2 by
      have : ω' i ≤ ω i := by simp only [ω']; split_ifs <;> omega
      have : ω' j ≤ ω j := by simp only [ω']; split_ifs <;> omega
      omega)
    have h2 := (PolyVGe_C_inv_p (p := p)).mul (PolyVGe_ULU U L hU hL i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine h1.add (h2.mono ?_)
    have := hω' i; have := hω' j; omega
  · -- the block matrix `[[A, -U], [p⁻¹ L Uᵀ, 1]]`
    rw [min_eq_left hzr.le]
    have hblock : (A + C ((p : ℚ)⁻¹) • (U.map C * L * (U.map C).transpose)).det =
        (Matrix.fromBlocks A (-U.map C) (C ((p : ℚ)⁻¹) • (L * (U.map C).transpose)) 1).det := by
      rw [Matrix.det_fromBlocks_one₂₂]
      congr 1
      rw [Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_smul, Matrix.mul_assoc]
    rw [hblock]
    refine PolyVGe_det_rc _ (Sum.elim ω fun _ => -2) (Sum.elim ω fun _ => 0)
      (fun a b => match a, b with
        | .inl i, .inl j => (ω i + ω j + 1) / 2
        | .inl _, .inr _ => 0
        | .inr _, .inl _ => -1
        | .inr _, .inr _ => 0) ?_ ?_ ?_
    · rintro (i | s) (j | s')
      · simp only [Sum.elim_inl]; omega
      · simp only [Sum.elim_inl, Sum.elim_inr]; have := hω i; omega
      · simp only [Sum.elim_inl, Sum.elim_inr]; have := hω j; omega
      · simp only [Sum.elim_inr]; omega
    · rintro (i | s) (j | s')
      · exact hA i j
      · simp only [Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.map_apply]
        exact (PolyVGe_C (hU i s')).neg
      · simp only [Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
        have : PolyVGe p 0 ((L * (U.map C).transpose) s j) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
          exact PolyVGe_sum _ fun s'' _ => ((hL s s'').mul (PolyVGe_C (hU j s''))).mono (by simp)
        exact ((PolyVGe_C_inv_p (p := p)).mul this).mono (by simp)
      · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
        split_ifs
        · exact PolyVGe_C VGe_one |>.mono le_rfl |> fun h => by simpa using h
        · exact PolyVGe_zero _
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      omega

end Zeta5
