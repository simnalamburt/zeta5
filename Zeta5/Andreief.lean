/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Andréief's identity

For functions `φ₀, …, φ_{n-1}` and a weight `ρ` on a measure space,
`n! · det [∫ φᵢ φⱼ ρ dμ]_{i,j} = ∫ det [φᵢ(y_k)]_{i,k}² ∏_k ρ(y_k) dμⁿ(y)`
(Andréief 1886; see Forrester, *Meet Andréief*, (1.7)). This is (6.10) of the paper.

The proof expands both determinants: the right-hand side is
`∑_{σ,τ} sgn σ sgn τ ∏ᵢ ∫ φ_{σ i} φ_{τ i} ρ`, and for each `τ` the sum over `σ` is `sgn τ` times
the determinant on the left.
-/

open MeasureTheory Matrix Equiv

namespace Zeta5

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

/-- `det [φᵢ(y_k)]_{i,k}`. -/
def vdet (φ : Fin n → α → ℝ) (y : Fin n → α) : ℝ := (Matrix.of fun i k => φ i (y k)).det

omit [MeasurableSpace α] in
theorem vdet_sq_mul_prod (φ : Fin n → α → ℝ) (ρ : α → ℝ) (y : Fin n → α) :
    vdet φ y ^ 2 * ∏ k, ρ (y k) =
      ∑ σ : Perm (Fin n), ∑ τ : Perm (Fin n), ((Perm.sign σ : ℤ) * (Perm.sign τ : ℤ) : ℝ) *
        ∏ i, (φ (σ i) (y i) * φ (τ i) (y i) * ρ (y i)) := by
  simp only [vdet, det_apply', of_apply]
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- **Andréief's identity**. -/
theorem andreief (φ : Fin n → α → ℝ) (ρ : α → ℝ)
    (hint : ∀ i j, Integrable (fun y => φ i y * φ j y * ρ y) μ) :
    (Matrix.of fun i j => ∫ y, φ i y * φ j y * ρ y ∂μ).det * n.factorial =
      ∫ y, vdet φ y ^ 2 * ∏ k, ρ (y k) ∂(Measure.pi fun _ => μ) := by
  set A := Matrix.of fun i j => ∫ y, φ i y * φ j y * ρ y ∂μ with hA
  simp_rw [vdet_sq_mul_prod]
  have hprod : ∀ σ τ : Perm (Fin n), Integrable
      (fun y : Fin n → α => ∏ i, (φ (σ i) (y i) * φ (τ i) (y i) * ρ (y i)))
      (Measure.pi fun _ => μ) := fun σ τ =>
    Integrable.fintype_prod (f := fun i y => φ (σ i) y * φ (τ i) y * ρ y) fun i => hint _ _
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ =>
    (hprod σ τ).const_mul _]
  have hterm : ∀ σ τ : Perm (Fin n), ∫ y, ((Perm.sign σ : ℤ) * (Perm.sign τ : ℤ) : ℝ) *
      ∏ i, (φ (σ i) (y i) * φ (τ i) (y i) * ρ (y i)) ∂(Measure.pi fun _ => μ) =
      ((Perm.sign σ : ℤ) * (Perm.sign τ : ℤ) : ℝ) *
        ∏ i, ∫ y, φ (σ i) y * φ (τ i) y * ρ y ∂μ := by
    intro σ τ
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (fun i z => φ (σ i) z * φ (τ i) z * ρ z)]
  simp_rw [integral_finsetSum _ fun τ _ => (hprod _ τ).const_mul _, hterm]
  -- for fixed `τ`, the sum over `σ` is `sgn τ • det A`
  have hτ : ∀ τ : Perm (Fin n), ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℝ) *
      ∏ i, ∫ y, φ (σ i) y * φ (τ i) y * ρ y ∂μ = (Perm.sign τ : ℤ) * A.det := by
    intro τ
    rw [← det_permute' τ A, det_apply']
    rfl
  rw [Finset.sum_comm]
  have hsq : ∀ τ : Perm (Fin n), ((Perm.sign τ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) = 1 := by
    intro τ
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsum : ∀ τ : Perm (Fin n), ∑ σ : Perm (Fin n),
      ((Perm.sign σ : ℤ) * (Perm.sign τ : ℤ) : ℝ) *
        ∏ i, ∫ y, φ (σ i) y * φ (τ i) y * ρ y ∂μ = A.det := by
    intro τ
    calc ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) * (Perm.sign τ : ℤ) : ℝ) *
          ∏ i, ∫ y, φ (σ i) y * φ (τ i) y * ρ y ∂μ
        = ((Perm.sign τ : ℤ) : ℝ) * ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℝ) *
            ∏ i, ∫ y, φ (σ i) y * φ (τ i) y * ρ y ∂μ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          ring
      _ = A.det := by rw [hτ, ← mul_assoc, hsq, one_mul]
  simp_rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    mul_comm]

end Zeta5
