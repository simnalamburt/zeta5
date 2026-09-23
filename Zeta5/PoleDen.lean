/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Lagrange
import Zeta5.Defs

/-!
# Partial fractions over `∏_{j ∈ S} (t + j²)`

The partial fraction decomposition behind `Zeta5.muX`:
`A mod ∏_{j ∈ S} (t + j²) = ∑_{j ∈ S} Res_{t=-j²} (A / ∏ (t + j²)) · ∏_{k ∈ S, k ≠ j} (t + k²)`.
-/

open Polynomial

namespace Zeta5

/-! ### Partial fractions -/

theorem poleDen_eq_mul_erase {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) :
    poleDen S = (X + C ((j : ℚ) ^ 2)) * poleDen (S.erase j) := by
  simp only [poleDen]
  exact (Finset.mul_prod_erase S (fun j : ℕ => X + C ((j : ℚ) ^ 2)) hj).symm

theorem eval_poleDen_eq_zero {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) :
    (poleDen S).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [poleDen_eq_mul_erase hj]
  simp

theorem eval_poleDen_erase_of_ne {S : Finset ℕ} {i j : ℕ} (hj : j ∈ S) (hij : i ≠ j) :
    (poleDen (S.erase i)).eval (-(j : ℚ) ^ 2) = 0 :=
  eval_poleDen_eq_zero (Finset.mem_erase.2 ⟨hij.symm, hj⟩)

theorem sq_injective_nat : Function.Injective fun j : ℕ => -(j : ℚ) ^ 2 := by
  intro i j h
  have : (i : ℚ) ^ 2 = (j : ℚ) ^ 2 := neg_inj.1 h
  exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg i) (Nat.cast_nonneg j)).1 this

theorem eval_poleDen_erase_ne_zero (S : Finset ℕ) (j : ℕ) :
    (poleDen (S.erase j)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [poleDen, eval_prod, Finset.prod_ne_zero_iff]
  intro k hk h
  simp only [eval_add, eval_X, eval_C] at h
  exact (Finset.mem_erase.1 hk).1 (sq_injective_nat (by simp only; linarith))

theorem eval_derivative_poleDen {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) :
    (derivative (poleDen S)).eval (-(j : ℚ) ^ 2) = (poleDen (S.erase j)).eval (-(j : ℚ) ^ 2) := by
  rw [poleDen_eq_mul_erase hj, derivative_mul, derivative_add, derivative_X, derivative_C]
  simp

/-- The partial fraction decomposition behind `muX`:
`A mod ∏_{j ∈ S} (t + j²) = ∑_{j ∈ S} Res_{t=-j²} (A / ∏ (t + j²)) · ∏_{k ∈ S, k ≠ j} (t + k²)`. -/
theorem modByMonic_poleDen (A : ℚ[X]) (S : Finset ℕ) :
    A %ₘ poleDen S = ∑ j ∈ S, C (residue A S j) * poleDen (S.erase j) := by
  have hcard : (S.image fun j : ℕ => -(j : ℚ) ^ 2).card = S.card :=
    Finset.card_image_of_injective _ sq_injective_nat
  refine eq_of_degrees_lt_of_eval_finset_eq (s := S.image fun j : ℕ => -(j : ℚ) ^ 2)
    ?_ ?_ ?_
  · rw [hcard]
    refine (degree_modByMonic_lt A (poleDen_monic S)).trans_le ?_
    rw [degree_eq_natDegree (poleDen_monic S).ne_zero, natDegree_poleDen]
  · rw [hcard, ← mem_degreeLT]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [mem_degreeLT]
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    rw [degree_eq_natDegree (poleDen_monic _).ne_zero, natDegree_poleDen,
      Finset.card_erase_of_mem hj]
    have := Finset.card_pos.2 ⟨j, hj⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    have h := congr_arg (eval (-(j : ℚ) ^ 2)) (modByMonic_add_div A (poleDen S))
    rw [eval_add, eval_mul, eval_poleDen_eq_zero hj, zero_mul, add_zero] at h
    rw [h, eval_finsetSum, Finset.sum_eq_single j]
    · rw [eval_mul, eval_C, residue, eval_derivative_poleDen hj,
        div_mul_cancel₀ _ (eval_poleDen_erase_ne_zero S j)]
    · intro i _ hij
      rw [eval_mul, eval_poleDen_erase_of_ne hj hij, mul_zero]
    · intro h'; exact absurd hj h'

end Zeta5
