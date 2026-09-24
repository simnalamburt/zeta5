/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Zeta5.GramBasis
import Zeta5.LocalTau

/-!
# Unimodular bases by the Chinese remainder theorem

The bases (4.5) and (4.11) reduce modulo `p` to the polynomials
`∏_{c ≠ a} (t - ρ_c)^{L_c} (t - ρ_a)^i` (`i < L_a`) with distinct `ρ_c ∈ 𝔽_p`. These are linearly
independent over `𝔽_p`: modulo `(t - ρ_a)^{L_a}` only the rows of the class `a` survive, and there
they are a unit times `(t - ρ_a)^i`. Hence an integral basis with this reduction has a coefficient
matrix whose determinant is prime to `p`.
-/

open Polynomial Finset

namespace Zeta5

section CRT

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∏_{c ≠ a} (X - ρ_c)^{L_c} (X - ρ_a)^i`. -/
noncomputable def crtRow (ρ : ι → F) (L : ι → ℕ) (a : ι) (i : ℕ) : F[X] :=
  (∏ c ∈ univ.erase a, (X - C (ρ c)) ^ L c) * (X - C (ρ a)) ^ i

theorem crtRow_linearIndependent (ρ : ι → F) (hρ : Function.Injective ρ) (L : ι → ℕ) :
    LinearIndependent F (fun x : Σ a, Fin (L a) => crtRow ρ L x.1 x.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg ⟨a, i⟩
  rw [Fintype.sum_sigma] at hg
  set U := ∏ c ∈ univ.erase a, (X - C (ρ c)) ^ L c
  set S := ∑ j : Fin (L a), g ⟨a, j⟩ • (X - C (ρ a)) ^ (j : ℕ)
  have hQ : ∀ b, b ≠ a → ∀ j : Fin (L b), (X - C (ρ a)) ^ L a ∣ crtRow ρ L b j := by
    intro b hb j
    exact Dvd.dvd.mul_right (dvd_prod_of_mem _ (mem_erase.2 ⟨Ne.symm hb, mem_univ a⟩)) _
  have hsplit := hg
  rw [← add_sum_erase _ _ (mem_univ a)] at hsplit
  have hdvd : (X - C (ρ a)) ^ L a ∣ U * S := by
    have e : U * S = ∑ j : Fin (L a), g ⟨a, j⟩ • crtRow ρ L a j := by
      simp only [S, crtRow, mul_sum, smul_eq_C_mul, U]; refine sum_congr rfl fun j _ => ?_; ring
    rw [e, eq_neg_of_add_eq_zero_left hsplit, dvd_neg]
    refine dvd_sum fun b hb => dvd_sum fun j _ => ?_
    rw [smul_eq_C_mul]
    exact Dvd.dvd.mul_left (hQ b (ne_of_mem_erase hb) j) _
  have hcop : IsCoprime ((X - C (ρ a)) ^ L a) U := by
    refine IsCoprime.prod_right fun c hc => IsCoprime.pow ?_
    exact isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.2 (hρ.ne (ne_of_mem_erase hc).symm)).isUnit
  have hS : S = 0 := by
    have h := hcop.dvd_of_dvd_mul_left hdvd
    by_contra hS0
    have hdeg : S.natDegree < L a := by
      refine (natDegree_sum_le_of_forall_le _ _ (n := L a - 1) fun j _ => ?_).trans_lt ?_
      · refine (natDegree_smul_le _ _).trans ?_
        rw [natDegree_pow, natDegree_X_sub_C, mul_one]
        have := j.2; omega
      · have : 0 < L a := Fin.pos i
        omega
    have := eq_zero_of_dvd_of_natDegree_lt h (by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact hdeg)
    exact hS0 this
  have hc : S.comp (X + C (ρ a)) = ∑ j : Fin (L a), g ⟨a, j⟩ • X ^ (j : ℕ) := by
    simp only [S, Polynomial.sum_comp, smul_comp, pow_comp, sub_comp, X_comp, C_comp,
      add_sub_cancel_right]
  have hcomp := congrArg (fun P => (P.comp (X + C (ρ a))).coeff i) hS
  simp only [hc, zero_comp, coeff_zero, finsetSum_coeff, coeff_smul, coeff_X_pow,
    smul_eq_mul] at hcomp
  rw [sum_eq_single i (fun j _ hj => by simp [Fin.val_ne_of_ne (Ne.symm hj)])
    (fun h => absurd (mem_univ i) h)] at hcomp
  simpa using hcomp

omit [Fintype ι] [DecidableEq ι] in
/-- Polynomials of degree `< H` that are linearly independent have an invertible coefficient
matrix. -/
theorem det_coeff_ne_zero {H : ℕ} (b : Fin H → F[X]) (hb : ∀ k, (b k).natDegree < H)
    (hind : LinearIndependent F b) :
    (Matrix.of fun k l : Fin H => (b k).coeff l).det ≠ 0 := by
  have hmem : ∀ k, b k ∈ degreeLT F H := fun k => by
    rw [mem_degreeLT]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast hb k)
  set b' : Fin H → degreeLT F H := fun k => ⟨b k, hmem k⟩
  have h1 : LinearIndependent F b' := by
    refine LinearIndependent.of_comp (degreeLT F H).subtype ?_
    have : (degreeLT F H).subtype ∘ b' = b := rfl
    rw [this]; exact hind
  have h2 := h1.map' (degreeLTEquiv F H).toLinearMap (degreeLTEquiv F H).ker
  have h3 : LinearIndependent F (Matrix.of fun k l : Fin H => (b k).coeff l).row := by
    convert h2 using 1
    all_goals try with_reducible_and_instances rfl
    ext k l
    rfl
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h3
  exact h3.ne_zero

end CRT

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integral family whose reduction modulo `p` is linearly independent has a coefficient
matrix with determinant prime to `p`. -/
theorem unimodular_of_independent {H : ℕ} (b : Fin H → ℤ[X]) (hb : ∀ k, (b k).natDegree < H)
    (hind : LinearIndependent (ZMod p) fun k => (b k).map (Int.castRingHom (ZMod p))) :
    (coeffMat fun k => (b k).map (Int.castRingHom ℚ)).det ≠ 0 ∧
      VGe p 0 ((coeffMat fun k => (b k).map (Int.castRingHom ℚ)).det⁻¹) := by
  set A : Matrix (Fin H) (Fin H) ℤ := Matrix.of fun k l => (b k).coeff l
  have hA : coeffMat (fun k => (b k).map (Int.castRingHom ℚ)) = A.map (Int.castRingHom ℚ) := by
    ext k l; simp [coeffMat, A]
  have hdet : (coeffMat fun k => (b k).map (Int.castRingHom ℚ)).det = (A.det : ℚ) := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; simp
  have hmod : ((A.det : ℤ) : ZMod p) ≠ 0 := by
    have e : ((A.det : ℤ) : ZMod p) =
        (Matrix.of fun k l : Fin H => ((b k).map (Int.castRingHom (ZMod p))).coeff l).det := by
      rw [show ((A.det : ℤ) : ZMod p) = Int.castRingHom (ZMod p) A.det from rfl, RingHom.map_det]
      congr 1; ext k l; simp [A]
    rw [e]
    exact det_coeff_ne_zero _ (fun k => (natDegree_map_le).trans_lt (hb k)) hind
  have hnd : ¬(p : ℤ) ∣ A.det := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
  rw [hdet]
  refine ⟨?_, VGe_inv_int hnd⟩
  intro h0
  apply hnd
  rw [show A.det = 0 by exact_mod_cast h0]
  exact dvd_zero _

end Zeta5
