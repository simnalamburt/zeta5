/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Zeta5.PBound
import Zeta5.Tau

/-!
# Changing the basis of the Hankel matrix

`G_K = [μ_X(W t^{i+j} / D_K)]` is the Gram matrix of the bilinear form `(f, g) ↦ μ_X(W f g / D_K)`
in the monomial basis. For another family `b_i = ∑_k B_{ik} t^k` of polynomials of degree `< h`,
`det [μ_X(W b_i b_j / D_K)] = det(B)² det G_K`. All the local bounds of §3 and §4 use this.
-/

open Polynomial Finset

namespace Zeta5

/-- `[μ_X(W b_i b_j / ∏_{j ∈ S} (t + j²))]`. -/
noncomputable def gram (W : ℚ[X]) (S : Finset ℕ) {m : ℕ} (b : Fin m → ℚ[X]) :
    Matrix (Fin m) (Fin m) ℚ[X] :=
  Matrix.of fun i j => muX (W * b i * b j) S

theorem G_eq_gram (n : ℕ) : G n = gram (D (N n) ^ 6) (Icc 1 (K n)) fun i => X ^ (i : ℕ) := by
  ext i j : 1
  simp [G, gram, pow_add, mul_assoc]

theorem muX_C_mul (c : ℚ) (A : ℚ[X]) (S : Finset ℕ) : muX (C c * A) S = C c * muX A S := by
  rw [← smul_eq_C_mul, muX_smul]

theorem muX_zero (S : Finset ℕ) : muX 0 S = 0 := by
  simpa using muX_C_mul 0 0 S

theorem muX_sum {ι : Type*} (s : Finset ι) (A : ι → ℚ[X]) (S : Finset ℕ) :
    muX (∑ i ∈ s, A i) S = ∑ i ∈ s, muX (A i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [muX_zero]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, muX_add, ih]

/-- The coefficient matrix `B_{ik} = [t^k] b_i`. -/
noncomputable def coeffMat {m : ℕ} (b : Fin m → ℚ[X]) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun i k => (b i).coeff k

theorem eq_sum_coeff {m : ℕ} (b : Fin m → ℚ[X]) (hb : ∀ i, (b i).natDegree < m) (i : Fin m) :
    b i = ∑ k : Fin m, C ((b i).coeff k) * X ^ (k : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => C ((b i).coeff k) * X ^ k)]
  conv_lhs => rw [(b i).as_sum_range' m (hb i)]
  simp [C_mul_X_pow_eq_monomial]

theorem gram_change {m : ℕ} (W : ℚ[X]) (S : Finset ℕ) (b : Fin m → ℚ[X])
    (hb : ∀ i, (b i).natDegree < m) :
    gram W S b = (coeffMat b).map C * gram W S (fun k => X ^ (k : ℕ)) *
      ((coeffMat b).map C).transpose := by
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, gram, Matrix.of_apply,
    coeffMat]
  have e : W * b i * b j = ∑ l : Fin m, ∑ k : Fin m, C ((b i).coeff k) * (C ((b j).coeff l) *
      (W * X ^ (k : ℕ) * X ^ (l : ℕ))) := by
    conv_lhs => rw [eq_sum_coeff b hb i, eq_sum_coeff b hb j]
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [e, muX_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [muX_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [muX_C_mul, muX_C_mul]
  ring

/-- `det [μ_X(W b_i b_j / D_S)] = det(B)² det [μ_X(W t^{i+j} / D_S)]`. -/
theorem det_gram_change {m : ℕ} (W : ℚ[X]) (S : Finset ℕ) (b : Fin m → ℚ[X])
    (hb : ∀ i, (b i).natDegree < m) :
    (gram W S b).det = C ((coeffMat b).det ^ 2) * (gram W S fun k : Fin m => X ^ (k : ℕ)).det := by
  rw [gram_change W S b hb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp only [map_pow]
  ring

/-- The determinant of a triangular change of basis. -/
theorem det_coeffMat_of_triangular {m : ℕ} (b : Fin m → ℚ[X])
    (hb : ∀ i, (b i).natDegree ≤ i) : (coeffMat b).det = ∏ i : Fin m, (b i).coeff i := by
  rw [Matrix.det_of_lowerTriangular]
  · rfl
  · intro i j hij
    exact coeff_eq_zero_of_natDegree_lt ((hb i).trans_lt hij)

variable {p : ℕ} [Fact p.Prime]

/-- A local bound for the Gram determinant in a basis with `v_p(det B) ≤ 0` bounds `Δ_K`. -/
theorem PolyVGe_Δ_of_gram {n : ℕ} (b : Fin (dim n) → ℚ[X]) (hb : ∀ i, (b i).natDegree < dim n)
    (h0 : (coeffMat b).det ≠ 0) (hB : VGe p 0 ((coeffMat b).det⁻¹)) {γ : ℤ}
    (h : PolyVGe p γ (gram (D (N n) ^ 6) (Icc 1 (K n)) b).det) : PolyVGe p γ (Δ n) := by
  have hdet := det_gram_change (D (N n) ^ 6) (Icc 1 (K n)) b hb
  rw [← G_eq_gram, ← Δ] at hdet
  have : Δ n = C (((coeffMat b).det ^ 2)⁻¹) * (gram (D (N n) ^ 6) (Icc 1 (K n)) b).det := by
    rw [hdet, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 h0), C_1, one_mul]
  rw [this]
  have := (PolyVGe_C (p := p) (hB.mul hB)).mul h
  simpa [inv_pow, sq] using this

end Zeta5
