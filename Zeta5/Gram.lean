/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Zeta5.Hermite

/-!
# Positivity at `ζ(5)` (Proposition 2.2)

At `X = ζ(5)` the functional becomes integration against the positive weight `w` of (2.10):
`μ_{ζ(5)}(A / ∏_{j ∈ S} (t + j²)) = ∫_0^∞ A(y²) / ∏_{j ∈ S} (y² + j²) · w(y) dy`.
This follows from the partial fraction decomposition used to define `muX`, the moment formula
`Zeta5.integral_pow_mul_wt`, and the pole formula `Zeta5.integral_wt_div_sq_add_sq`. Hence
`G_K(ζ(5))` is the Gram matrix of `1, y², …, y^{2(h-1)}` for the positive weight
`D_N(y²)⁶ / D_K(y²) · w(y)`, so it is positive definite and `Δ_K(ζ(5)) > 0`.

## Main results

* `Zeta5.modByMonic_poleDen`: the partial fraction decomposition.
* `Zeta5.aeval_muX_eq_integral`: `μ_{ζ(5)} = ∫ · w`.
* `Zeta5.posDef_G`: `G_K(ζ(5))` is positive definite.
* `Zeta5.aeval_Q_pos`: `Q_{K,M}(ζ(5)) > 0`.
-/

open Real MeasureTheory Set Polynomial Matrix

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

theorem aeval_poleDen_pos (S : Finset ℕ) {t : ℝ} (ht : 0 < t) : 0 < aeval t (poleDen S) := by
  rw [poleDen, map_prod]
  exact Finset.prod_pos fun j _ => by simp only [map_add, aeval_X, aeval_C]; positivity

/-- The partial fraction decomposition, evaluated at a real point `t > 0`. -/
theorem aeval_div_poleDen (A : ℚ[X]) (S : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    aeval t A / aeval t (poleDen S) =
      aeval t (A /ₘ poleDen S) + ∑ j ∈ S, (residue A S j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hden := (aeval_poleDen_pos S ht).ne'
  have hA := congr_arg (aeval t) (modByMonic_add_div A (poleDen S))
  rw [modByMonic_poleDen, map_add, map_mul, map_sum] at hA
  rw [← hA, add_div, add_comm, mul_div_cancel_left₀ _ hden, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hprod : aeval t (poleDen S) = (t + (j : ℝ) ^ 2) * aeval t (poleDen (S.erase j)) := by
    rw [poleDen_eq_mul_erase hj, map_mul]
    simp
  have hne : aeval t (poleDen (S.erase j)) ≠ 0 := (aeval_poleDen_pos _ ht).ne'
  have hne' : t + (j : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hprod, map_mul, aeval_C]
  field_simp
  simp

/-! ### The functional at `ζ(5)` as an integral -/

theorem aestronglyMeasurable_wt : AEStronglyMeasurable wt (volume.restrict (Ioi 0)) :=
  integrableOn_wt.aestronglyMeasurable

theorem integrableOn_wt_div {j : ℕ} (hj : 1 ≤ j) :
    IntegrableOn (fun y => wt y / (y ^ 2 + (j : ℝ) ^ 2)) (Ioi 0) := by
  have hj' : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ hj
  refine IntegrableOn.congr_fun (integrableOn_wt.bdd_mul (c := 1)
    (f := fun y : ℝ => 1 / (y ^ 2 + (j : ℝ) ^ 2))
    (Continuous.aestronglyMeasurable (by fun_prop (disch := intro y; positivity))) ?_)
    (fun y _ => by ring) measurableSet_Ioi
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
  nlinarith [sq_nonneg y]

theorem integrableOn_pow_mul_wt' (e : ℕ) : IntegrableOn (fun y => (y ^ 2) ^ e * wt y) (Ioi 0) := by
  simpa [← pow_mul] using integrableOn_pow_mul_wt e

theorem integrableOn_aeval_sq_mul_wt (q : ℚ[X]) :
    IntegrableOn (fun y => aeval (y ^ 2) q * wt y) (Ioi 0) := by
  simp_rw [aeval_eq_sum_range, Finset.sum_mul]
  refine integrable_finsetSum _ fun e _ => ?_
  simp_rw [Algebra.smul_def, mul_assoc]
  exact (integrableOn_pow_mul_wt' e).const_mul _

/-- `∫_0^∞ q(y²) w(y) dy = μ(q)` for every polynomial `q`, by linearity from (2.2). -/
theorem integral_aeval_sq_mul_wt (q : ℚ[X]) : ∫ y in Ioi 0, aeval (y ^ 2) q * wt y = mu q := by
  simp_rw [aeval_eq_sum_range, Finset.sum_mul]
  rw [integral_finsetSum _ fun e _ => ?_]
  · rw [mu_apply, sum_over_range _ (fun e => by simp)]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    simp_rw [Algebra.smul_def, mul_assoc, ← pow_mul]
    rw [integral_const_mul, integral_pow_mul_wt, eq_ratCast, mul_comm]
  · simp_rw [Algebra.smul_def, mul_assoc]
    exact (integrableOn_pow_mul_wt' e).const_mul _

theorem integrableOn_aeval_div_poleDen_mul_wt (A : ℚ[X]) {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j) :
    IntegrableOn (fun y => aeval (y ^ 2) A / aeval (y ^ 2) (poleDen S) * wt y) (Ioi 0) := by
  have hint : IntegrableOn (fun y : ℝ => aeval (y ^ 2) (A /ₘ poleDen S) * wt y +
      ∑ j ∈ S, (residue A S j : ℝ) * (wt y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) :=
    (integrableOn_aeval_sq_mul_wt _).add
      (integrable_finsetSum _ fun j hj => (integrableOn_wt_div (hS j hj)).const_mul _)
  refine hint.congr_fun (fun y hy => ?_) measurableSet_Ioi
  dsimp only
  rw [aeval_div_poleDen A S (pow_pos hy 2), add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Proposition 2.2 for the rational functions of `muX`:
`μ_{ζ(5)}(A / ∏_{j ∈ S} (t + j²)) = ∫_0^∞ A(y²) / ∏_{j ∈ S} (y² + j²) · w(y) dy`. -/
theorem aeval_muX_eq_integral (A : ℚ[X]) {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j) :
    aeval (riemannZeta 5).re (muX A S) =
      ∫ y in Ioi 0, aeval (y ^ 2) A / aeval (y ^ 2) (poleDen S) * wt y := by
  have hcongr : ∫ y in Ioi 0, aeval (y ^ 2) A / aeval (y ^ 2) (poleDen S) * wt y =
      ∫ y in Ioi 0, (aeval (y ^ 2) (A /ₘ poleDen S) * wt y +
        ∑ j ∈ S, (residue A S j : ℝ) * (wt y / (y ^ 2 + (j : ℝ) ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [aeval_div_poleDen A S (pow_pos hy 2), add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hcongr, integral_add (integrableOn_aeval_sq_mul_wt _)
    (integrable_finsetSum _ fun j hj => (integrableOn_wt_div (hS j hj)).const_mul _),
    integral_finsetSum _ fun j hj => (integrableOn_wt_div (hS j hj)).const_mul _,
    integral_aeval_sq_mul_wt, muX, map_add, map_sum, aeval_C]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_wt_div_sq_add_sq (hS j hj), map_mul, aeval_C, eq_ratCast]

/-! ### The Gram matrix -/

/-- The weight `D_N(y²)⁶ / D_K(y²) · w(y)` for which `G_K(ζ(5))` is a Gram matrix. -/
noncomputable def gramWeight (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (D (N n)) ^ 6 / aeval (y ^ 2) (D (K n)) * wt y

theorem gramWeight_pos (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 < gramWeight n y := by
  have h1 := aeval_poleDen_pos (Finset.Icc 1 (N n)) (pow_pos hy 2)
  have h2 := aeval_poleDen_pos (Finset.Icc 1 (K n)) (pow_pos hy 2)
  have h3 := wt_pos hy
  simp only [gramWeight, D]
  positivity

theorem mem_Icc_one_le {m j : ℕ} (hj : j ∈ Finset.Icc 1 m) : 1 ≤ j := (Finset.mem_Icc.1 hj).1

theorem gram_integrand_eq (n i j : ℕ) (y : ℝ) :
    aeval (y ^ 2) (D (N n) ^ 6 * X ^ (i + j)) / aeval (y ^ 2) (poleDen (Finset.Icc 1 (K n))) *
      wt y = y ^ (2 * i) * y ^ (2 * j) * gramWeight n y := by
  simp only [gramWeight, D, map_mul, map_pow, aeval_X]
  rw [← pow_mul, mul_add, pow_add]
  ring

theorem integrableOn_gram (n i j : ℕ) :
    IntegrableOn (fun y => y ^ (2 * i) * y ^ (2 * j) * gramWeight n y) (Ioi 0) :=
  (integrableOn_aeval_div_poleDen_mul_wt (D (N n) ^ 6 * X ^ (i + j))
    (S := Finset.Icc 1 (K n)) fun _ => mem_Icc_one_le).congr_fun
    (fun y _ => gram_integrand_eq n i j y) measurableSet_Ioi

/-- Proposition 2.2: the entries of `G_K(ζ(5))` are the moments of `gramWeight`. -/
theorem aeval_G (n : ℕ) (i j : Fin (dim n)) :
    aeval (riemannZeta 5).re (G n i j) =
      ∫ y in Ioi 0, y ^ (2 * (i : ℕ)) * y ^ (2 * (j : ℕ)) * gramWeight n y := by
  rw [G, of_apply, aeval_muX_eq_integral _ fun _ => mem_Icc_one_le]
  exact setIntegral_congr_fun measurableSet_Ioi fun y _ => gram_integrand_eq n i j y

/-- A nonzero vector gives a nonzero even polynomial `∑ vᵢ y^{2i}`. -/
theorem sum_mul_pow_ne_zero {m : ℕ} {v : Fin m → ℝ} (hv : v ≠ 0) :
    (∑ i, C (v i) * X ^ (2 * (i : ℕ)) : ℝ[X]) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  intro h0
  have := congr_arg (fun p : ℝ[X] => p.coeff (2 * (i : ℕ))) h0
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [Fin.val_inj, hji.symm]) (by simp)] at this
  exact hi (by simpa using this)

/-- `G_K(ζ(5))` is positive definite. -/
theorem posDef_G (n : ℕ) : ((G n).map (aeval (riemannZeta 5).re)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, map_apply, star_trivial, G, of_apply, add_comm (i : ℕ)]
  set P : ℝ → ℝ := fun y => ∑ i, v i * y ^ (2 * (i : ℕ)) with hP
  have hint : ∀ i j : Fin (dim n), IntegrableOn
      (fun y => v i * (y ^ (2 * (i : ℕ)) * y ^ (2 * (j : ℕ)) * gramWeight n y * v j)) (Ioi 0) :=
    fun i j => ((integrableOn_gram n i j).mul_const _).const_mul _
  have hpt : ∀ y, ∑ i : Fin (dim n), ∑ j : Fin (dim n),
      v i * (y ^ (2 * (i : ℕ)) * y ^ (2 * (j : ℕ)) * gramWeight n y * v j) =
      P y ^ 2 * gramWeight n y := by
    intro y
    rw [hP, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hPint : IntegrableOn (fun y => P y ^ 2 * gramWeight n y) (Ioi 0) :=
    IntegrableOn.congr_fun
      (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
        hint i j) (fun y _ => hpt y) measurableSet_Ioi
  have hform : star v ⬝ᵥ ((G n).map (aeval (riemannZeta 5).re) *ᵥ v) =
      ∫ y in Ioi 0, P y ^ 2 * gramWeight n y := by
    calc star v ⬝ᵥ ((G n).map (aeval (riemannZeta 5).re) *ᵥ v)
        = ∑ i : Fin (dim n), ∑ j : Fin (dim n), ∫ y in Ioi 0,
            v i * (y ^ (2 * (i : ℕ)) * y ^ (2 * (j : ℕ)) * gramWeight n y * v j) := by
          simp only [dotProduct, mulVec, map_apply, aeval_G, Pi.star_apply, star_trivial,
            Finset.mul_sum, integral_const_mul, integral_mul_const]
      _ = ∫ y in Ioi 0, ∑ i : Fin (dim n), ∑ j : Fin (dim n),
            v i * (y ^ (2 * (i : ℕ)) * y ^ (2 * (j : ℕ)) * gramWeight n y * v j) := by
          rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => hint i j]
      _ = ∫ y in Ioi 0, P y ^ 2 * gramWeight n y :=
          setIntegral_congr_fun measurableSet_Ioi fun y _ => hpt y
  rw [hform]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hPint).2 ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      mul_nonneg (sq_nonneg _) (gramWeight_pos n hy).le
  have hZ := finite_setOfPred_isRoot (sum_mul_pow_ne_zero hv)
  have hsub : Ioi 0 \ {x | IsRoot (∑ i, C (v i) * X ^ (2 * (i : ℕ)) : ℝ[X]) x} ⊆
      Function.support (fun y => P y ^ 2 * gramWeight n y) ∩ Ioi 0 := by
    intro y ⟨hy, hroot⟩
    refine ⟨?_, hy⟩
    have hPy : P y ≠ 0 := by
      intro h
      apply hroot
      simp only [Set.mem_ofPred_eq, IsRoot, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact h
    exact mul_ne_zero (pow_ne_zero _ hPy) (gramWeight_pos n hy).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_sdiff_null (hZ.measure_zero _), volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `Δ_K(ζ(5)) > 0`. -/
theorem aeval_Δ_pos (n : ℕ) : 0 < aeval (riemannZeta 5).re (Δ n) := by
  rw [Δ, AlgHom.map_det]
  exact (posDef_G n).det_pos

/-- Theorem 2.1: `Q_{K,M}(ζ(5)) > 0`, for every `n` and `M`. -/
theorem aeval_Q_pos (n M : ℕ) : 0 < aeval (riemannZeta 5).re (Q n M) := by
  rw [Q, F, map_mul, map_mul, aeval_C, aeval_C, eq_ratCast, eq_ratCast]
  have h1 : (0 : ℝ) < normFactor n M := by exact_mod_cast normFactor_pos n M
  have h2 : (0 : ℝ) < S n := by exact_mod_cast S_pos n
  exact mul_pos h1 (mul_pos h2 (aeval_Δ_pos n))

end Zeta5
