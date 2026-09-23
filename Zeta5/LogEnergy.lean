/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The logarithmic energy of a measure of mass zero (Lemma 6.2)

Lemma 6.2 of the paper states `I(ν) ≤ 0` for a signed measure `ν` of mass zero. We prove it for
the regularised kernel `log((x - y)² + δ²)` and `ν = μ₁ - μ₂`, where `μ₁` and `μ₂` are finite
measures on `ℝ` of the same mass with bounded support. This is all that §6.1 needs: the
regularisation replaces the circles of the paper, and the kernel is bounded on the supports, so no
limiting argument is needed.

The proof is the one of the paper.
* The Gaussian kernel is positive definite: completing the square gives
  `e^{-s(x-y)²} = √(4s/π) ∫ e^{-2s(x-w)²} e^{-2s(y-w)²} dw`, so the Gaussian energy of `ν` is
  `√(4s/π) ∫ (∫ e^{-2s(x-w)²} dν(x))² dw ≥ 0`.
* Frullani's integral gives `log((x-y)² + δ²) = log δ² + ∫₀^∞ s⁻¹ e^{-δ² s} (1 - e^{-s(x-y)²}) ds`,
  and the mass-zero condition removes the constant terms.
-/

open Real MeasureTheory Set Filter

namespace Zeta5

/-! ### The Gaussian kernel is positive definite -/

theorem gauss_mul_gauss (s x y w : ℝ) :
    exp (-(2 * s) * (x - w) ^ 2) * exp (-(2 * s) * (y - w) ^ 2) =
      exp (-s * (x - y) ^ 2) * exp (-(4 * s) * (w - (x + y) / 2) ^ 2) := by
  rw [← exp_add, ← exp_add]
  congr 1
  ring

theorem integrable_gauss {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable fun w => exp (-b * (c - w) ^ 2) :=
  (integrable_exp_neg_mul_sq hb).comp_sub_left c

theorem integral_gauss {b : ℝ} (c : ℝ) : ∫ w, exp (-b * (c - w) ^ 2) = √(π / b) := by
  have := integral_sub_left_eq_self (μ := volume) (fun w => exp (-b * w ^ 2)) c
  rw [this, integral_gaussian]

theorem integral_gauss_mul_gauss {s : ℝ} (x y : ℝ) :
    ∫ w, exp (-(2 * s) * (x - w) ^ 2) * exp (-(2 * s) * (y - w) ^ 2) =
      √(π / (4 * s)) * exp (-s * (x - y) ^ 2) := by
  simp_rw [gauss_mul_gauss]
  have := integral_sub_right_eq_self (μ := volume) (fun w => exp (-(4 * s) * w ^ 2)) ((x + y) / 2)
  rw [integral_const_mul, this, integral_gaussian, mul_comm]

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- `F_μ(w) = ∫ e^{-2s(x-w)²} dμ(x)`. -/
noncomputable def gaussConv (s : ℝ) (μ : Measure ℝ) (w : ℝ) : ℝ :=
  ∫ x, exp (-(2 * s) * (x - w) ^ 2) ∂μ

theorem integrable_gauss_prod {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => exp (-(2 * s) * (p.1 - p.2) ^ 2)) (μ.prod volume) := by
  rw [integrable_prod_iff (by fun_prop)]
  refine ⟨ae_of_all _ fun x => integrable_gauss (by positivity) x, ?_⟩
  simp_rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), integral_gauss]
  exact integrable_const _

theorem integrable_gaussConv {s : ℝ} (hs : 0 < s) : Integrable (gaussConv s μ) :=
  (integrable_gauss_prod hs).integral_prod_right

theorem gaussConv_nonneg (s : ℝ) (μ : Measure ℝ) (w : ℝ) : 0 ≤ gaussConv s μ w :=
  integral_nonneg fun _ => (exp_pos _).le

theorem gaussConv_le (s : ℝ) (hs : 0 ≤ s) (w : ℝ) : gaussConv s μ w ≤ μ.real univ := by
  have : gaussConv s μ w ≤ ∫ _, (1 : ℝ) ∂μ :=
    integral_mono (integrable_const _ |>.mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      nlinarith [sq_nonneg (x - w)])) (integrable_const _) fun x => by
        rw [exp_le_one_iff]; nlinarith [sq_nonneg (x - w)]
  simpa using this

theorem integrable_gaussConv_mul {s : ℝ} (hs : 0 < s) :
    Integrable fun w => gaussConv s μ w * gaussConv s ν w :=
  (integrable_gaussConv hs).mul_bdd (integrable_gaussConv hs).aestronglyMeasurable
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussConv_nonneg _ _ _)]
      exact gaussConv_le s hs.le w)

/-- The Gaussian energy `∫∫ e^{-s(x-y)²} dμ(x) dν(y)`. -/
noncomputable def gaussEnergy (s : ℝ) (μ ν : Measure ℝ) : ℝ :=
  ∫ p, exp (-s * (p.1 - p.2) ^ 2) ∂(μ.prod ν)

theorem gaussEnergy_eq {s : ℝ} (hs : 0 < s) :
    √(π / (4 * s)) * gaussEnergy s μ ν = ∫ w, gaussConv s μ w * gaussConv s ν w := by
  have hint : Integrable (Function.uncurry fun (p : ℝ × ℝ) (w : ℝ) =>
      exp (-(2 * s) * (p.1 - w) ^ 2) * exp (-(2 * s) * (p.2 - w) ^ 2))
      ((μ.prod ν).prod volume) := by
    rw [integrable_prod_iff (by fun_prop)]
    refine ⟨ae_of_all _ fun p => ?_, ?_⟩
    · exact (integrable_gauss (by positivity) p.1).mul_bdd (by fun_prop)
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
          nlinarith [sq_nonneg (p.2 - w)])
    · simp_rw [Function.uncurry_apply_pair, Real.norm_eq_abs,
        abs_of_pos (mul_pos (exp_pos _) (exp_pos _)), integral_gauss_mul_gauss]
      exact (integrable_const √(π / (4 * s))).mono' (by fun_prop) (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [exp_le_one_iff]; nlinarith [sq_nonneg (p.1 - p.2)])
  rw [gaussEnergy, ← integral_const_mul]
  simp_rw [← integral_gauss_mul_gauss (s := s)]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  exact integral_prod_mul (fun x => exp (-(2 * s) * (x - w) ^ 2))
    (fun y => exp (-(2 * s) * (y - w) ^ 2))

/-- The Gaussian kernel is positive definite: the Gaussian energy of `μ₁ - μ₂` is nonnegative. -/
theorem gaussEnergy_nonneg {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {s : ℝ}
    (hs : 0 < s) :
    0 ≤ gaussEnergy s μ₁ μ₁ - gaussEnergy s μ₁ μ₂ - gaussEnergy s μ₂ μ₁ +
      gaussEnergy s μ₂ μ₂ := by
  have hc : 0 < √(π / (4 * s)) := by positivity
  have e11 := gaussEnergy_eq (μ := μ₁) (ν := μ₁) hs
  have e12 := gaussEnergy_eq (μ := μ₁) (ν := μ₂) hs
  have e21 := gaussEnergy_eq (μ := μ₂) (ν := μ₁) hs
  have e22 := gaussEnergy_eq (μ := μ₂) (ν := μ₂) hs
  have hI : 0 ≤ ∫ w, (gaussConv s μ₁ w * gaussConv s μ₁ w - gaussConv s μ₁ w * gaussConv s μ₂ w -
      gaussConv s μ₂ w * gaussConv s μ₁ w + gaussConv s μ₂ w * gaussConv s μ₂ w) :=
    integral_nonneg fun w => by
      simp only [Pi.zero_apply]
      nlinarith [sq_nonneg (gaussConv s μ₁ w - gaussConv s μ₂ w)]
  rw [integral_add ?_ (integrable_gaussConv_mul hs), integral_sub ?_ (integrable_gaussConv_mul hs),
    integral_sub (integrable_gaussConv_mul hs) (integrable_gaussConv_mul hs)] at hI
  rotate_left
  · exact (integrable_gaussConv_mul hs).sub (integrable_gaussConv_mul hs)
  · exact ((integrable_gaussConv_mul hs).sub (integrable_gaussConv_mul hs)).sub
      (integrable_gaussConv_mul hs)
  refine nonneg_of_mul_nonneg_right ?_ hc
  linarith

/-! ### Frullani's integral for the logarithm -/

/-- The integrand `s⁻¹ (e^{-δ² s} - e^{-(r² + δ²) s})` of Frullani's integral for
`log (1 + r²/δ²)`. -/
noncomputable def frullani (δ r s : ℝ) : ℝ :=
  s⁻¹ * (exp (-(δ ^ 2 * s)) - exp (-((r ^ 2 + δ ^ 2) * s)))

theorem frullani_eq (δ r s : ℝ) :
    frullani δ r s = s⁻¹ * exp (-(δ ^ 2 * s)) * (1 - exp (-s * r ^ 2)) := by
  have : exp (-((r ^ 2 + δ ^ 2) * s)) = exp (-(δ ^ 2 * s)) * exp (-s * r ^ 2) := by
    rw [← exp_add]; congr 1; ring
  rw [frullani, this]
  ring

theorem frullani_nonneg (δ r : ℝ) {s : ℝ} (hs : 0 < s) : 0 ≤ frullani δ r s := by
  rw [frullani_eq]
  refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
  rw [exp_le_one_iff]
  nlinarith [sq_nonneg r]

theorem frullani_le (δ r : ℝ) {s : ℝ} (hs : 0 < s) :
    frullani δ r s ≤ r ^ 2 * exp (-(δ ^ 2 * s)) := by
  rw [frullani_eq]
  have h1 : 1 - exp (-s * r ^ 2) ≤ s * r ^ 2 := by linarith [add_one_le_exp (-s * r ^ 2)]
  calc s⁻¹ * exp (-(δ ^ 2 * s)) * (1 - exp (-s * r ^ 2))
      ≤ s⁻¹ * exp (-(δ ^ 2 * s)) * (s * r ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = r ^ 2 * exp (-(δ ^ 2 * s)) := by field_simp

theorem integrableOn_frullani {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    IntegrableOn (frullani δ r) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (pow_pos hδ 2)).const_mul (r ^ 2)).mono' ?_ ?_
  · exact (by unfold frullani; fun_prop : Measurable (frullani δ r)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (frullani_nonneg δ r hs), neg_mul]
    exact frullani_le δ r hs

/-- `log(r² + δ²) = log δ² + ∫₀^∞ s⁻¹ (e^{-δ² s} - e^{-(r² + δ²) s}) ds`. -/
theorem log_eq_frullani {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    log (r ^ 2 + δ ^ 2) = log (δ ^ 2) + ∫ s in Ioi 0, frullani δ r s := by
  have hf : LocallyIntegrableOn (fun x : ℝ => exp (-x)) (Ioi 0) :=
    (continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun x : ℝ => exp (-x)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have := (continuous_neg.rexp.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [neg_zero, exp_zero] at this
  have h := Frullani.integral_Ioi_eq hf (pow_pos hδ 2) (by positivity : 0 < r ^ 2 + δ ^ 2) hL
    tendsto_exp_neg_atTop_nhds_zero (integrableOn_frullani hδ r)
  simp only [smul_eq_mul, sub_zero, mul_one] at h
  rw [show (∫ s in Ioi 0, frullani δ r s) = log ((r ^ 2 + δ ^ 2) / δ ^ 2) by rw [← h]; rfl,
    log_div (by positivity) (by positivity)]
  ring

/-! ### The regularised logarithmic energy -/

/-- The regularised logarithmic energy `∫∫ log((x-y)² + δ²) dμ(x) dν(y)`. -/
noncomputable def logEnergy (δ : ℝ) (μ ν : Measure ℝ) : ℝ :=
  ∫ p, log ((p.1 - p.2) ^ 2 + δ ^ 2) ∂(μ.prod ν)

omit [IsFiniteMeasure μ] in
theorem ae_sq_sub_le {T : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ T) (hν : ∀ᵐ y ∂ν, |y| ≤ T) :
    ∀ᵐ p ∂(μ.prod ν), (p.1 - p.2) ^ 2 ≤ 4 * T ^ 2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ,
    Measure.quasiMeasurePreserving_snd.ae hν] with p h1 h2
  have := abs_sub p.1 p.2
  have h0 : 0 ≤ |p.1 - p.2| := abs_nonneg _
  nlinarith [sq_abs (p.1 - p.2)]

theorem integrable_frullani_prod {δ T : ℝ} (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ T)
    (hν : ∀ᵐ y ∂ν, |y| ≤ T) :
    Integrable (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) => frullani δ (p.1 - p.2) s)
      ((μ.prod ν).prod (volume.restrict (Ioi 0))) := by
  refine ((integrable_const (4 * T ^ 2)).mul_prod
    (exp_neg_integrableOn_Ioi 0 (pow_pos hδ 2))).mono' ?_ ?_
  · exact (by unfold frullani; fun_prop : Measurable (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) =>
      frullani δ (p.1 - p.2) s)).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_sq_sub_le hμ hν),
      Measure.quasiMeasurePreserving_snd.ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => hs))] with q h1 h2
    simp only [Function.uncurry, Real.norm_eq_abs] at h1 h2 ⊢
    rw [abs_of_nonneg (frullani_nonneg δ _ h2)]
    calc frullani δ (q.1.1 - q.1.2) q.2 ≤ (q.1.1 - q.1.2) ^ 2 * exp (-(δ ^ 2 * q.2)) :=
          frullani_le δ _ h2
      _ ≤ 4 * T ^ 2 * exp (-δ ^ 2 * q.2) := by
          rw [neg_mul]; exact mul_le_mul_of_nonneg_right h1 (exp_pos _).le

theorem integral_frullani_prod {δ s : ℝ} (hs : 0 ≤ s) :
    ∫ p, frullani δ (p.1 - p.2) s ∂(μ.prod ν) =
      s⁻¹ * exp (-(δ ^ 2 * s)) * (μ.real univ * ν.real univ - gaussEnergy s μ ν) := by
  have hg : Integrable (fun p : ℝ × ℝ => exp (-s * (p.1 - p.2) ^ 2)) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      nlinarith [sq_nonneg (p.1 - p.2)])
  simp_rw [frullani_eq]
  rw [integral_const_mul, integral_sub (integrable_const _) hg, integral_const, gaussEnergy,
    smul_eq_mul, mul_one, ← univ_prod_univ, measureReal_prod_prod]

theorem logEnergy_eq {δ T : ℝ} (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ T) (hν : ∀ᵐ y ∂ν, |y| ≤ T) :
    logEnergy δ μ ν = log (δ ^ 2) * (μ.real univ * ν.real univ) +
      ∫ s in Ioi 0, ∫ p, frullani δ (p.1 - p.2) s ∂(μ.prod ν) := by
  have hint := integrable_frullani_prod hδ hμ hν
  have hint' : Integrable (fun p : ℝ × ℝ => ∫ s in Ioi 0, frullani δ (p.1 - p.2) s) (μ.prod ν) :=
    hint.integral_prod_left
  rw [← integral_integral_swap hint, logEnergy]
  simp_rw [log_eq_frullani hδ]
  rw [integral_add (integrable_const _) hint', integral_const, smul_eq_mul, ← univ_prod_univ,
    measureReal_prod_prod, mul_comm]

/-- **Lemma 6.2** for the regularised kernel: the logarithmic energy of `μ₁ - μ₂` is at most `0`
when `μ₁` and `μ₂` have the same mass. -/
theorem logEnergy_nonpos {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {δ T : ℝ}
    (hδ : 0 < δ) (h₁ : ∀ᵐ x ∂μ₁, |x| ≤ T) (h₂ : ∀ᵐ x ∂μ₂, |x| ≤ T)
    (hmass : μ₁.real univ = μ₂.real univ) :
    logEnergy δ μ₁ μ₁ - logEnergy δ μ₁ μ₂ - logEnergy δ μ₂ μ₁ + logEnergy δ μ₂ μ₂ ≤ 0 := by
  rw [logEnergy_eq hδ h₁ h₁, logEnergy_eq hδ h₁ h₂, logEnergy_eq hδ h₂ h₁, logEnergy_eq hδ h₂ h₂]
  have i11 := (integrable_frullani_prod hδ h₁ h₁).integral_prod_right
  have i12 := (integrable_frullani_prod hδ h₁ h₂).integral_prod_right
  have i21 := (integrable_frullani_prod hδ h₂ h₁).integral_prod_right
  have i22 := (integrable_frullani_prod hδ h₂ h₂).integral_prod_right
  simp only [Function.uncurry_apply_pair] at i11 i12 i21 i22
  have key : ∫ s in Ioi 0, ((∫ p, frullani δ (p.1 - p.2) s ∂(μ₁.prod μ₁)) -
      (∫ p, frullani δ (p.1 - p.2) s ∂(μ₁.prod μ₂)) -
      (∫ p, frullani δ (p.1 - p.2) s ∂(μ₂.prod μ₁)) +
      ∫ p, frullani δ (p.1 - p.2) s ∂(μ₂.prod μ₂)) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun s hs => ?_
    rw [integral_frullani_prod hs.le, integral_frullani_prod hs.le, integral_frullani_prod hs.le,
      integral_frullani_prod hs.le, hmass]
    have hc : 0 ≤ s⁻¹ * exp (-(δ ^ 2 * s)) := by have : (0 : ℝ) < s := hs; positivity
    nlinarith [mul_nonneg hc (gaussEnergy_nonneg (μ₁ := μ₁) (μ₂ := μ₂) hs)]
  rw [integral_add ?_ i22, integral_sub ?_ i21, integral_sub i11 i12] at key
  · rw [hmass]; linarith
  · exact i11.sub i12
  · exact (i11.sub i12).sub i21

/-! ### Iterated integrals and symmetry -/

theorem integrable_logKernel {δ T : ℝ} (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ T)
    (hν : ∀ᵐ y ∂ν, |y| ≤ T) :
    Integrable (fun p : ℝ × ℝ => log ((p.1 - p.2) ^ 2 + δ ^ 2)) (μ.prod ν) := by
  refine (integrable_const (|log (δ ^ 2)| + |log (4 * T ^ 2 + δ ^ 2)|)).mono'
    (Continuous.log (by fun_prop) fun p => by positivity).aestronglyMeasurable ?_
  filter_upwards [ae_sq_sub_le hμ hν] with p hp
  have h1 : log (δ ^ 2) ≤ log ((p.1 - p.2) ^ 2 + δ ^ 2) :=
    log_le_log (by positivity) (by nlinarith [sq_nonneg (p.1 - p.2)])
  have h2 : log ((p.1 - p.2) ^ 2 + δ ^ 2) ≤ log (4 * T ^ 2 + δ ^ 2) :=
    log_le_log (by positivity) (by linarith)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (log (δ ^ 2)), le_abs_self (log (4 * T ^ 2 + δ ^ 2)),
    abs_nonneg (log (δ ^ 2)), abs_nonneg (log (4 * T ^ 2 + δ ^ 2))]

theorem logEnergy_eq_iter {δ T : ℝ} (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ T)
    (hν : ∀ᵐ y ∂ν, |y| ≤ T) :
    logEnergy δ μ ν = ∫ x, ∫ y, log ((x - y) ^ 2 + δ ^ 2) ∂ν ∂μ :=
  integral_prod _ (integrable_logKernel hδ hμ hν)

theorem integrable_logKernel_iter {δ T : ℝ} (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ T)
    (hν : ∀ᵐ y ∂ν, |y| ≤ T) : Integrable (fun x => ∫ y, log ((x - y) ^ 2 + δ ^ 2) ∂ν) μ :=
  (integrable_logKernel hδ hμ hν).integral_prod_left

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem logEnergy_comm [SFinite μ] [SFinite ν] (δ : ℝ) : logEnergy δ μ ν = logEnergy δ ν μ := by
  unfold logEnergy
  rw [← integral_prod_swap]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring_nf

end Zeta5
