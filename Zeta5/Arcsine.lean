/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The arcsine measure and its logarithmic potential (A.1)

The arcsine probability measure on `[m - R, m + R]` has density `1/(π √((t-a)(b-t)))`. We define
it as the image of the uniform probability measure on `(0, 2π]` under `θ ↦ m + R cos θ`, so that
its integrals are circle averages: `∫ f dω = circleAverage (fun z => f (m + R Re z)) 0 1`.

On the unit circle, `c - Re z = -(z - w)(z - w')/(2z)` whenever `w + w' = 2c` and `w w' = 1`
(the Joukowski map). With `circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖` this gives the classical
formula (A.1) for the potential: `U(t) = log(R/2) + log max(1, |c| + √(c² - 1))` with
`c = (t - m)/R`.
-/

open Real MeasureTheory Set Filter

namespace Zeta5

/-! ### The Joukowski factorisation -/

theorem abs_sub_re_eq {z w w' : ℂ} (hz : ‖z‖ = 1) {c : ℝ} (hsum : w + w' = 2 * c)
    (hprod : w * w' = 1) : |c - z.re| = ‖z - w‖ * ‖z - w'‖ / 2 := by
  have hnormSq : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have key : (z - w) * (z - w') = z * ((2 * (z.re - c) : ℝ) : ℂ) := by
    have hre : ((z.re : ℝ) : ℂ) = (z + (starRingEnd ℂ) z) / 2 := by
      rw [Complex.add_conj]; push_cast; ring
    push_cast
    rw [hre]
    linear_combination (-z) * hsum + hprod - hnormSq
  have := congr_arg (‖·‖) key
  simp only [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
  rw [this, abs_two, abs_sub_comm]
  ring

/-- The two roots of `X² - 2cX + 1`. -/
noncomputable def jouk (c : ℝ) : ℂ × ℂ :=
  if |c| ≤ 1 then (c + √(1 - c ^ 2) * Complex.I, c - √(1 - c ^ 2) * Complex.I)
  else (c + √(c ^ 2 - 1), c - √(c ^ 2 - 1))

theorem jouk_sum (c : ℝ) : (jouk c).1 + (jouk c).2 = 2 * c := by
  unfold jouk; split_ifs <;> ring

theorem jouk_prod (c : ℝ) : (jouk c).1 * (jouk c).2 = 1 := by
  unfold jouk
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ 1 - c ^ 2 := by nlinarith [abs_le.1 h, sq_abs c]
    have hs : ((√(1 - c ^ 2) : ℝ) : ℂ) ^ 2 = 1 - c ^ 2 := by
      rw [← Complex.ofReal_pow, sq_sqrt h1]; push_cast; ring
    linear_combination hs - ((√(1 - c ^ 2) : ℝ) : ℂ) ^ 2 * Complex.I_sq
  · have h1 : (0 : ℝ) ≤ c ^ 2 - 1 := by
      simp only [not_le] at h; nlinarith [sq_abs c, abs_nonneg c]
    have hs : ((√(c ^ 2 - 1) : ℝ) : ℂ) ^ 2 = c ^ 2 - 1 := by
      rw [← Complex.ofReal_pow, sq_sqrt h1]; push_cast; ring
    linear_combination (-1 : ℂ) * hs

theorem posLog_jouk (c : ℝ) :
    log⁺ ‖(jouk c).1‖ + log⁺ ‖(jouk c).2‖ = log (max 1 (|c| + √(c ^ 2 - 1))) := by
  unfold jouk
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ 1 - c ^ 2 := by nlinarith [abs_le.1 h, sq_abs c]
    have hn : ∀ s : ℝ, s ^ 2 = 1 - c ^ 2 → ‖(c : ℂ) + s * Complex.I‖ = 1 := by
      intro s hs
      rw [Complex.norm_def, Complex.normSq_add_mul_I, show c ^ 2 + s ^ 2 = 1 by linarith, sqrt_one]
    have e1 := hn (√(1 - c ^ 2)) (sq_sqrt h1)
    have e2 : ‖(c : ℂ) - √(1 - c ^ 2) * Complex.I‖ = 1 := by
      have := hn (-√(1 - c ^ 2)) (by rw [neg_sq, sq_sqrt h1])
      rwa [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at this
    rw [e1, e2, posLog_one, add_zero, sqrt_eq_zero'.2 (by linarith), add_zero,
      max_eq_left (by linarith [abs_le.1 h] : |c| ≤ 1), Real.log_one]
  · simp only [not_le] at h
    have h1 : 0 ≤ c ^ 2 - 1 := by nlinarith [sq_abs c, abs_nonneg c]
    set s := √(c ^ 2 - 1) with hs
    have hs0 : 0 ≤ s := sqrt_nonneg _
    have hss : s ^ 2 = c ^ 2 - 1 := sq_sqrt h1
    have hs_lt : s < |c| := by
      by_contra hcon
      simp only [not_lt] at hcon
      nlinarith [sq_abs c, abs_nonneg c, mul_le_mul hcon hcon (abs_nonneg c) hs0]
    rw [show ((c : ℂ) + s) = ((c + s : ℝ) : ℂ) by push_cast; ring,
      show ((c : ℂ) - s) = ((c - s : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      max_eq_right (by linarith : 1 ≤ |c| + s)]
    rcases le_or_gt 0 c with hc | hc
    · rw [abs_of_nonneg hc] at h hs_lt ⊢
      have hprod : (c + s) * (c - s) = 1 := by nlinarith
      have h2 : |c - s| ≤ 1 := by
        rw [abs_of_pos (by linarith)]
        nlinarith
      rw [(posLog_eq_zero_iff |c - s|).2 (by rwa [abs_abs]), add_zero,
        posLog_eq_log (by rw [abs_abs, abs_of_pos (by linarith)]; linarith), log_abs]
    · rw [abs_of_neg hc] at h hs_lt ⊢
      have h2 : |c + s| ≤ 1 := by
        rw [abs_of_neg (by linarith)]
        nlinarith
      rw [(posLog_eq_zero_iff |c + s|).2 (by rwa [abs_abs]), zero_add,
        posLog_eq_log (by rw [abs_abs, abs_of_neg (by linarith)]; linarith),
        abs_of_neg (by linarith : c - s < 0)]
      congr 1
      ring

/-! ### The circle average -/

theorem log_abs_sub_mul_re_eventuallyEq (a : ℝ) {R : ℝ} (hR : 0 < R) :
    (fun z : ℂ => log |a - R * z.re|) =ᶠ[codiscreteWithin (Metric.sphere 0 |1|)]
      fun z => log R + log ‖z - (jouk (a / R)).1‖ + log ‖z - (jouk (a / R)).2‖ - log 2 := by
  filter_upwards [self_mem_codiscreteWithin _,
    compl_finite_mem_codiscreteWithin (s := Metric.sphere (0 : ℂ) |1|)
      (Set.toFinite {(jouk (a / R)).1, (jouk (a / R)).2})] with z hz hzw
  simp only [abs_one, mem_sphere_iff_norm, sub_zero] at hz
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hzw
  have h1 : ‖z - (jouk (a / R)).1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hzw.1)
  have h2 : ‖z - (jouk (a / R)).2‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hzw.2)
  have e : |a - R * z.re| = R * (‖z - (jouk (a / R)).1‖ * ‖z - (jouk (a / R)).2‖ / 2) := by
    rw [← abs_sub_re_eq hz (jouk_sum _) (jouk_prod _), ← abs_of_pos hR, ← abs_mul,
      abs_of_pos hR]
    congr 1
    field_simp
  rw [e, log_mul hR.ne' (by positivity), log_div (by positivity) two_ne_zero, log_mul h1 h2]
  ring

theorem circleIntegrable_log_abs_sub_mul_re (a : ℝ) {R : ℝ} (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => log |a - R * z.re|) 0 1 := by
  refine (circleIntegrable_congr_codiscreteWithin (log_abs_sub_mul_re_eventuallyEq a hR)).2 ?_
  exact (((circleIntegrable_const _ _ _).add (circleIntegrable_log_norm_sub_const 1)).add
    (circleIntegrable_log_norm_sub_const 1)).sub (circleIntegrable_const _ _ _)

/-- The potential of the arcsine measure, as a circle average. -/
theorem circleAverage_log_abs_sub_mul_re (a : ℝ) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => log |a - R * z.re|) 0 1 =
      log (R / 2) + log (max 1 (|a / R| + √((a / R) ^ 2 - 1))) := by
  set w := (jouk (a / R)).1 with hw
  set w' := (jouk (a / R)).2 with hw'
  have i0 : CircleIntegrable (fun _ : ℂ => log R) 0 1 := circleIntegrable_const _ _ _
  have i1 : CircleIntegrable (fun z : ℂ => log ‖z - w‖) 0 1 := circleIntegrable_log_norm_sub_const 1
  have i2 : CircleIntegrable (fun z : ℂ => log ‖z - w'‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have i01 : CircleIntegrable (fun z : ℂ => log R + log ‖z - w‖) 0 1 := i0.add i1
  have i012 : CircleIntegrable (fun z : ℂ => log R + log ‖z - w‖ + log ‖z - w'‖) 0 1 :=
    i01.add i2
  rw [circleAverage_congr_codiscreteWithin (log_abs_sub_mul_re_eventuallyEq a hR) one_ne_zero,
    circleAverage_fun_sub i012 (circleIntegrable_const _ _ _), circleAverage_fun_add i01 i2,
    circleAverage_fun_add i0 i1, circleAverage_const, circleAverage_const,
    circleAverage_log_norm_sub_const_eq_posLog, circleAverage_log_norm_sub_const_eq_posLog,
    add_assoc, hw, hw', posLog_jouk, log_div hR.ne' two_ne_zero]
  ring

/-! ### The arcsine measure -/

/-- The arcsine probability measure on `[m - R, m + R]`: the image of the uniform probability
measure on `(0, 2π]` under `θ ↦ m + R cos θ`. -/
noncomputable def arcsine (m R : ℝ) : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • (volume.restrict (Ioc 0 (2 * π))).map fun θ => m + R * Real.cos θ

theorem integral_arcsine (m R : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ u, f u ∂arcsine m R = circleAverage (fun z => f (m + R * z.re)) 0 1 := by
  rw [arcsine, integral_smul_measure, integral_map (by fun_prop) hf.aestronglyMeasurable,
    circleAverage_def, intervalIntegral.integral_of_le (by linarith [pi_pos]),
    ENNReal.toReal_ofReal (by have := pi_pos; positivity)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp [circleMap]

theorem integrable_arcsine_iff (m R : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (arcsine m R) ↔ CircleIntegrable (fun z => f (m + R * z.re)) 0 1 := by
  rw [arcsine, integrable_smul_measure (by simpa using pi_pos) ENNReal.ofReal_ne_top,
    integrable_map_measure hf.aestronglyMeasurable (by fun_prop), CircleIntegrable,
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  refine integrableOn_congr_fun (fun θ _ => ?_) measurableSet_Ioc
  simp [circleMap]

instance (m R : ℝ) : IsProbabilityMeasure (arcsine m R) := by
  constructor
  rw [arcsine, Measure.smul_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem ae_arcsine_mem (m R : ℝ) : ∀ᵐ u ∂arcsine m R, u ∈ Icc (m - |R|) (m + |R|) := by
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff (p := fun x => x ∈ Icc (m - |R|) (m + |R|)) (by fun_prop) measurableSet_Icc]
  refine ae_of_all _ fun θ => ?_
  have h1 := abs_le.1 (abs_cos_le_one θ)
  have h2 := neg_abs_le R
  have h3 := le_abs_self R
  constructor <;> nlinarith [abs_nonneg R]

theorem arcsine_singleton (m : ℝ) {R : ℝ} (hR : R ≠ 0) (t : ℝ) : arcsine m R {t} = 0 := by
  rw [arcsine, Measure.smul_apply, Measure.map_apply (by fun_prop) (measurableSet_singleton t),
    smul_eq_mul, mul_eq_zero]
  refine Or.inr (nonpos_iff_eq_zero.1 ((Measure.restrict_le_self _).trans (le_of_eq ?_)))
  set c := (t - m) / R with hcdef
  have hsub : (fun θ => m + R * Real.cos θ) ⁻¹' {t} ⊆
      (range fun k : ℤ => 2 * k * π + arccos c) ∪ range fun k : ℤ => 2 * k * π - arccos c := by
    intro θ hθ
    simp only [mem_preimage, mem_singleton_iff] at hθ
    have hc : Real.cos θ = c := by rw [hcdef, ← hθ]; field_simp; ring
    have := (Real.cos_eq_cos_iff).1 (show Real.cos (arccos c) = Real.cos θ by
      rw [cos_arccos (by rw [← hc]; exact neg_one_le_cos θ) (by rw [← hc]; exact cos_le_one θ),
        hc])
    obtain ⟨k, hk | hk⟩ := this
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr ⟨k, hk.symm⟩
  exact measure_mono_null hsub (((countable_range _).union (countable_range _)).measure_zero _)

/-- The logarithmic potential (A.1) of the arcsine measure `arcsine m R`. -/
noncomputable def arcsinePot (m R t : ℝ) : ℝ :=
  log (R / 2) + log (max 1 (|(t - m) / R| + √(((t - m) / R) ^ 2 - 1)))

theorem integral_log_arcsine (m : ℝ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    ∫ u, log |t - u| ∂arcsine m R = arcsinePot m R t := by
  rw [integral_arcsine m R (by fun_prop), arcsinePot,
    ← circleAverage_log_abs_sub_mul_re (t - m) hR]
  congr 1
  funext z
  congr 2
  ring

theorem integrable_log_arcsine (m : ℝ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Integrable (fun u => log |t - u|) (arcsine m R) := by
  rw [integrable_arcsine_iff m R (by fun_prop)]
  have : (fun z : ℂ => log |t - (m + R * z.re)|) = fun z => log |(t - m) - R * z.re| := by
    funext z; congr 2; ring
  rw [this]
  exact circleIntegrable_log_abs_sub_mul_re (t - m) hR

theorem arcsinePot_of_mem (m : ℝ) {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc (m - R) (m + R)) :
    arcsinePot m R t = log (R / 2) := by
  have h : |(t - m) / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR, div_le_one hR, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : ((t - m) / R) ^ 2 - 1 ≤ 0 := by
    nlinarith [sq_abs ((t - m) / R), abs_nonneg ((t - m) / R)]
  rw [arcsinePot, sqrt_eq_zero'.2 h2, add_zero, max_eq_left h, Real.log_one, add_zero]

theorem continuous_arcsinePot (m R : ℝ) : Continuous (arcsinePot m R) := by
  unfold arcsinePot
  refine continuous_const.add (Continuous.log (by fun_prop) fun t => ?_)
  exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

end Zeta5
