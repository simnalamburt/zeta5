/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Frullani's integral for the exponential

`∫₀^∞ s⁻¹ (e^{-as} - e^{-bs}) ds = log(b/a)` for `0 < a ≤ b`: the integrand is `∫_a^b e^{-ts} dt`,
and exchanging the integrals gives `∫_a^b t⁻¹ dt`. (The pinned Mathlib has no general Frullani
integral.)
-/

open Real MeasureTheory Set

namespace Zeta5

theorem integral_frullani_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in Ioi 0, s⁻¹ * (exp (-(a * s)) - exp (-(b * s))) = log (b / a) := by
  have hin : ∀ s ∈ Ioi (0 : ℝ),
      s⁻¹ * (exp (-(a * s)) - exp (-(b * s))) = ∫ t in Ioc a b, exp (-(t * s)) := by
    intro s hs
    have hs0 : (s : ℝ) ≠ 0 := (mem_Ioi.1 hs).ne'
    rw [← intervalIntegral.integral_of_le hab]
    have e : (∫ t in a..b, exp (-(t * s))) = ∫ t in a..b, exp (-s * t) := by
      congr 1; ext t; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_left (fun x => exp x) (neg_ne_zero.2 hs0),
      integral_exp]
    simp only [smul_eq_mul]
    field_simp
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hin]
  have hint : Integrable (Function.uncurry fun (s t : ℝ) => exp (-(t * s)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc a b))) := by
    refine ((exp_neg_integrableOn_Ioi 0 ha).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Ioc a b)))).mono' ?_ ?_
    · exact (by fun_prop : Continuous (Function.uncurry fun (s t : ℝ) => exp (-(t * s))))
        |>.aestronglyMeasurable
    · have h1 : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc a b))),
          z.1 ∈ Ioi (0 : ℝ) :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
      have h2 : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc a b))),
          z.2 ∈ Ioc a b :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [Function.uncurry, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_one]
      exact exp_le_exp.2 (by nlinarith [mem_Ioi.1 hz1, (mem_Ioc.1 hz2).1])
  rw [integral_integral_swap hint]
  have hout : ∀ t ∈ Ioc a b, ∫ s in Ioi 0, exp (-(t * s)) = t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ha.trans (mem_Ioc.1 ht).1
    have := integral_exp_mul_Ioi (a := -t) (by linarith) 0
    simp only [mul_zero, exp_zero] at this
    rw [show (fun s => exp (-(t * s))) = fun s => exp (-t * s) by ext s; ring_nf, this]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hout, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]

end Zeta5
