/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Zeta5.PoleIntegrals
import Zeta5.Weight

/-!
# The pole values (2.3) as integrals

Proposition 2.2 needs, for every integer `j ≥ 1`,
`∫_0^∞ w(y) / (y² + j²) dy = j⁴ (ζ(5) - H_j^{(5)}) - 1/4 + 1/(2j)`,
which is `a⁴ ζ(5, a) - 1/(2a) - 1/4` at `a = j`. The paper derives it from four integrations by
parts and Hermite's integral formula for the Hurwitz zeta function. We follow the same route but
avoid Hermite's formula:

1. With `g(y) = y⁵ / (y² + a²)` and `c > 0`, four integrations by parts give
   `∫_0^∞ c⁴ e^{-cy} g(y) dy = ∫_0^∞ e^{-cy} g⁗(y) dy = 24 a⁴ ∫_0^∞ e^{-cy} r₅(a, y) dy`,
   where `r₅(a, y) = Re((y - ia)⁻⁵)`; the boundary terms vanish because `g, …, g‴` vanish at `0`.
   Summing over `c = 2πℓ` gives `∫_0^∞ w(y) / (y² + a²) dy = 2a⁴ ∫_0^∞ f(y) r₅(a, y) dy` with
   `f(y) = 1 / (e^{2πy} - 1)`.
2. The partial fraction expansion of the cotangent (Mathlib's `cot_series_rep'`) at `iy` gives
   `f(y) = -1/2 + 1/(2πy) + (1/π) ∑_{k ≥ 1} y / (y² + k²)`.
3. The resulting rational integrals are computed in `Zeta5.PoleIntegrals`.

## Main results

* `Zeta5.aeval_muPole`: the value of (2.3) at a real point.
* `Zeta5.integral_wt_div_sq_add_sq`: the integral formula.
-/

open Real MeasureTheory Set Filter Topology Polynomial

namespace Zeta5

theorem aeval_muPole (x : ℝ) (j : ℕ) :
    aeval x (muPole j) = (j : ℝ) ^ 4 * (x - H5 j) - 1 / 4 + 1 / (2 * j) := by
  simp [muPole]

/-! ### The derivatives of `g(y) = y⁵ / (y² + a²)` -/

/-- `g⁽ᵐ⁾(y)` for `g(y) = y⁵ / (y² + a²)` and `m ≤ 4`. -/
noncomputable def gD (a : ℝ) : ℕ → ℝ → ℝ
  | 0, y => y ^ 5 / (y ^ 2 + a ^ 2)
  | 1, y => y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2) / (y ^ 2 + a ^ 2) ^ 2
  | 2, y => 2 * y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) / (y ^ 2 + a ^ 2) ^ 3
  | 3, y => 6 * y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) /
      (y ^ 2 + a ^ 2) ^ 4
  | _, y => 24 * a ^ 4 * r5 a y

theorem hasDerivAt_gD {a : ℝ} (ha : a ≠ 0) {m : ℕ} (hm : m < 4) (y : ℝ) :
    HasDerivAt (gD a m) (gD a (m + 1) y) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hq := (hasDerivAt_pow 2 y).add_const (a ^ 2)
  interval_cases m
  · convert (hasDerivAt_pow 5 y).div hq hd using 1
    · ext x; simp [gD]
    · simp only [gD]; norm_num; field_simp; ring
  · convert ((hasDerivAt_pow 4 y).mul (((hasDerivAt_pow 2 y).const_mul 3).const_add
      (5 * a ^ 2))).div (hq.pow 2) (pow_ne_zero _ hd) using 1
    · ext x; simp [gD]
    · simp only [gD]; norm_num; field_simp; ring
  · convert (((hasDerivAt_pow 3 y).const_mul 2).mul (((((hasDerivAt_pow 2 y).const_mul
      (9 * a ^ 2)).const_add (10 * a ^ 4)).add ((hasDerivAt_pow 4 y).const_mul 3)))).div
      (hq.pow 3) (pow_ne_zero _ hd) using 1
    · ext x; simp [gD]
    · simp only [gD]; norm_num; field_simp; ring
  · convert (((hasDerivAt_pow 2 y).const_mul 6).mul (((((hasDerivAt_pow 2 y).const_mul
      (5 * a ^ 4)).const_add (10 * a ^ 6)).add ((hasDerivAt_pow 4 y).const_mul (4 * a ^ 2))).add
      (hasDerivAt_pow 6 y))).div (hq.pow 4) (pow_ne_zero _ hd) using 1
    · ext x; simp [gD]
    · simp only [gD, r5]; norm_num; field_simp; ring

theorem gD_zero {a : ℝ} {m : ℕ} (hm : m < 4) : gD a m 0 = 0 := by
  interval_cases m <;> simp [gD]

theorem continuous_gD {a : ℝ} (ha : a ≠ 0) (m : ℕ) : Continuous (gD a m) := by
  have hd : ∀ y : ℝ, y ^ 2 + a ^ 2 ≠ 0 := fun y => by positivity
  match m with
  | 0 => exact Continuous.div (by fun_prop) (by fun_prop) hd
  | 1 => exact Continuous.div (by fun_prop) (by fun_prop) fun y => pow_ne_zero _ (hd y)
  | 2 => exact Continuous.div (by fun_prop) (by fun_prop) fun y => pow_ne_zero _ (hd y)
  | 3 => exact Continuous.div (by fun_prop) (by fun_prop) fun y => pow_ne_zero _ (hd y)
  | _ + 4 => exact (continuousOn_r5 ha).const_mul _

/-- A uniform polynomial bound for `g, g', …, g⁗` on `[0, ∞)`. -/
theorem abs_gD_le {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : m ≤ 4) {y : ℝ} (hy : 0 ≤ y) :
    |gD a m y| ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 := by
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  have hB : (60 : ℝ) ≤ 60 + 120 / a ^ 2 := le_add_of_nonneg_right (by positivity)
  have h1 : (1 : ℝ) ≤ (1 + y) ^ 3 := one_le_pow₀ (by linarith)
  have hy3 : y ^ 3 ≤ (1 + y) ^ 3 := pow_le_pow_left₀ hy (by linarith) 3
  have hy2 : y ^ 2 ≤ (1 + y) ^ 3 := by nlinarith [sq_nonneg y]
  have hy1 : y ≤ (1 + y) ^ 3 := by nlinarith [sq_nonneg y]
  interval_cases m
  · rw [gD, abs_of_nonneg (by positivity), div_le_iff₀ hd]
    have : y ^ 5 ≤ y ^ 3 * (y ^ 2 + a ^ 2) := by nlinarith [pow_nonneg hy 3, sq_nonneg a]
    nlinarith [pow_nonneg hy 3,
      mul_le_mul_of_nonneg_right hB (by positivity : (0 : ℝ) ≤ (1 + y) ^ 3)]
  · rw [gD, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2) ≤ 5 * y ^ 2 * (y ^ 2 + a ^ 2) ^ 2 := by
      nlinarith [pow_nonneg hy 2, sq_nonneg a, sq_nonneg (y * a), pow_nonneg hy 4]
    calc y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2) ≤ 5 * y ^ 2 * (y ^ 2 + a ^ 2) ^ 2 := this
      _ ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 * (y ^ 2 + a ^ 2) ^ 2 := by gcongr; nlinarith
  · rw [gD, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : 2 * y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) ≤
        20 * y * (y ^ 2 + a ^ 2) ^ 3 := by
      have e : 20 * y * (y ^ 2 + a ^ 2) ^ 3 - 2 * y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 +
          3 * y ^ 4) =
          2 * y * (7 * y ^ 6 + 21 * a ^ 2 * y ^ 4 + 20 * a ^ 4 * y ^ 2 + 10 * a ^ 6) := by
        ring
      have : 0 ≤ 2 * y * (7 * y ^ 6 + 21 * a ^ 2 * y ^ 4 + 20 * a ^ 4 * y ^ 2 + 10 * a ^ 6) := by
        positivity
      linarith
    calc 2 * y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) ≤ 20 * y * (y ^ 2 + a ^ 2) ^ 3 :=
          this
      _ ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 * (y ^ 2 + a ^ 2) ^ 3 := by gcongr; nlinarith
  · rw [gD, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : 6 * y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) ≤
        60 * (y ^ 2 + a ^ 2) ^ 4 := by
      nlinarith [pow_nonneg hy 2, sq_nonneg a, pow_nonneg (sq_nonneg a) 2,
        pow_nonneg (sq_nonneg a) 3, pow_nonneg (sq_nonneg a) 4, pow_nonneg hy 4, pow_nonneg hy 6,
        pow_nonneg hy 8, mul_nonneg (pow_nonneg hy 2) (pow_nonneg (sq_nonneg a) 3),
        mul_nonneg (pow_nonneg hy 4) (pow_nonneg (sq_nonneg a) 2),
        mul_nonneg (pow_nonneg hy 6) (sq_nonneg a)]
    calc 6 * y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) ≤
        60 * (y ^ 2 + a ^ 2) ^ 4 := this
      _ ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 * (y ^ 2 + a ^ 2) ^ 4 := by gcongr; nlinarith
  · simp only [gD]
    rw [abs_mul, abs_of_pos (by positivity)]
    have hr := abs_r5_le (a := a) hy
    have ha6 : (a ^ 2) ^ 3 ≤ (y ^ 2 + a ^ 2) ^ 3 := by gcongr; nlinarith [sq_nonneg y]
    calc 24 * a ^ 4 * |r5 a y| ≤ 24 * a ^ 4 * (5 * y / (y ^ 2 + a ^ 2) ^ 3) := by gcongr
      _ ≤ 24 * a ^ 4 * (5 * y / (a ^ 2) ^ 3) := by gcongr
      _ = 120 / a ^ 2 * y := by field_simp; ring
      _ ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 := by
          have : 120 / a ^ 2 ≤ 60 + 120 / a ^ 2 := le_add_of_nonneg_left (by norm_num)
          calc 120 / a ^ 2 * y ≤ (60 + 120 / a ^ 2) * y := by gcongr
            _ ≤ (60 + 120 / a ^ 2) * (1 + y) ^ 3 := by gcongr

/-! ### Integration by parts against `e^{-cy}` -/

theorem tendsto_pow_mul_exp_neg_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => y ^ n * exp (-(c * y))) atTop (𝓝 0) := by
  have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (c ^ n)⁻¹
  simp only [mul_zero] at this
  refine this.congr fun y => ?_
  simp only [Function.comp_apply, id]
  field_simp
  ring

theorem integrableOn_one_add_pow_mul_exp {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => (1 + y) ^ 3 * exp (-(c * y))) (Ioi 0) := by
  have h := (((integrableOn_pow_mul_exp 0 hc).add ((integrableOn_pow_mul_exp 1 hc).const_mul 3)).add
    ((integrableOn_pow_mul_exp 2 hc).const_mul 3)).add (integrableOn_pow_mul_exp 3 hc)
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

theorem tendsto_one_add_pow_mul_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => (1 + y) ^ 3 * exp (-(c * y))) atTop (𝓝 0) := by
  have := (((tendsto_pow_mul_exp_neg_mul 0 hc).add ((tendsto_pow_mul_exp_neg_mul 1 hc).const_mul
    3)).add ((tendsto_pow_mul_exp_neg_mul 2 hc).const_mul 3)).add (tendsto_pow_mul_exp_neg_mul 3 hc)
  simp only [mul_zero, add_zero] at this
  exact this.congr fun y => by ring

theorem integrableOn_exp_mul_gD {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {m : ℕ} (hm : m ≤ 4) :
    IntegrableOn (fun y => exp (-(c * y)) * gD a m y) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_one_add_pow_mul_exp hc).const_mul (60 + 120 / a ^ 2))
    ((Continuous.continuousOn (by have := continuous_gD ha.ne' m; fun_prop)).aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun y hy => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (-(c * y)) * |gD a m y| ≤ exp (-(c * y)) * ((60 + 120 / a ^ 2) * (1 + y) ^ 3) := by
        gcongr; exact abs_gD_le ha hm (le_of_lt hy)
    _ = (60 + 120 / a ^ 2) * ((1 + y) ^ 3 * exp (-(c * y))) := by ring

theorem tendsto_exp_mul_gD {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {m : ℕ} (hm : m ≤ 4) :
    Tendsto (fun y => exp (-(c * y)) * gD a m y) atTop (𝓝 0) := by
  have hlim := (tendsto_one_add_pow_mul_exp hc).const_mul (60 + 120 / a ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (-(c * y)) * |gD a m y| ≤ exp (-(c * y)) * ((60 + 120 / a ^ 2) * (1 + y) ^ 3) := by
        gcongr; exact abs_gD_le ha hm hy
    _ = (60 + 120 / a ^ 2) * ((1 + y) ^ 3 * exp (-(c * y))) := by ring

/-- One integration by parts: `c ∫_0^∞ e^{-cy} h = ∫_0^∞ e^{-cy} h'` when `h(0) = 0`. -/
theorem integral_exp_mul_eq {c : ℝ} {h h' : ℝ → ℝ} (hd : ∀ y, HasDerivAt h (h' y) y) (h0 : h 0 = 0)
    (hi : IntegrableOn (fun y => exp (-(c * y)) * h y) (Ioi 0))
    (hi' : IntegrableOn (fun y => exp (-(c * y)) * h' y) (Ioi 0))
    (hlim : Tendsto (fun y => exp (-(c * y)) * h y) atTop (𝓝 0)) :
    c * ∫ y in Ioi 0, exp (-(c * y)) * h y = ∫ y in Ioi 0, exp (-(c * y)) * h' y := by
  have hΦ : ∀ y, HasDerivAt (fun y => -(exp (-(c * y)) * h y))
      (c * (exp (-(c * y)) * h y) - exp (-(c * y)) * h' y) y := by
    intro y
    have he : HasDerivAt (fun y => exp (-(c * y))) (exp (-(c * y)) * (-(c * 1))) y :=
      ((hasDerivAt_id y).const_mul c).neg.exp
    convert (he.mul (hd y)).neg using 1
    ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto (hΦ 0).continuousAt.continuousWithinAt
    (fun y _ => hΦ y) ((hi.const_mul c).sub hi') (by simpa using hlim.neg)
  rw [integral_sub (hi.const_mul c) hi', integral_const_mul] at this
  simp only [mul_zero, neg_zero, exp_zero, h0, mul_zero, neg_zero, sub_zero] at this
  linarith

/-- Four integrations by parts:
`∫_0^∞ c⁴ e^{-cy} y⁵ / (y² + a²) dy = 24 a⁴ ∫_0^∞ e^{-cy} r₅(a, y) dy`. -/
theorem integral_exp_mul_gD_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    c ^ 4 * ∫ y in Ioi 0, exp (-(c * y)) * gD a 0 y =
      24 * a ^ 4 * ∫ y in Ioi 0, exp (-(c * y)) * r5 a y := by
  have step : ∀ m < 4, c * ∫ y in Ioi 0, exp (-(c * y)) * gD a m y =
      ∫ y in Ioi 0, exp (-(c * y)) * gD a (m + 1) y := fun m hm =>
    integral_exp_mul_eq (hasDerivAt_gD ha.ne' hm) (gD_zero hm)
      (integrableOn_exp_mul_gD ha hc (by omega)) (integrableOn_exp_mul_gD ha hc (by omega))
      (tendsto_exp_mul_gD ha hc (by omega))
  have h4 : ∫ y in Ioi 0, exp (-(c * y)) * gD a 4 y =
      24 * a ^ 4 * ∫ y in Ioi 0, exp (-(c * y)) * r5 a y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [gD]
    ring
  rw [← h4, ← step 3 (by norm_num), ← step 2 (by norm_num), ← step 1 (by norm_num),
    ← step 0 (by norm_num)]
  ring

/-! ### Summing over `ℓ` -/

/-- `f(y) = ∑_{ℓ ≥ 1} e^{-2πℓy} = 1 / (e^{2πy} - 1)`. -/
noncomputable def fq (y : ℝ) : ℝ := ∑' ℓ : ℕ, exp (-((2 * π * (ℓ + 1)) * y))

theorem cL_pos (ℓ : ℕ) : 0 < 2 * π * ((ℓ : ℝ) + 1) := by positivity

theorem wTerm_div_eq (a : ℝ) (ℓ : ℕ) (y : ℝ) :
    wTerm ℓ y / (y ^ 2 + a ^ 2) =
      (2 * π * (ℓ + 1)) ^ 4 / 12 * (exp (-((2 * π * (ℓ + 1)) * y)) * gD a 0 y) := by
  simp only [wTerm, gD]
  ring

theorem integral_wTerm_div {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    ∫ y in Ioi 0, wTerm ℓ y / (y ^ 2 + a ^ 2) =
      2 * a ^ 4 * ∫ y in Ioi 0, exp (-((2 * π * (ℓ + 1)) * y)) * r5 a y := by
  simp only [wTerm_div_eq]
  rw [integral_const_mul, div_mul_eq_mul_div, integral_exp_mul_gD_zero ha (cL_pos ℓ)]
  ring

theorem integrableOn_wTerm_div {a : ℝ} (ha : 0 < a) (ℓ : ℕ) :
    IntegrableOn (fun y => wTerm ℓ y / (y ^ 2 + a ^ 2)) (Ioi 0) := by
  simp only [wTerm_div_eq]
  exact (integrableOn_exp_mul_gD ha (cL_pos ℓ) (by norm_num)).const_mul _

theorem integrableOn_exp_mul_r5 {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun y => exp (-(c * y)) * r5 a y) (Ioi 0) := by
  refine IntegrableOn.congr_fun ((integrableOn_exp_mul_gD ha hc (m := 4) le_rfl).const_mul
    (24 * a ^ 4)⁻¹) (fun y _ => ?_) measurableSet_Ioi
  simp only [gD]
  field_simp

theorem integral_abs_exp_mul_r5_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ y in Ioi 0, ‖exp (-(c * y)) * r5 a y‖ ≤ 5 / a ^ 6 * (1 / c ^ 2) := by
  have hi : IntegrableOn (fun y : ℝ => 5 / a ^ 6 * (y ^ 1 * exp (-(c * y)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp 1 hc).const_mul _
  calc ∫ y in Ioi 0, ‖exp (-(c * y)) * r5 a y‖
      ≤ ∫ y in Ioi 0, 5 / a ^ 6 * (y ^ 1 * exp (-(c * y))) := by
        refine setIntegral_mono_on (integrableOn_exp_mul_r5 ha hc).norm hi measurableSet_Ioi
          fun y hy => ?_
        have hy : 0 < y := hy
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
        have ha6 : (a ^ 2) ^ 3 ≤ (y ^ 2 + a ^ 2) ^ 3 := by gcongr; nlinarith [sq_nonneg y]
        calc exp (-(c * y)) * |r5 a y| ≤ exp (-(c * y)) * (5 * y / (y ^ 2 + a ^ 2) ^ 3) := by
              gcongr; exact abs_r5_le hy.le
          _ ≤ exp (-(c * y)) * (5 * y / (a ^ 2) ^ 3) := by gcongr
          _ = 5 / a ^ 6 * (y ^ 1 * exp (-(c * y))) := by ring
    _ = 5 / a ^ 6 * (1 / c ^ 2) := by
        rw [integral_const_mul, integral_pow_mul_exp 1 hc]
        norm_num

theorem hasSum_integral_exp_mul_r5 {a : ℝ} (ha : 0 < a) :
    HasSum (fun ℓ : ℕ => ∫ y in Ioi 0, exp (-((2 * π * (ℓ + 1)) * y)) * r5 a y)
      (∫ y in Ioi 0, fq y * r5 a y) := by
  have h := hasSum_integral_of_summable_integral_norm
    (F := fun (ℓ : ℕ) y => exp (-((2 * π * ((ℓ : ℝ) + 1)) * y)) * r5 a y)
    (μ := volume.restrict (Ioi 0))
    (fun ℓ => integrableOn_exp_mul_r5 ha (cL_pos ℓ)) ?_
  · simpa only [fq, tsum_mul_right] using h
  · have hs : Summable fun ℓ : ℕ => 5 / a ^ 6 * (1 / (2 * π * ((ℓ : ℝ) + 1)) ^ 2) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
      refine (this.mul_left (1 / (2 * π) ^ 2)).congr fun ℓ => ?_
      push_cast
      field_simp
    refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun y => norm_nonneg _)
      (fun ℓ => ?_) hs
    simpa only [one_div] using integral_abs_exp_mul_r5_le ha (cL_pos ℓ)

/-- Step 1: `∫_0^∞ w(y) / (y² + a²) dy = 2a⁴ ∫_0^∞ f(y) r₅(a, y) dy`. -/
theorem integral_wt_div_eq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, wt y / (y ^ 2 + a ^ 2) = 2 * a ^ 4 * ∫ y in Ioi 0, fq y * r5 a y := by
  have hS : Summable fun ℓ : ℕ => ∫ y in Ioi 0, ‖wTerm ℓ y / (y ^ 2 + a ^ 2)‖ := by
    refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun y => norm_nonneg _)
      (fun ℓ => ?_) ((hasSum_integral_pow_mul_wTerm 0).summable.mul_left (1 / a ^ 2))
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_wTerm_div ha ℓ).norm
      ((integrableOn_pow_mul_wTerm 0 ℓ).const_mul _) measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    have hw := wTerm_nonneg ℓ hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_zero, one_mul,
      div_le_iff₀ (by positivity)]
    calc wTerm ℓ y = 1 / a ^ 2 * wTerm ℓ y * a ^ 2 := by field_simp
      _ ≤ 1 / a ^ 2 * wTerm ℓ y * (y ^ 2 + a ^ 2) := by gcongr; nlinarith [sq_nonneg y]
  have h := hasSum_integral_of_summable_integral_norm
    (F := fun ℓ y => wTerm ℓ y / (y ^ 2 + a ^ 2)) (μ := volume.restrict (Ioi 0))
    (fun ℓ => integrableOn_wTerm_div ha ℓ) hS
  have h' : ∫ y in Ioi 0, wt y / (y ^ 2 + a ^ 2) =
      ∑' ℓ : ℕ, ∫ y in Ioi 0, wTerm ℓ y / (y ^ 2 + a ^ 2) := by
    rw [h.tsum_eq]
    simp only [wt, tsum_div_const]
  rw [h']
  simp only [integral_wTerm_div ha]
  rw [tsum_mul_left, (hasSum_integral_exp_mul_r5 ha).tsum_eq]

/-! ### The partial fraction expansion of `f` -/

theorem exp_neg_two_pi_lt_one {y : ℝ} (hy : 0 < y) : exp (-(2 * π * y)) < 1 := by
  rw [exp_lt_one_iff]
  have := pi_pos
  nlinarith

theorem fq_eq {y : ℝ} (hy : 0 < y) :
    fq y = exp (-(2 * π * y)) / (1 - exp (-(2 * π * y))) := by
  have hq := exp_neg_two_pi_lt_one hy
  have hg := tsum_geometric_of_lt_one (exp_pos (-(2 * π * y))).le hq
  rw [fq, div_eq_mul_inv, ← hg, ← tsum_mul_left]
  congr 1
  ext ℓ
  rw [← pow_succ', ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem mem_integerComplement_mul_I {y : ℝ} (hy : y ≠ 0) :
    (y : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have := congr_arg Complex.im hn
  simp at this
  exact hy this.symm

theorem cotTerm_mul_I {y : ℝ} (hy : 0 < y) (n : ℕ) :
    cotTerm ((y : ℂ) * Complex.I) n =
      ((-(2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ) * Complex.I := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : (y : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have := congr_arg Complex.im h
    exact hy.ne' (by simpa using this)
  have h2 : (y : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have := congr_arg Complex.im h
    exact hy.ne' (by simpa using this)
  have h3 : ((y ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : y ^ 2 + ((n : ℝ) + 1) ^ 2 ≠ 0)
  simp only [cotTerm]
  push_cast at h3 ⊢
  field_simp
  linear_combination (2 * (y : ℂ) ^ 3 * Complex.I) * Complex.I_sq

theorem cot_pi_mul_I {y : ℝ} (hy : 0 < y) :
    (π : ℂ) * Complex.cot (π * ((y : ℂ) * Complex.I)) - 1 / ((y : ℂ) * Complex.I) =
      -Complex.I * ((π * (1 + exp (-(2 * π * y))) / (1 - exp (-(2 * π * y))) - 1 / y : ℝ) : ℂ) := by
  have hq := exp_neg_two_pi_lt_one hy
  have hq' : (1 : ℂ) - ((exp (-(2 * π * y)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.2 hq).ne'
  have hexp : Complex.exp (2 * π * Complex.I * ((y : ℂ) * Complex.I)) =
      ((exp (-(2 * π * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [Complex.cot_pi_eq_exp_ratio, hexp]
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∑_{k ≥ 1} y / (y² + k²) = π f(y) + π/2 - 1/(2y)` for `y > 0`: the partial fraction expansion
of `coth`, from Mathlib's `cot_series_rep'` at `iy`. -/
theorem hasSum_div_sq_add_sq {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => y / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) (π * fq y + π / 2 - 1 / (2 * y)) := by
  have hx := mem_integerComplement_mul_I hy.ne'
  have h := (summable_cotTerm hx).hasSum
  have ht : ∑' n, cotTerm ((y : ℂ) * Complex.I) n =
      (π : ℂ) * Complex.cot (π * ((y : ℂ) * Complex.I)) - 1 / ((y : ℂ) * Complex.I) :=
    (cot_series_rep' hx).symm
  rw [ht, cot_pi_mul_I hy] at h
  simp_rw [cotTerm_mul_I hy] at h
  have h2 := h.div_const Complex.I
  simp only [mul_div_assoc, div_self Complex.I_ne_zero, mul_one, neg_mul] at h2
  rw [neg_div, mul_div_cancel_left₀ _ Complex.I_ne_zero, ← Complex.ofReal_neg,
    Complex.hasSum_ofReal] at h2
  have h3 := h2.div_const (-2)
  have hq := exp_neg_two_pi_lt_one hy
  have hq' : 1 - exp (-(2 * π * y)) ≠ 0 := (sub_pos.2 hq).ne'
  convert h3 using 1
  · ext n
    field_simp
  · rw [fq_eq hy]
    generalize exp (-(2 * π * y)) = q at hq' ⊢
    field_simp
    ring

/-! ### Assembling the pole formula -/

theorem integrableOn_mul_abs_r5 {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y => y * |r5 a y|) (Ioi 0) := by
  refine integrableOn_of_le_inv_sq_add_sq (C := 5 / a ^ 2) ha.ne'
    (by have := continuousOn_r5 ha.ne'; fun_prop) fun y hy => ?_
  have hy : 0 < y := hy
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity)]
  calc y * |r5 a y| ≤ y * (5 * y / (y ^ 2 + a ^ 2) ^ 3) := by gcongr; exact abs_r5_le hy.le
    _ = 5 * y ^ 2 / (y ^ 2 + a ^ 2) ^ 3 := by ring
    _ ≤ 5 * (y ^ 2 + a ^ 2) / (y ^ 2 + a ^ 2) ^ 3 := by gcongr; nlinarith [sq_nonneg a]
    _ = 5 / ((y ^ 2 + a ^ 2) * (y ^ 2 + a ^ 2)) := by field_simp
    _ ≤ 5 / (a ^ 2 * (y ^ 2 + a ^ 2)) := by gcongr; nlinarith [sq_nonneg y]
    _ = 5 / a ^ 2 / (y ^ 2 + a ^ 2) := by rw [div_div]

theorem hasSum_integral_yk5 {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => ∫ y in Ioi 0, yk5 a ((n : ℝ) + 1) y)
      (∫ y in Ioi 0, ∑' n : ℕ, yk5 a ((n : ℝ) + 1) y) := by
  refine hasSum_integral_of_summable_integral_norm (fun n => integrableOn_yk5 ha) ?_
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 * ∫ y in Ioi 0, y * |r5 a y| :=
    ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))).mul_right
      _ |>.congr fun n => by push_cast; ring
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
    (fun n => ?_) hs
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_yk5 ha).norm ((integrableOn_mul_abs_r5 ha).const_mul _)
    measurableSet_Ioi fun y hy => ?_
  have hy : 0 < y := hy
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, yk5, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ y / (y ^ 2 + ((n : ℝ) + 1) ^ 2))]
  calc y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) * |r5 a y| ≤ y / ((n : ℝ) + 1) ^ 2 * |r5 a y| := by
        gcongr; nlinarith [sq_nonneg y]
    _ = 1 / ((n : ℝ) + 1) ^ 2 * (y * |r5 a y|) := by ring

theorem fq_mul_r5 {a y : ℝ} (hy : 0 < y) :
    fq y * r5 a y = 1 / π * ∑' n : ℕ, yk5 a ((n : ℝ) + 1) y - 1 / 2 * r5 a y +
      1 / (2 * π) * q5 a y := by
  have h := (hasSum_div_sq_add_sq hy).tsum_eq
  have hfq : fq y = (∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) - π / 2 + 1 / (2 * y)) / π := by
    rw [h]; field_simp; ring
  simp only [yk5]
  rw [tsum_mul_right, hfq, r5_eq_mul_q5]
  field_simp

/-- `∫_0^∞ f(y) r₅(a, y) dy = -1/(8a⁴) + 1/(4a⁵) + (1/2) ∑_{k ≥ 1} (a + k)⁻⁵`. -/
theorem integral_fq_mul_r5 {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, fq y * r5 a y =
      -(1 / (8 * a ^ 4)) + 1 / (4 * a ^ 5) + 1 / 2 * ∑' n : ℕ, 1 / (a + n + 1) ^ 5 := by
  have hvals : ∀ n : ℕ, ∫ y in Ioi 0, yk5 a ((n : ℝ) + 1) y = π / 2 * (1 / (a + n + 1) ^ 5) := by
    intro n
    rw [integral_yk5 ha (by positivity)]
    field_simp
    ring
  have hS : HasSum (fun n : ℕ => π / 2 * (1 / (a + n + 1) ^ 5))
      (∫ y in Ioi 0, ∑' n : ℕ, yk5 a ((n : ℝ) + 1) y) := by
    simpa only [hvals] using hasSum_integral_yk5 ha
  have hpos : 0 < ∫ y in Ioi 0, ∑' n : ℕ, yk5 a ((n : ℝ) + 1) y := by
    rw [← hS.tsum_eq]
    exact hS.summable.tsum_pos (fun n => by positivity) 0 (by positivity)
  have hint : IntegrableOn (fun y => ∑' n : ℕ, yk5 a ((n : ℝ) + 1) y) (Ioi 0) :=
    Integrable.of_integral_ne_zero hpos.ne'
  have h1 : IntegrableOn (fun x => 1 / π * ∑' n : ℕ, yk5 a ((n : ℝ) + 1) x - 1 / 2 * r5 a x)
      (Ioi 0) := (hint.const_mul _).sub ((integrableOn_r5 ha).const_mul _)
  have h2 : IntegrableOn (fun x => 1 / (2 * π) * q5 a x) (Ioi 0) :=
    (integrableOn_q5 ha).const_mul _
  have h3 : IntegrableOn (fun x => 1 / π * ∑' n : ℕ, yk5 a ((n : ℝ) + 1) x) (Ioi 0) :=
    hint.const_mul _
  have h4 : IntegrableOn (fun x => 1 / 2 * r5 a x) (Ioi 0) := (integrableOn_r5 ha).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => fq_mul_r5 (a := a) hy),
    integral_add h1 h2, integral_sub h3 h4, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_r5 ha, integral_q5 ha, ← hS.tsum_eq,
    tsum_mul_left]
  have := pi_pos
  field_simp
  ring

/-- `∫_0^∞ w(y) / (y² + a²) dy = a⁴ ∑_{k ≥ 1} (a + k)⁻⁵ - 1/4 + 1/(2a)`, i.e.
`a⁴ ζ(5, a) - 1/(2a) - 1/4`, for every real `a > 0`. -/
theorem integral_wt_div_sq_add_sq_real {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, wt y / (y ^ 2 + a ^ 2) =
      a ^ 4 * ∑' n : ℕ, 1 / (a + n + 1) ^ 5 - 1 / 4 + 1 / (2 * a) := by
  rw [integral_wt_div_eq ha, integral_fq_mul_r5 ha]
  field_simp
  ring

/-! ### `ζ(5)` -/

theorem riemannZeta_five_re : (riemannZeta 5).re = ∑' n : ℕ, 1 / (n : ℝ) ^ 5 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  push_cast at h
  have : (∑' n : ℕ, 1 / (n : ℂ) ^ 5) = ((∑' n : ℕ, 1 / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  rw [h, this, Complex.ofReal_re]

theorem summable_one_div_pow_five : Summable fun n : ℕ => 1 / (n : ℝ) ^ 5 :=
  Real.summable_one_div_nat_pow.2 (by norm_num)

theorem H5_succ (j : ℕ) : (H5 (j + 1) : ℝ) = H5 j + 1 / ((j : ℝ) + 1) ^ 5 := by
  rw [H5, Finset.sum_Icc_succ_top (by omega), ← H5]
  push_cast
  ring

/-- `∑_{k ≥ 1} (j + k)⁻⁵ = ζ(5) - H_j^{(5)}`. -/
theorem tsum_shift_eq (j : ℕ) :
    ∑' n : ℕ, 1 / ((j : ℝ) + n + 1) ^ 5 = (riemannZeta 5).re - H5 j := by
  induction j with
  | zero =>
    rw [riemannZeta_five_re, summable_one_div_pow_five.tsum_eq_zero_add]
    simp [H5]
  | succ j ih =>
    have hs : Summable fun n : ℕ => 1 / ((j : ℝ) + n + 1) ^ 5 := by
      refine (summable_nat_add_iff (j + 1)).2 summable_one_div_pow_five |>.congr fun n => ?_
      push_cast
      ring_nf
    have e : ∑' n : ℕ, 1 / ((j : ℝ) + 1 + n + 1) ^ 5 =
        ∑' n : ℕ, 1 / ((j : ℝ) + ((n : ℝ) + 1) + 1) ^ 5 := by
      congr 1
      ext n
      ring_nf
    rw [H5_succ, ← sub_sub, ← ih, hs.tsum_eq_zero_add]
    push_cast
    rw [e]
    ring

/-- The pole values (2.3) at `X = ζ(5)` are integrals against the weight `w` of (2.10). -/
theorem integral_wt_div_sq_add_sq {j : ℕ} (hj : 1 ≤ j) :
    ∫ y in Ioi 0, wt y / (y ^ 2 + (j : ℝ) ^ 2) = aeval (riemannZeta 5).re (muPole j) := by
  rw [integral_wt_div_sq_add_sq_real (by exact_mod_cast hj : (0 : ℝ) < j), tsum_shift_eq,
    aeval_muPole]

end Zeta5
