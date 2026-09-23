/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Elementary integrals for the pole formula

Write `r₅(a, y) = Re((y - ia)⁻⁵) = (y⁵ - 10a²y³ + 5a⁴y) / (y² + a²)⁵`. After four integrations by
parts and the partial fraction expansion of `coth`, the pole formula (2.3) reduces to the rational
integrals, for `a, k > 0`,
* `∫_0^∞ r₅(a, y) dy = 1/(4a⁴)`,
* `∫_0^∞ r₅(a, y) / y dy = π / (2a⁵)`,
* `∫_0^∞ y / (y² + k²) · r₅(a, y) dy = π / (2(a + k)⁵)`.
Each is computed from an explicit antiderivative (found with a computer algebra system and checked
here by differentiation).
-/

open Real MeasureTheory Set Filter Topology

namespace Zeta5

/-- `r₅(a, y) = Re((y - ia)⁻⁵)`. -/
noncomputable def r5 (a y : ℝ) : ℝ :=
  (y ^ 5 - 10 * a ^ 2 * y ^ 3 + 5 * a ^ 4 * y) / (y ^ 2 + a ^ 2) ^ 5

/-! ### Limits and integrability of rational functions -/

theorem tendsto_pow_div_sq_add_sq_pow (a : ℝ) {m p : ℕ} (h : m < 2 * p) :
    Tendsto (fun y : ℝ => y ^ m / (y ^ 2 + a ^ 2) ^ p) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_ge_atTop 1] with y hy
  have hy0 : 0 < y := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  calc y ^ m ≤ y ^ (2 * p - 1) := pow_le_pow_right₀ hy (by omega)
    _ = y⁻¹ * (y ^ 2) ^ p := by
        rw [← pow_mul, eq_inv_mul_iff_mul_eq₀ hy0.ne', ← pow_succ']
        congr 1
        omega
    _ ≤ y⁻¹ * (y ^ 2 + a ^ 2) ^ p := by gcongr; nlinarith [sq_nonneg a]

theorem integrableOn_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    IntegrableOn (fun y : ℝ => 1 / (y ^ 2 + a ^ 2)) (Ioi 0) := by
  have h := (integrable_inv_one_add_sq.comp_div ha).const_mul (a ^ 2)⁻¹
  refine (h.congr (Eventually.of_forall fun y => ?_)).integrableOn
  have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- An integrand bounded by `C / (y² + a²)` and continuous on `(0, ∞)` is integrable there. -/
theorem integrableOn_of_le_inv_sq_add_sq {f : ℝ → ℝ} {a C : ℝ} (ha : a ≠ 0)
    (hf : ContinuousOn f (Ioi 0)) (hb : ∀ y ∈ Ioi (0 : ℝ), |f y| ≤ C / (y ^ 2 + a ^ 2)) :
    IntegrableOn f (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_inv_sq_add_sq ha).const_mul C)
    (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs, mul_one_div]
  exact hb y hy

/-! ### Bounds for `r₅` -/

theorem abs_r5_le {a y : ℝ} (hy : 0 ≤ y) : |r5 a y| ≤ 5 * y / (y ^ 2 + a ^ 2) ^ 3 := by
  rcases eq_or_lt_of_le hy with rfl | hy'
  · simp [r5]
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [r5, abs_div, abs_of_pos (by positivity : 0 < (y ^ 2 + a ^ 2) ^ 5),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : |y ^ 5 - 10 * a ^ 2 * y ^ 3 + 5 * a ^ 4 * y| ≤ 5 * y * (y ^ 2 + a ^ 2) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y ^ 2), sq_nonneg (a ^ 2), mul_nonneg hy (sq_nonneg a),
      mul_nonneg hy (sq_nonneg (a ^ 2)), mul_nonneg hy (sq_nonneg y),
      mul_nonneg (mul_nonneg hy (sq_nonneg a)) (sq_nonneg y)]
  calc |y ^ 5 - 10 * a ^ 2 * y ^ 3 + 5 * a ^ 4 * y| * (y ^ 2 + a ^ 2) ^ 3
      ≤ 5 * y * (y ^ 2 + a ^ 2) ^ 2 * (y ^ 2 + a ^ 2) ^ 3 := by gcongr
    _ = 5 * y * (y ^ 2 + a ^ 2) ^ 5 := by ring

theorem continuousOn_r5 {a : ℝ} (ha : a ≠ 0) : Continuous (r5 a) := by
  unfold r5
  exact Continuous.div (by fun_prop) (by fun_prop) fun y => by positivity

/-! ### `∫_0^∞ r₅(a, y) dy = 1/(4a⁴)` -/

/-- An antiderivative of `r₅(a, ·)`, namely `-Re((y - ia)⁻⁴)/4`. -/
noncomputable def R4 (a y : ℝ) : ℝ :=
  -(y ^ 4 - 6 * a ^ 2 * y ^ 2 + a ^ 4) / (4 * (y ^ 2 + a ^ 2) ^ 4)

theorem hasDerivAt_R4 {a : ℝ} (ha : a ≠ 0) (y : ℝ) : HasDerivAt (R4 a) (r5 a y) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 := (((hasDerivAt_pow 4 y).sub ((hasDerivAt_pow 2 y).const_mul (6 * a ^ 2))).add_const
    (a ^ 4)).neg
  have h2 := (((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 4).const_mul 4
  convert h1.div h2 (mul_ne_zero four_ne_zero (pow_ne_zero _ hd)) using 1
  · ext x
    simp [R4]
  · simp only [r5, Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]
    norm_num
    field_simp
    ring

theorem tendsto_R4 (a : ℝ) : Tendsto (R4 a) atTop (𝓝 0) := by
  have h4 := tendsto_pow_div_sq_add_sq_pow a (m := 4) (p := 4) (by norm_num)
  have h2 := tendsto_pow_div_sq_add_sq_pow a (m := 2) (p := 4) (by norm_num)
  have h0 := tendsto_pow_div_sq_add_sq_pow a (m := 0) (p := 4) (by norm_num)
  have := ((h4.sub (h2.const_mul (6 * a ^ 2))).add (h0.const_mul (a ^ 4))).neg.div_const 4
  simp only [mul_zero, sub_zero, add_zero, neg_zero, zero_div] at this
  refine this.congr fun y => ?_
  have hd : 0 < y ^ 2 + a ^ 2 ∨ y ^ 2 + a ^ 2 = 0 := by
    rcases eq_or_lt_of_le (by positivity : 0 ≤ y ^ 2 + a ^ 2) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hd with hd | hd
  · simp only [R4]
    field_simp
  · simp [R4, hd]

theorem integrableOn_r5 {a : ℝ} (ha : 0 < a) : IntegrableOn (r5 a) (Ioi 0) := by
  refine integrableOn_of_le_inv_sq_add_sq (C := 5 / (2 * a ^ 3)) ha.ne'
    (continuousOn_r5 ha.ne').continuousOn fun y hy => ?_
  have hy : 0 < y := hy
  refine (abs_r5_le hy.le).trans ?_
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hd]
  have h2a : 2 * a * y ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (y - a)]
  have ha2 : a ^ 2 ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
  calc 5 * y * (y ^ 2 + a ^ 2) = 5 * (2 * a * y) * (y ^ 2 + a ^ 2) / (2 * a) := by
        field_simp
    _ ≤ 5 * (y ^ 2 + a ^ 2) * (y ^ 2 + a ^ 2) / (2 * a) := by gcongr
    _ = 5 / (2 * a ^ 3) * (a ^ 2 * (y ^ 2 + a ^ 2) ^ 2) := by field_simp
    _ ≤ 5 / (2 * a ^ 3) * ((y ^ 2 + a ^ 2) * (y ^ 2 + a ^ 2) ^ 2) := by gcongr
    _ = 5 / (2 * a ^ 3) * (y ^ 2 + a ^ 2) ^ 3 := by ring

/-- `∫_0^∞ r₅(a, y) dy = 1/(4a⁴)`. -/
theorem integral_r5 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, r5 a y = 1 / (4 * a ^ 4) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := R4 a)
    (hasDerivAt_R4 ha.ne' 0).continuousAt.continuousWithinAt
    (fun y _ => hasDerivAt_R4 ha.ne' y) (integrableOn_r5 ha) (tendsto_R4 a)]
  simp only [R4]
  field_simp
  ring

/-! ### `∫_0^∞ r₅(a, y) / y dy = π / (2a⁵)` -/

/-- `q₅(a, y) = r₅(a, y) / y`, extended continuously to `y = 0`. -/
noncomputable def q5 (a y : ℝ) : ℝ :=
  (y ^ 4 - 10 * a ^ 2 * y ^ 2 + 5 * a ^ 4) / (y ^ 2 + a ^ 2) ^ 5

theorem r5_eq_mul_q5 (a y : ℝ) : r5 a y = y * q5 a y := by
  simp only [r5, q5]
  ring

theorem tendsto_arctan_div (a : ℝ) (ha : 0 < a) :
    Tendsto (fun y : ℝ => arctan (y / a)) atTop (𝓝 (π / 2)) :=
  (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const ha)

theorem hasDerivAt_arctan_div {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    HasDerivAt (fun y : ℝ => arctan (y / a)) (a / (y ^ 2 + a ^ 2)) y := by
  have := ((hasDerivAt_id y).div_const a).arctan
  convert this using 1
  · simp only [id]
  · have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    simp only [id]
    field_simp
    ring

/-- An antiderivative of `q₅(a, ·)`. -/
noncomputable def F1 (a y : ℝ) : ℝ :=
  y * (12 * a ^ 6 + 14 * a ^ 4 * y ^ 2 + 11 * a ^ 2 * y ^ 4 + 3 * y ^ 6) /
    (3 * a ^ 4 * (y ^ 2 + a ^ 2) ^ 4) + arctan (y / a) / a ^ 5

theorem hasDerivAt_F1 {a : ℝ} (ha : a ≠ 0) (y : ℝ) : HasDerivAt (F1 a) (q5 a y) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 := (hasDerivAt_id y).mul ((((((hasDerivAt_pow 2 y).const_mul (14 * a ^ 4)).const_add
    (12 * a ^ 6)).add ((hasDerivAt_pow 4 y).const_mul (11 * a ^ 2))).add
    ((hasDerivAt_pow 6 y).const_mul 3)))
  have h2 := (((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 4).const_mul (3 * a ^ 4)
  have h3 := (hasDerivAt_arctan_div ha y).div_const (a ^ 5)
  convert (h1.div h2 (mul_ne_zero (by positivity) (pow_ne_zero _ hd))).add h3 using 1
  · ext x
    simp [F1]
  · simp only [q5, Pi.add_apply, Pi.pow_apply, id]
    norm_num
    field_simp
    ring

theorem tendsto_F1 {a : ℝ} (ha : 0 < a) : Tendsto (F1 a) atTop (𝓝 (π / (2 * a ^ 5))) := by
  have t1 := tendsto_pow_div_sq_add_sq_pow a (m := 1) (p := 4) (by norm_num)
  have t3 := tendsto_pow_div_sq_add_sq_pow a (m := 3) (p := 4) (by norm_num)
  have t5 := tendsto_pow_div_sq_add_sq_pow a (m := 5) (p := 4) (by norm_num)
  have t7 := tendsto_pow_div_sq_add_sq_pow a (m := 7) (p := 4) (by norm_num)
  have := ((((t1.const_mul (12 * a ^ 6)).add (t3.const_mul (14 * a ^ 4))).add
    (t5.const_mul (11 * a ^ 2))).add (t7.const_mul 3)).div_const (3 * a ^ 4) |>.add
    ((tendsto_arctan_div a ha).div_const (a ^ 5))
  simp only [mul_zero, add_zero, zero_div, zero_add] at this
  convert this using 2 with y
  · simp only [F1]
    have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
  · field_simp

theorem integrableOn_q5 {a : ℝ} (ha : 0 < a) : IntegrableOn (q5 a) (Ioi 0) := by
  have hcont : Continuous (q5 a) := by
    unfold q5
    exact Continuous.div (by fun_prop) (by fun_prop) fun y => by positivity
  refine integrableOn_of_le_inv_sq_add_sq (C := 5 / a ^ 4) ha.ne' hcont.continuousOn
    fun y hy => ?_
  have hy : 0 < y := hy
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  have ha2 : a ^ 2 ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
  rw [q5, abs_div, abs_of_pos (pow_pos hd 5), div_le_div_iff₀ (pow_pos hd 5) hd]
  have hnum : |y ^ 4 - 10 * a ^ 2 * y ^ 2 + 5 * a ^ 4| ≤ 5 * (y ^ 2 + a ^ 2) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y ^ 2), sq_nonneg (a ^ 2), sq_nonneg (a * y)]
  calc |y ^ 4 - 10 * a ^ 2 * y ^ 2 + 5 * a ^ 4| * (y ^ 2 + a ^ 2)
      ≤ 5 * (y ^ 2 + a ^ 2) ^ 2 * (y ^ 2 + a ^ 2) := by gcongr
    _ = 5 / a ^ 4 * ((a ^ 2) ^ 2 * (y ^ 2 + a ^ 2) ^ 3) := by field_simp
    _ ≤ 5 / a ^ 4 * ((y ^ 2 + a ^ 2) ^ 2 * (y ^ 2 + a ^ 2) ^ 3) := by gcongr
    _ = 5 / a ^ 4 * (y ^ 2 + a ^ 2) ^ 5 := by ring

/-- `∫_0^∞ r₅(a, y) / y dy = π / (2a⁵)`. -/
theorem integral_q5 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, q5 a y = π / (2 * a ^ 5) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := F1 a)
    (hasDerivAt_F1 ha.ne' 0).continuousAt.continuousWithinAt
    (fun y _ => hasDerivAt_F1 ha.ne' y) (integrableOn_q5 ha) (tendsto_F1 ha)]
  simp [F1]

/-! ### `∫_0^∞ y / (y² + k²) · r₅(a, y) dy = π / (2(a + k)⁵)` -/

/-- The integrand `y / (y² + k²) · r₅(a, y)`. -/
noncomputable def yk5 (a k y : ℝ) : ℝ := y / (y ^ 2 + k ^ 2) * r5 a y

/-- The numerator of the rational part of the antiderivative of `yk5 a k` for `k ≠ a`. -/
noncomputable def NK (a k y : ℝ) : ℝ :=
  12 * a ^ 8 * (a ^ 2 + k ^ 2) + a ^ 2 * (14 * a ^ 6 + 73 * a ^ 4 * k ^ 2 - 20 * a ^ 2 * k ^ 4 +
    5 * k ^ 6) * y ^ 2 + (11 * a ^ 6 + 61 * a ^ 4 * k ^ 2 + a ^ 2 * k ^ 4 - k ^ 6) * y ^ 4 +
    3 * (a ^ 4 + 6 * a ^ 2 * k ^ 2 + k ^ 4) * y ^ 6

/-- An antiderivative of `yk5 a k` for `k ≠ a`, with `D = a² - k²`. -/
noncomputable def FK (a k y : ℝ) : ℝ :=
  y * NK a k y / (3 * (a ^ 2 - k ^ 2) ^ 4 * (y ^ 2 + a ^ 2) ^ 4) +
    a * (a ^ 4 + 10 * a ^ 2 * k ^ 2 + 5 * k ^ 4) / (a ^ 2 - k ^ 2) ^ 5 * arctan (y / a) -
    k * (5 * a ^ 4 + 10 * a ^ 2 * k ^ 2 + k ^ 4) / (a ^ 2 - k ^ 2) ^ 5 * arctan (y / k)

theorem hasDerivAt_FK {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) (hak : a ^ 2 - k ^ 2 ≠ 0) (y : ℝ) :
    HasDerivAt (FK a k) (yk5 a k y) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hdk : y ^ 2 + k ^ 2 ≠ 0 := by positivity
  have h1 := (hasDerivAt_id y).mul (((((hasDerivAt_pow 2 y).const_mul
    (a ^ 2 * (14 * a ^ 6 + 73 * a ^ 4 * k ^ 2 - 20 * a ^ 2 * k ^ 4 + 5 * k ^ 6))).const_add
    (12 * a ^ 8 * (a ^ 2 + k ^ 2))).add ((hasDerivAt_pow 4 y).const_mul
    (11 * a ^ 6 + 61 * a ^ 4 * k ^ 2 + a ^ 2 * k ^ 4 - k ^ 6))).add
    ((hasDerivAt_pow 6 y).const_mul (3 * (a ^ 4 + 6 * a ^ 2 * k ^ 2 + k ^ 4))))
  have h2 := (((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 4).const_mul (3 * (a ^ 2 - k ^ 2) ^ 4)
  have h3 := (hasDerivAt_arctan_div ha y).const_mul
    (a * (a ^ 4 + 10 * a ^ 2 * k ^ 2 + 5 * k ^ 4) / (a ^ 2 - k ^ 2) ^ 5)
  have h4 := (hasDerivAt_arctan_div hk y).const_mul
    (k * (5 * a ^ 4 + 10 * a ^ 2 * k ^ 2 + k ^ 4) / (a ^ 2 - k ^ 2) ^ 5)
  convert ((h1.div h2 (mul_ne_zero (by positivity) (pow_ne_zero _ hd))).add h3).sub h4 using 1
  · ext x
    simp [FK, NK]
  · simp only [yk5, r5, Pi.add_apply, Pi.pow_apply, id]
    norm_num
    field_simp
    ring

theorem tendsto_FK {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (hak : a ^ 2 - k ^ 2 ≠ 0) :
    Tendsto (FK a k) atTop (𝓝 (π / (2 * (a + k) ^ 5))) := by
  have t1 := tendsto_pow_div_sq_add_sq_pow a (m := 1) (p := 4) (by norm_num)
  have t3 := tendsto_pow_div_sq_add_sq_pow a (m := 3) (p := 4) (by norm_num)
  have t5 := tendsto_pow_div_sq_add_sq_pow a (m := 5) (p := 4) (by norm_num)
  have t7 := tendsto_pow_div_sq_add_sq_pow a (m := 7) (p := 4) (by norm_num)
  have := (((((t1.const_mul (12 * a ^ 8 * (a ^ 2 + k ^ 2))).add (t3.const_mul
    (a ^ 2 * (14 * a ^ 6 + 73 * a ^ 4 * k ^ 2 - 20 * a ^ 2 * k ^ 4 + 5 * k ^ 6)))).add
    (t5.const_mul (11 * a ^ 6 + 61 * a ^ 4 * k ^ 2 + a ^ 2 * k ^ 4 - k ^ 6))).add
    (t7.const_mul (3 * (a ^ 4 + 6 * a ^ 2 * k ^ 2 + k ^ 4)))).div_const
    (3 * (a ^ 2 - k ^ 2) ^ 4) |>.add ((tendsto_arctan_div a ha).const_mul
      (a * (a ^ 4 + 10 * a ^ 2 * k ^ 2 + 5 * k ^ 4) / (a ^ 2 - k ^ 2) ^ 5))).sub
    ((tendsto_arctan_div k hk).const_mul
      (k * (5 * a ^ 4 + 10 * a ^ 2 * k ^ 2 + k ^ 4) / (a ^ 2 - k ^ 2) ^ 5))
  simp only [mul_zero, add_zero, zero_div, zero_add] at this
  convert this using 2 with y
  · simp only [FK, NK]
    have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
  · have hak' : a + k ≠ 0 := by positivity
    have hamk : a - k ≠ 0 := fun h => hak (by
      have : a = k := by linarith
      rw [this]; ring)
    rw [show a ^ 2 - k ^ 2 = (a - k) * (a + k) by ring]
    field_simp
    ring

theorem abs_yk5_le {a k y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    |yk5 a k y| ≤ 5 / a ^ 4 / (y ^ 2 + a ^ 2) := by
  have hd : 0 < y ^ 2 + a ^ 2 := by positivity
  have hdk : 0 ≤ y ^ 2 + k ^ 2 := by positivity
  have ha2 : a ^ 2 ≤ y ^ 2 + a ^ 2 := by nlinarith [sq_nonneg y]
  rw [yk5, abs_mul, abs_div, abs_of_nonneg hy, abs_of_nonneg hdk]
  rcases eq_or_lt_of_le hdk with h0 | hpos
  · rw [← h0, div_zero, zero_mul]; positivity
  calc y / (y ^ 2 + k ^ 2) * |r5 a y| ≤ y / (y ^ 2 + k ^ 2) * (5 * y / (y ^ 2 + a ^ 2) ^ 3) := by
        gcongr; exact abs_r5_le hy
    _ = 5 * (y ^ 2 / (y ^ 2 + k ^ 2)) / (y ^ 2 + a ^ 2) ^ 3 := by ring
    _ ≤ 5 * 1 / (y ^ 2 + a ^ 2) ^ 3 := by
        gcongr
        rw [div_le_one hpos]
        nlinarith [sq_nonneg k]
    _ ≤ 5 / a ^ 4 / (y ^ 2 + a ^ 2) := by
        rw [div_div, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (a ^ 2) ^ 2 ≤ (y ^ 2 + a ^ 2) ^ 2 := by gcongr
        nlinarith

theorem integrableOn_yk5 {a k : ℝ} (ha : 0 < a) : IntegrableOn (yk5 a k) (Ioi 0) := by
  have hcont : ContinuousOn (yk5 a k) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    unfold yk5
    exact ((continuousAt_id.div (by fun_prop) (by positivity)).mul
      ((continuousOn_r5 ha.ne').continuousAt)).continuousWithinAt
  exact integrableOn_of_le_inv_sq_add_sq (C := 5 / a ^ 4) ha.ne' hcont fun y hy =>
    (abs_yk5_le ha (le_of_lt hy)).trans_eq (by ring)

/-- An antiderivative of `yk5 a a`. -/
noncomputable def FA (a y : ℝ) : ℝ :=
  y * (-15 * a ^ 8 + 730 * a ^ 6 * y ^ 2 + 32 * a ^ 4 * y ^ 4 + 70 * a ^ 2 * y ^ 6 + 15 * y ^ 8) /
    (480 * a ^ 4 * (y ^ 2 + a ^ 2) ^ 5) + arctan (y / a) / (32 * a ^ 5)

theorem hasDerivAt_FA {a : ℝ} (ha : a ≠ 0) (y : ℝ) : HasDerivAt (FA a) (yk5 a a y) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 := (hasDerivAt_id y).mul (((((((hasDerivAt_pow 2 y).const_mul (730 * a ^ 6)).const_add
    (-15 * a ^ 8)).add ((hasDerivAt_pow 4 y).const_mul (32 * a ^ 4))).add
    ((hasDerivAt_pow 6 y).const_mul (70 * a ^ 2))).add ((hasDerivAt_pow 8 y).const_mul 15)))
  have h2 := (((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 5).const_mul (480 * a ^ 4)
  have h3 := (hasDerivAt_arctan_div ha y).div_const (32 * a ^ 5)
  convert (h1.div h2 (mul_ne_zero (by positivity) (pow_ne_zero _ hd))).add h3 using 1
  · ext x
    simp [FA]
  · simp only [yk5, r5, Pi.add_apply, Pi.pow_apply, id]
    norm_num
    field_simp
    ring

theorem tendsto_FA {a : ℝ} (ha : 0 < a) :
    Tendsto (FA a) atTop (𝓝 (π / (2 * (a + a) ^ 5))) := by
  have t1 := tendsto_pow_div_sq_add_sq_pow a (m := 1) (p := 5) (by norm_num)
  have t3 := tendsto_pow_div_sq_add_sq_pow a (m := 3) (p := 5) (by norm_num)
  have t5 := tendsto_pow_div_sq_add_sq_pow a (m := 5) (p := 5) (by norm_num)
  have t7 := tendsto_pow_div_sq_add_sq_pow a (m := 7) (p := 5) (by norm_num)
  have t9 := tendsto_pow_div_sq_add_sq_pow a (m := 9) (p := 5) (by norm_num)
  have := (((((t1.const_mul (-15 * a ^ 8)).add (t3.const_mul (730 * a ^ 6))).add
    (t5.const_mul (32 * a ^ 4))).add (t7.const_mul (70 * a ^ 2))).add
    (t9.const_mul 15)).div_const (480 * a ^ 4) |>.add
    ((tendsto_arctan_div a ha).div_const (32 * a ^ 5))
  simp only [mul_zero, add_zero, zero_div, zero_add] at this
  convert this using 2 with y
  · simp only [FA]
    have : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
  · field_simp
    ring

/-- `∫_0^∞ y / (y² + k²) · r₅(a, y) dy = π / (2(a + k)⁵)` for `a, k > 0`. -/
theorem integral_yk5 {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    ∫ y in Ioi 0, yk5 a k y = π / (2 * (a + k) ^ 5) := by
  by_cases hak : a ^ 2 - k ^ 2 = 0
  · have : k = a := by nlinarith
    subst this
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := FA k)
      (hasDerivAt_FA hk.ne' 0).continuousAt.continuousWithinAt
      (fun y _ => hasDerivAt_FA hk.ne' y) (integrableOn_yk5 hk) (tendsto_FA hk)]
    simp [FA]
  · rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := FK a k)
      (hasDerivAt_FK ha.ne' hk.ne' hak 0).continuousAt.continuousWithinAt
      (fun y _ => hasDerivAt_FK ha.ne' hk.ne' hak y) (integrableOn_yk5 ha)
      (tendsto_FK ha hk hak)]
    simp [FK]

end Zeta5
