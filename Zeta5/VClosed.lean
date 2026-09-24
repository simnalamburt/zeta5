/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Zeta5.Field

/-!
# The external field in closed form (A.5), and its minimum

For `s > 0`, `J(s², c) = ∫_0^c log(s² + u²) du = c log(s² + c²) - 2c + 2s arctan(c/s)`, so
`V(s²) = Φ(s)` with
`Φ(s) = -3πs + log(1 + s²) - 6α log(s² + α²) - 2s arctan s + 12s arctan(s/α) - 2 + 12α`
(using `arctan(1/s) = π/2 - arctan s`). This is (A.5) of the paper. Its derivative is
`Φ'(s) = 2P(s)`, `P(s) = -3π/2 - arctan s + 6 arctan(s/α)`, and `P` is increasing on `[0, 1/2]`
since `P'(s) = -1/(1+s²) + 6α/(α²+s²)` changes sign only at `s² = 711/880`. Hence `V` decreases
on `(0, q]` and increases on `[q', ∞)` as soon as `P(√q) ≤ 0 ≤ P(√q')` and `√q' ≤ 1/2`.
-/

open Real Set

namespace Zeta5

theorem alpha_real : (alpha : ℝ) = 3 / 40 := by rw [alpha]; push_cast; ring

theorem lambda_real : (lambda : ℝ) = 37 / 40 := by rw [lambda]; push_cast; ring

/-- `Φ(s) = V(s²)`, (A.5). -/
noncomputable def Phi (s : ℝ) : ℝ :=
  -3 * π * s + log (1 + s ^ 2) - 6 * (3 / 40) * log (s ^ 2 + (3 / 40) ^ 2) -
    2 * s * arctan s + 12 * s * arctan (s / (3 / 40)) - 2 + 12 * (3 / 40)

/-- `P(s) = Φ'(s)/2`. -/
noncomputable def Pd (s : ℝ) : ℝ := -3 * π / 2 - arctan s + 6 * arctan (s / (3 / 40))

/-! ### The closed form -/

theorem hasDerivAt_Jprim {s : ℝ} (hs : 0 < s) (u : ℝ) :
    HasDerivAt (fun u => u * log (s ^ 2 + u ^ 2) - 2 * u + 2 * s * arctan (u / s))
      (log (s ^ 2 + u ^ 2)) u := by
  have hpos : 0 < s ^ 2 + u ^ 2 := by positivity
  have h1 : HasDerivAt (fun u => s ^ 2 + u ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).const_add (s ^ 2)
  have h2 := ((hasDerivAt_id u).mul (h1.log hpos.ne'))
  have h3 := ((hasDerivAt_id u).div_const s).arctan.const_mul (2 * s)
  convert (h2.sub ((hasDerivAt_id u).const_mul 2)).add h3 using 1
  all_goals try with_reducible_and_instances rfl
  · funext u; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
  · simp only [id]
    field_simp
    ring

theorem Jlog_sq_eq {s : ℝ} (hs : 0 < s) (c : ℝ) :
    Jlog (s ^ 2) c = c * log (s ^ 2 + c ^ 2) - 2 * c + 2 * s * arctan (c / s) := by
  unfold Jlog
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_Jprim hs u)
    ((Continuous.log (by fun_prop) fun u => by positivity).intervalIntegrable _ _)]
  simp

theorem Vfield_sq {s : ℝ} (hs : 0 < s) : Vfield (s ^ 2) = Phi s := by
  rw [Vfield, Jlog_sq_eq hs, Jlog_sq_eq hs, sqrt_sq hs.le, alpha_real]
  have h1 : arctan (1 / s) = π / 2 - arctan s := by rw [one_div, arctan_inv_of_pos hs]
  have h2 : arctan (3 / 40 / s) = π / 2 - arctan (s / (3 / 40)) := by
    rw [← arctan_inv_of_pos (by positivity), inv_div]
  rw [h1, h2, Phi]
  ring_nf

theorem Vfield_eq {t : ℝ} (ht : 0 < t) : Vfield t = Phi √t := by
  rw [← Vfield_sq (sqrt_pos.2 ht), sq_sqrt ht.le]

/-! ### Derivatives -/

theorem hasDerivAt_Phi (s : ℝ) : HasDerivAt Phi (2 * Pd s) s := by
  have ha : (0 : ℝ) < 3 / 40 := by norm_num
  have hp1 : 0 < 1 + s ^ 2 := by positivity
  have hp2 : 0 < s ^ 2 + (3 / 40 : ℝ) ^ 2 := by positivity
  have e1 : HasDerivAt (fun s => 1 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add 1
  have e2 : HasDerivAt (fun s => s ^ 2 + (3 / 40 : ℝ) ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).add_const ((3 / 40 : ℝ) ^ 2)
  have h := (((((((hasDerivAt_id s).const_mul (-3 * π)).add (e1.log hp1.ne')).sub
    ((e2.log hp2.ne').const_mul (6 * (3 / 40)))).sub
    (((hasDerivAt_id s).const_mul 2).mul (hasDerivAt_id s).arctan)).add
    (((hasDerivAt_id s).const_mul 12).mul ((hasDerivAt_id s).div_const (3 / 40)).arctan)).sub_const
    2).add_const (12 * (3 / 40))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext s
    simp only [Phi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
  · simp only [Pd, id]
    field_simp
    ring

theorem hasDerivAt_Pd (s : ℝ) :
    HasDerivAt Pd (-(1 / (1 + s ^ 2)) + 6 * (1 / (1 + (s / (3 / 40)) ^ 2) * (1 / (3 / 40)))) s := by
  have h := ((hasDerivAt_const s (-3 * π / 2)).sub (hasDerivAt_id s).arctan).add
    (((hasDerivAt_id s).div_const (3 / 40)).arctan.const_mul 6)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext s; simp only [Pd, Pi.add_apply, Pi.sub_apply, id]
  · simp only [id]; ring

theorem continuous_Pd : Continuous Pd :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_Pd s).continuousAt

theorem continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_Phi s).continuousAt

/-- `P` is increasing on `[0, 1/2]`. -/
theorem monotoneOn_Pd : MonotoneOn Pd (Icc 0 (1 / 2)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) continuous_Pd.continuousOn
    (fun s _ => (hasDerivAt_Pd s).hasDerivWithinAt) fun s hs => ?_
  rw [interior_Icc] at hs
  have h1 : 0 < 1 + s ^ 2 := by positivity
  have h2 : 0 < 1 + (s / (3 / 40)) ^ 2 := by positivity
  rw [div_pow, show (s ^ 2 / (3 / 40) ^ 2 : ℝ) = s ^ 2 * (1600 / 9) by ring]
  rw [show 1 + s ^ 2 * (1600 / 9 : ℝ) = (9 + 1600 * s ^ 2) / 9 by ring]
  have h3 : 0 < 9 + 1600 * s ^ 2 := by positivity
  rw [neg_add_eq_sub, sub_nonneg, div_div_eq_mul_div, one_mul, div_le_iff₀ h1]
  rw [show (6 * (9 / (9 + 1600 * s ^ 2) * (1 / (3 / 40))) * (1 + s ^ 2) : ℝ) =
    720 * (1 + s ^ 2) / (9 + 1600 * s ^ 2) by field_simp; ring]
  rw [le_div_iff₀ h3]
  nlinarith [hs.1, hs.2]

/-- `P ≥ 0` on `[1/2, ∞)`: there `6 arctan(s/α) ≥ 6 arctan √3 = 2π`. -/
theorem Pd_nonneg_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) : 0 ≤ Pd s := by
  have hsqrt3 : √3 ≤ s / (3 / 40) := by
    have : √3 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have h1 : π / 3 ≤ arctan (s / (3 / 40)) := by
    have := arctan_strictMono.monotone hsqrt3
    rwa [← tan_pi_div_three, arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])] at this
  have h2 := arctan_lt_pi_div_two s
  unfold Pd
  linarith

/-! ### Monotonicity of `V` -/

/-- If `P(√q) ≤ 0` and `√q ≤ 1/2`, `Φ` decreases on `[0, √q]`. -/
theorem antitoneOn_Phi {s₀ : ℝ} (hs₀ : s₀ ≤ 1 / 2) (hP : Pd s₀ ≤ 0) :
    AntitoneOn Phi (Icc 0 s₀) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) continuous_Phi.continuousOn
    (fun s _ => (hasDerivAt_Phi s).hasDerivWithinAt) fun s hs => ?_
  rw [interior_Icc] at hs
  have := monotoneOn_Pd ⟨hs.1.le, by linarith [hs.2]⟩ ⟨hs.1.le.trans hs.2.le, hs₀⟩ hs.2.le
  linarith

/-- If `0 ≤ P(√q')` and `√q' ≤ 1/2`, `Φ` increases on `[√q', ∞)`. -/
theorem monotoneOn_Phi {s₀ : ℝ} (hs₀0 : 0 ≤ s₀) (hs₀ : s₀ ≤ 1 / 2) (hP : 0 ≤ Pd s₀) :
    MonotoneOn Phi (Ici s₀) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) continuous_Phi.continuousOn
    (fun s _ => (hasDerivAt_Phi s).hasDerivWithinAt) fun s hs => ?_
  rw [interior_Ici] at hs
  rcases le_total s (1 / 2) with h | h
  · have := monotoneOn_Pd ⟨hs₀0, hs₀⟩ ⟨hs₀0.trans hs.le, h⟩ hs.le
    linarith
  · linarith [Pd_nonneg_of_half_le h]

theorem Vfield_antitone {q t t' : ℝ} (hq : √q ≤ 1 / 2) (hP : Pd √q ≤ 0) (ht : 0 < t)
    (htt' : t ≤ t') (ht' : t' ≤ q) : Vfield t' ≤ Vfield t := by
  rw [Vfield_eq ht, Vfield_eq (ht.trans_le htt')]
  exact antitoneOn_Phi hq hP ⟨sqrt_nonneg _, sqrt_le_sqrt (htt'.trans ht')⟩
    ⟨sqrt_nonneg _, sqrt_le_sqrt ht'⟩ (sqrt_le_sqrt htt')

theorem Vfield_monotone {q t t' : ℝ} (hq : √q ≤ 1 / 2) (hP : 0 ≤ Pd √q) (hq0 : 0 < q)
    (ht : q ≤ t) (htt' : t ≤ t') : Vfield t ≤ Vfield t' := by
  rw [Vfield_eq (hq0.trans_le ht), Vfield_eq (hq0.trans_le (ht.trans htt'))]
  exact monotoneOn_Phi (sqrt_nonneg _) hq hP (sqrt_le_sqrt ht) (sqrt_le_sqrt (ht.trans htt'))
    (sqrt_le_sqrt htt')

end Zeta5
