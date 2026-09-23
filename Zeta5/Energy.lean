/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Potential

/-!
# The logarithmic energy bound (6.9)

For every configuration `t₁, …, t_h > 0` of distinct points,
`2 ∑_{i<j} log|t_i - t_j| - K ∑ V(t_i) + ∑ √t_i ≤ (λM₀ - I(ρ)) K² + o(K²)`,
uniformly in the configuration. This is §6.1 of the paper. We compare the normalised counting
measure `σ = K⁻¹ ∑ δ_{t_i}` with the measure `ρ` of Lemma 6.1, which has the same mass `h/K = λ`,
through the regularised form of Lemma 6.2 (`Zeta5.logEnergy_nonpos`): the kernel
`log((x - y)² + δ²)` replaces the circles of radius `ε` of the paper. The diagonal then costs
`h log δ`, and the error in the cross term is `o(1)` by `Zeta5.exists_regularize_rho`.

The potential inequality (6.2) on `(0, 2]` is the numerical part of Lemma 6.1 (Appendix A),
`Zeta5.potential_le_M0`. For `t ≥ 2` we prove (6.8) directly.
-/

open Real MeasureTheory Set Filter

namespace Zeta5

/-! ### The potential inequality (6.7), (6.8) -/

/-- `U^ρ(t) ≤ λ log t` for `t ≥ 2`, since `ρ` lives on `[0, 2]`. -/
theorem Urho_le_log {t : ℝ} (ht : 2 ≤ t) : Urho t ≤ 37 / 40 * log t := by
  rw [← integral_log_rho]
  calc ∫ u, log |t - u| ∂rho ≤ ∫ _, log t ∂rho := by
        refine integral_mono_ae (integrable_log_rho t) (integrable_const _) ?_
        filter_upwards [ae_rho] with u hu
        rcases eq_or_ne (t - u) 0 with h | h
        · rw [h, abs_zero, log_zero]; exact log_nonneg (by linarith)
        · exact log_le_log (abs_pos.2 h)
            (by rw [abs_of_nonneg (by linarith [hu.2])]; linarith [hu.1])
    _ = 37 / 40 * log t := by rw [integral_const, smul_eq_mul, rho_real_univ]

theorem log_le_Jlog_one {t : ℝ} (ht : 0 < t) : log t ≤ Jlog t 1 := by
  have hcont : Continuous fun u : ℝ => log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => by positivity
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one intervalIntegrable_const
    (hcont.intervalIntegrable 0 1)
    (fun u _ => log_le_log ht (by nlinarith [sq_nonneg u]) :
      ∀ u ∈ Icc (0 : ℝ) 1, log t ≤ log (t + u ^ 2))
  unfold Jlog
  simpa using h

theorem Jlog_alpha_le {t : ℝ} (ht : 0 < t) :
    Jlog t alpha ≤ alpha * log t + alpha ^ 3 / (3 * t) := by
  have ha : (0 : ℝ) ≤ alpha := by rw [alpha_real]; norm_num
  have hcont : Continuous fun u : ℝ => log (t + u ^ 2) :=
    Continuous.log (by fun_prop) fun u => by positivity
  have h := intervalIntegral.integral_mono_on (μ := volume) ha (hcont.intervalIntegrable _ _)
    ((continuous_const.add ((continuous_pow 2).div_const t)).intervalIntegrable 0 (alpha : ℝ))
    (fun u _ => by
      have : log (t + u ^ 2) - log t ≤ u ^ 2 / t := by
        rw [← log_div (by positivity) ht.ne']
        refine (log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
        field_simp
        ring
      linarith :
      ∀ u ∈ Icc (0 : ℝ) alpha, log (t + u ^ 2) ≤ log t + u ^ 2 / t)
  simp only [Pi.add_apply] at h
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (((continuous_pow 2).div_const t).intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_div, integral_pow] at h
  simp only [sub_zero, smul_eq_mul] at h
  unfold Jlog
  convert h using 1
  ring

/-- (6.8) and (6.7) for `t ≥ 2`. -/
theorem field_bound_large {t Kr : ℝ} (ht : 2 ≤ t) (hK : 2 ≤ Kr) :
    2 * Urho t - Vfield t + √t / Kr ≤ M0 := by
  have ht0 : 0 < t := by linarith
  have hU := Urho_le_log ht
  have h1 := log_le_Jlog_one ht0
  have h2 := Jlog_alpha_le ht0
  rw [alpha_real] at h2
  set s := √t with hs
  have hs0 : 0 ≤ s := sqrt_nonneg t
  have hss : s ^ 2 = t := sq_sqrt ht0.le
  have hs1 : 1.41 ≤ s := by nlinarith
  have hlog : log t ≤ 2 * (s - 1) := by
    rw [← hss, Real.log_pow]
    have := log_le_sub_one_of_pos (by linarith : 0 < s)
    push_cast
    linarith
  have hsK : s / Kr ≤ s / 2 := div_le_div_of_nonneg_left hs0 two_pos hK
  have hpi : 3.14 * s ≤ π * s := mul_le_mul_of_nonneg_right pi_gt_d2.le hs0
  have hα : (3 / 40 : ℝ) ^ 3 / (3 * t) ≤ (3 / 40) ^ 3 / 6 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
  rw [Vfield, M0_real, alpha_real]
  nlinarith

/-- (6.7): `2U^ρ(t) ≤ V(t) - √t/K + M₀ + √2/K` for `t > 0` and `K ≥ 2`. -/
theorem two_Urho_le {t Kr : ℝ} (ht : 0 < t) (hK : 2 ≤ Kr) :
    2 * Urho t ≤ Vfield t - √t / Kr + M0 + √2 / Kr := by
  have hK0 : 0 < Kr := by linarith
  rcases le_total t 2 with h | h
  · have := potential_le_M0 ht h
    have : √t / Kr ≤ √2 / Kr := div_le_div_of_nonneg_right (sqrt_le_sqrt h) hK0.le
    linarith
  · have := field_bound_large h hK
    have : 0 ≤ √2 / Kr := by positivity
    linarith

/-! ### The normalised counting measure -/

/-- `σ = K⁻¹ ∑ δ_{t_i}`. -/
noncomputable def cnt {h : ℕ} (Kr : ℝ) (t : Fin h → ℝ) : Measure ℝ :=
  ENNReal.ofReal Kr⁻¹ • ∑ i, Measure.dirac (t i)

section cnt

variable {h : ℕ} {Kr : ℝ} {t : Fin h → ℝ}

theorem cnt_univ (hK : 0 < Kr) : cnt Kr t univ = ENNReal.ofReal (h / Kr) := by
  rw [cnt, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv, mul_comm]

instance : IsFiniteMeasure (cnt Kr t) := by
  constructor
  rw [cnt, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top _)

theorem cnt_real_univ (hK : 0 < Kr) : (cnt Kr t).real univ = h / Kr := by
  rw [measureReal_def, cnt_univ hK, ENNReal.toReal_ofReal (by positivity)]

theorem integral_cnt (hK : 0 < Kr) (f : ℝ → ℝ) : ∫ x, f x ∂cnt Kr t = Kr⁻¹ * ∑ i, f (t i) := by
  rw [cnt, integral_smul_measure, integral_finsetSum_measure fun i _ =>
    integrable_dirac enorm_lt_top, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  simp only [integral_dirac]

theorem ae_cnt : ∀ᵐ x ∂cnt Kr t, |x| ≤ ∑ i, |t i| + 2 := by
  refine Measure.ae_smul_measure ?_ _
  rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hs : MeasurableSet {a : ℝ | ¬|a| ≤ ∑ i, |t i| + 2} :=
    (measurableSet_le continuous_abs.measurable measurable_const).compl
  rw [Measure.dirac_apply' _ hs, indicator_of_notMem]
  simp only [mem_ofPred_eq, not_not]
  have := Finset.single_le_sum (f := fun i => |t i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

end cnt

/-! ### Sums over pairs -/

theorem sum_sum_symm {h : ℕ} (f : Fin h → Fin h → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have hsplit : ∀ i, ∑ j, f i j = ∑ j, (if j < i then f i j else 0) + f i i +
      ∑ j ∈ Finset.Ioi i, f i j := by
    intro i
    have hIoi : ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
      rw [← Finset.sum_filter]; congr 1; ext j; simp
    have hdiag : ∑ j, (if j = i then f i j else 0) = f i i := by simp
    rw [hIoi, ← hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp [hji, hji.ne, not_lt.2 hji.le]
    · simp
    · simp [hij, hij.ne', not_lt.2 hij.le]
  have hlow : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (by ext i; simp) fun i _ => hf i j
  simp_rw [hsplit, Finset.sum_add_distrib, hlow]
  ring

/-! ### The energy bound -/

/-- (6.9), asymptotic form. -/
theorem energy_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t : Fin (dim n) → ℝ, (∀ i, 0 < t i) → Function.Injective t →
      2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t j - t i| - K n * ∑ i, Vfield (t i) +
        ∑ i, √(t i) ≤ ((lambda : ℝ) * M0 - Irho + ε) * (K n : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hreg⟩ := exists_regularize_rho (half_pos hε)
  set C := √2 + |log δ| with hC
  have hC0 : 0 ≤ C := by positivity
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈C / ε⌉₊] with n hn hnC t htpos htinj
  set Kr : ℝ := (K n : ℝ) with hKr
  have hKn : Kr = 40 * n := by rw [hKr]; simp [K]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK2 : 2 ≤ Kr := by rw [hKn]; linarith
  have hK0 : 0 < Kr := by linarith
  have hh : (dim n : ℝ) = 37 / 40 * Kr := by rw [hKn]; simp [dim]; ring
  -- the measures
  have h1 : ∀ᵐ x ∂cnt Kr t, |x| ≤ ∑ i, |t i| + 2 := ae_cnt
  have h2 : ∀ᵐ x ∂rho, |x| ≤ ∑ i, |t i| + 2 := ae_rho_abs.mono fun x hx => by
    have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hmass : (cnt Kr t).real univ = rho.real univ := by
    rw [cnt_real_univ hK0, rho_real_univ, hh]; field_simp
  have key := logEnergy_nonpos hδ h1 h2 hmass
  -- the four energies
  set A := ∑ i, ∑ j, log ((t i - t j) ^ 2 + δ ^ 2) with hA
  set B := ∑ i, ∫ u, log ((t i - u) ^ 2 + δ ^ 2) ∂rho with hB
  have e11 : logEnergy δ (cnt Kr t) (cnt Kr t) = Kr⁻¹ * (Kr⁻¹ * A) := by
    rw [logEnergy_eq_iter hδ h1 h1, integral_cnt hK0]
    simp_rw [integral_cnt hK0]
    rw [← Finset.mul_sum]
  have e12 : logEnergy δ (cnt Kr t) rho = Kr⁻¹ * B := by
    rw [logEnergy_eq_iter hδ h1 h2, integral_cnt hK0]
  have e21 : logEnergy δ rho (cnt Kr t) = logEnergy δ (cnt Kr t) rho := logEnergy_comm δ
  have e22 := two_Irho_le_logEnergy hδ
  rw [e21, e11, e12] at key
  -- the diagonal and the pairs
  set S := ∑ i, ∑ j ∈ Finset.Ioi i, log |t j - t i| with hS
  have b11 : dim n * log (δ ^ 2) + 4 * S ≤ A := by
    rw [hA, sum_sum_symm _ fun i j => by ring_nf]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ∀ i, ∀ j ∈ Finset.Ioi i, 2 * log |t j - t i| ≤ log ((t i - t j) ^ 2 + δ ^ 2) := by
      intro i j hj
      have hne : t j - t i ≠ 0 := sub_ne_zero.2 fun e => (Finset.mem_Ioi.1 hj).ne' (htinj e)
      rw [two_mul_log_abs]
      exact log_le_log (by positivity) (by nlinarith [sq_nonneg δ])
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => Finset.sum_le_sum (this i)
    simp only [← Finset.mul_sum] at this
    rw [hS]
    linarith
  have b12 : B ≤ ∑ i, (2 * Urho (t i)) + dim n * (ε / 2) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hreg (t i)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    exact this
  have b7 : ∑ i, (2 * Urho (t i)) ≤
      ∑ i, Vfield (t i) - Kr⁻¹ * ∑ i, √(t i) + dim n * M0 + dim n * √2 * Kr⁻¹ := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => two_Urho_le (htpos i) hK2
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, ← Finset.sum_mul] at this
    linarith
  -- the lower order terms
  have hlow : dim n * √2 - dim n * log δ ≤ ε / 2 * Kr ^ 2 := by
    have hCK : 2 * C ≤ ε * Kr := by
      have : C / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
      rw [div_le_iff₀ hε] at this
      rw [hKn]; nlinarith
    have : dim n * √2 - dim n * log δ ≤ dim n * C := by
      rw [hC]; nlinarith [neg_abs_le (log δ), (Nat.cast_nonneg (dim n) : (0 : ℝ) ≤ dim n)]
    rw [hh] at this ⊢
    nlinarith [mul_le_mul_of_nonneg_left hCK hK0.le]
  -- combine
  have hlogδ : log (δ ^ 2) = 2 * log δ := by rw [Real.log_pow]; push_cast; ring
  rw [hlogδ] at b11
  have key' := mul_le_mul_of_nonneg_left key (sq_nonneg Kr)
  rw [mul_zero] at key'
  have e1 : Kr ^ 2 * (Kr⁻¹ * (Kr⁻¹ * A) - Kr⁻¹ * B - Kr⁻¹ * B + logEnergy δ rho rho) =
      A - 2 * Kr * B + Kr ^ 2 * logEnergy δ rho rho := by
    field_simp
    ring
  rw [e1] at key'
  have hb7K := mul_le_mul_of_nonneg_left b7 hK0.le
  have e2 : Kr * (∑ i, Vfield (t i) - Kr⁻¹ * ∑ i, √(t i) + dim n * M0 + dim n * √2 * Kr⁻¹) =
      Kr * ∑ i, Vfield (t i) - ∑ i, √(t i) + dim n * Kr * M0 + dim n * √2 := by
    field_simp
  rw [e2] at hb7K
  have hKb12 := mul_le_mul_of_nonneg_left b12 hK0.le
  have hKe22 := mul_le_mul_of_nonneg_left e22 (sq_nonneg Kr)
  have hεK : 0 ≤ ε * Kr ^ 2 := by positivity
  rw [lambda_real, M0_real]
  rw [M0_real, hh] at hb7K
  rw [hh] at b11 hKb12 hlow
  linarith

end Zeta5
