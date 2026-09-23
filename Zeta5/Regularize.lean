/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.Dini

/-!
# Regularising the logarithmic potential

For a finite measure `μ` on `ℝ` with bounded support, no atoms, and a continuous logarithmic
potential `U(t) = ∫ log|t - u| dμ(u)`, the regularised potentials
`∫ log((t - u)² + δ²) dμ(u)` decrease to `2U(t)` as `δ ↓ 0`, uniformly in `t ∈ ℝ`. On a compact
interval this is Dini's theorem; far from the support the difference is at most `δ² μ(ℝ)`.

This replaces the estimate `∫ U_ρ dω_i - U_ρ(t_i) ≤ 60 √ε` of §6.1 of the paper: we only need
that the error is `o(1)`, uniformly in the configuration.
-/

open Real MeasureTheory Set Filter Topology

namespace Zeta5

theorem two_mul_log_abs (x : ℝ) : 2 * log |x| = log (x ^ 2) := by
  rw [← sq_abs x, Real.log_pow]; push_cast; ring

theorem log_sq_add_sub_le {x δ : ℝ} (hx : 1 ≤ |x|) :
    log (x ^ 2 + δ ^ 2) - 2 * log |x| ≤ δ ^ 2 := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
  rw [two_mul_log_abs, ← log_div (by positivity) (by positivity)]
  refine (log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [div_sub_one (by positivity), add_sub_cancel_left, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg δ]

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem integrable_log_sq_add {T : ℝ} (hsupp : ∀ᵐ u ∂μ, |u| ≤ T) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u => log ((t - u) ^ 2 + δ ^ 2)) μ := by
  refine (integrable_const (|log (δ ^ 2)| + |log ((|t| + T) ^ 2 + δ ^ 2)|)).mono'
    (measurable_log.comp (by fun_prop : Measurable fun u : ℝ =>
      (t - u) ^ 2 + δ ^ 2)).aestronglyMeasurable ?_
  filter_upwards [hsupp] with u hu
  have h1 : log (δ ^ 2) ≤ log ((t - u) ^ 2 + δ ^ 2) :=
    log_le_log (by positivity) (by nlinarith [sq_nonneg (t - u)])
  have h2 : log ((t - u) ^ 2 + δ ^ 2) ≤ log ((|t| + T) ^ 2 + δ ^ 2) := by
    refine log_le_log (by positivity) ?_
    have : |t - u| ≤ |t| + T := (abs_sub _ _).trans (by linarith)
    nlinarith [sq_abs (t - u), abs_nonneg (t - u)]
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (log (δ ^ 2)), le_abs_self (log ((|t| + T) ^ 2 + δ ^ 2)),
    abs_nonneg (log (δ ^ 2)), abs_nonneg (log ((|t| + T) ^ 2 + δ ^ 2))]

/-- The regularised potentials converge uniformly to `2U`. -/
theorem exists_regularize {T : ℝ} (hsupp : ∀ᵐ u ∂μ, |u| ≤ T) (hatom : ∀ t, μ {t} = 0)
    (hint : ∀ t, Integrable (fun u => log |t - u|) μ)
    (hcont : Continuous fun t => ∫ u, log |t - u| ∂μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ t, ∫ u, log ((t - u) ^ 2 + δ ^ 2) ∂μ ≤ 2 * ∫ u, log |t - u| ∂μ + ε := by
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδn
  have hδpos : ∀ n, 0 < δn n := fun n => by positivity
  have hδle : ∀ n, δn n ≤ 1 := fun n => by
    rw [hδn, div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have hδanti : Antitone δn := fun n m hnm => by
    simp only [hδn]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hδlim : Tendsto δn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → ℝ → ℝ := fun n t => ∫ u, log ((t - u) ^ 2 + δn n ^ 2) ∂μ with hF
  set f : ℝ → ℝ := fun t => 2 * ∫ u, log |t - u| ∂μ with hf
  set K := Icc (-(T + 1)) (T + 1) with hK
  -- continuity of the regularised potentials on `K`
  have hF_cont : ∀ n, ContinuousOn (F n) K := by
    intro n
    set B := |log (δn n ^ 2)| + |log ((2 * T + 1) ^ 2 + δn n ^ 2)|
    refine continuousOn_of_dominated (bound := fun _ => B) (fun t _ => (measurable_log.comp
      (by fun_prop : Measurable fun u : ℝ => (t - u) ^ 2 + δn n ^ 2)).aestronglyMeasurable)
      (fun t ht => ?_) (integrable_const _) (ae_of_all _ fun u => ?_)
    · filter_upwards [hsupp] with u hu
      have h1 : log (δn n ^ 2) ≤ log ((t - u) ^ 2 + δn n ^ 2) :=
        log_le_log (by have := hδpos n; positivity) (by nlinarith [sq_nonneg (t - u)])
      have h2 : log ((t - u) ^ 2 + δn n ^ 2) ≤ log ((2 * T + 1) ^ 2 + δn n ^ 2) := by
        refine log_le_log (by have := hδpos n; positivity) ?_
        have : |t - u| ≤ 2 * T + 1 :=
          (abs_sub _ _).trans (by linarith [abs_le.2 ⟨ht.1, ht.2⟩])
        nlinarith [sq_abs (t - u), abs_nonneg (t - u)]
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [neg_abs_le (log (δn n ^ 2)),
        le_abs_self (log ((2 * T + 1) ^ 2 + δn n ^ 2)), abs_nonneg (log (δn n ^ 2)),
        abs_nonneg (log ((2 * T + 1) ^ 2 + δn n ^ 2))]
    · exact (Continuous.log (by fun_prop) fun t => by
        have := hδpos n; positivity).continuousOn
  -- monotonicity in `n`
  have hF_anti : ∀ t ∈ K, Antitone fun n => F n t := by
    intro t _ n m hnm
    refine integral_mono (integrable_log_sq_add hsupp t (hδpos m))
      (integrable_log_sq_add hsupp t (hδpos n)) fun u => ?_
    refine log_le_log (by have := hδpos m; positivity) ?_
    have := hδanti hnm
    have := hδpos m
    nlinarith
  -- pointwise convergence, by dominated convergence
  have h_tendsto : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t)) := by
    intro t
    set C := log ((|t| + T) ^ 2 + 1)
    have hlim : f t = ∫ u, 2 * log |t - u| ∂μ := by rw [hf, integral_const_mul]
    rw [hlim]
    refine tendsto_integral_of_dominated_convergence (fun u => 2 * abs (log |t - u|) + |C|)
      (fun n => (measurable_log.comp (by fun_prop : Measurable fun u : ℝ =>
        (t - u) ^ 2 + δn n ^ 2)).aestronglyMeasurable)
      (((hint t).norm.const_mul 2).add (integrable_const _))
      (fun n => ?_) ?_
    · filter_upwards [hsupp, measure_eq_zero_iff_ae_notMem.1 (hatom t)] with u hu hut
      have hne : t - u ≠ 0 := sub_ne_zero.2 fun h => hut (h ▸ rfl)
      have h1 : 2 * log |t - u| ≤ log ((t - u) ^ 2 + δn n ^ 2) := by
        rw [two_mul_log_abs]
        exact log_le_log (by positivity) (by nlinarith [sq_nonneg (δn n)])
      have h2 : log ((t - u) ^ 2 + δn n ^ 2) ≤ C := by
        refine log_le_log (by positivity) ?_
        have : |t - u| ≤ |t| + T := (abs_sub _ _).trans (by linarith)
        have := hδle n
        have := hδpos n
        nlinarith [sq_abs (t - u), abs_nonneg (t - u)]
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [abs_nonneg (log |t - u|), neg_abs_le (log |t - u|),
        le_abs_self C, abs_nonneg C]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hatom t)] with u hut
      have hne : t - u ≠ 0 := sub_ne_zero.2 fun h => hut (h ▸ rfl)
      rw [two_mul_log_abs]
      have hpos : 0 < (t - u) ^ 2 + 0 ^ 2 := by positivity
      have := ((continuousAt_log hpos.ne').tendsto.comp
        ((continuous_const.add (continuous_pow 2)).tendsto 0 |>.comp hδlim))
      have h0 : (t - u) ^ 2 + (0 : ℝ) ^ 2 = (t - u) ^ 2 := by ring
      rw [h0] at this
      exact this
  have hunif := Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc hF_cont hF_anti
    ((continuous_const.mul hcont).continuousOn) fun t _ => h_tendsto t
  -- far from the support
  have hsmall : Tendsto (fun n => δn n ^ 2 * μ.real univ) atTop (𝓝 0) := by
    simpa using (hδlim.pow 2).mul_const (μ.real univ)
  obtain ⟨n, hn1, hn2⟩ := ((Metric.tendstoUniformlyOn_iff.1 hunif ε hε).and
    (hsmall.eventually (gt_mem_nhds hε))).exists
  refine ⟨δn n, hδpos n, fun t => ?_⟩
  by_cases htK : t ∈ K
  · have := hn1 t htK
    rw [Real.dist_eq, abs_lt] at this
    simp only [hF, Pi.mul_apply] at this
    linarith
  · have ht : T + 1 < |t| := by
      simp only [hK, mem_Icc, not_and_or, not_le] at htK
      rcases htK with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
      · exact h.trans_le (le_abs_self t)
    have hle : ∫ u, log ((t - u) ^ 2 + δn n ^ 2) ∂μ - ∫ u, 2 * log |t - u| ∂μ ≤
        δn n ^ 2 * μ.real univ := by
      rw [← integral_sub (integrable_log_sq_add hsupp t (hδpos n)) ((hint t).const_mul 2)]
      calc ∫ u, (log ((t - u) ^ 2 + δn n ^ 2) - 2 * log |t - u|) ∂μ
          ≤ ∫ _, δn n ^ 2 ∂μ := by
            refine integral_mono_ae ((integrable_log_sq_add hsupp t (hδpos n)).sub
              ((hint t).const_mul 2)) (integrable_const _) ?_
            filter_upwards [hsupp] with u hu
            exact log_sq_add_sub_le (by
              have := abs_sub_abs_le_abs_sub t u
              linarith)
        _ = δn n ^ 2 * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
    rw [integral_const_mul] at hle
    linarith

end Zeta5
