/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Arcsine
import Zeta5.LogEnergy
import Zeta5.Regularize

/-!
# The comparison measure `ρ` of Lemma 6.1

`ρ = ∑_{j=1}^{16} c_j ω[a_j, b_j]` is a sum of sixteen arcsine measures on nested intervals
`0 < a₁₆ < ⋯ < a₁ < b₁ < ⋯ < b₁₆ < 2`, with the rational data of Table 1 (in units of `10⁻¹²`).
Its mass is `∑ c_j = 37/40 = λ`.

* `Zeta5.Urho`: its logarithmic potential, by (A.1).
* `Zeta5.Irho`: its energy (A.2), `I(ρ) = ∑_{j,k} c_j c_k log((b_m - a_m)/4)` with `m = max(j, k)`.
  We only need the lower bound `∫∫ log((x-y)² + δ²) dρ dρ ≥ 2 I(ρ)`, which follows from the
  nesting: the potential of the larger interval is constant on the smaller one.
-/

open Real MeasureTheory Set Filter

namespace Zeta5

/-! ### Table 1 -/

/-- Table 1: `10¹² a_j`. -/
def tabA : Fin 16 → ℕ := ![3906748086, 2312248264, 1402286665, 881725356, 578197906, 396324613,
  283911191, 212206188, 165097686, 133347132, 111522114, 96349355, 85815639, 78667711, 74129565,
  71741310]

/-- Table 1: `10¹² b_j`. -/
def tabB : Fin 16 → ℕ := ![8992695531, 15340997855, 25730180724, 41909578246, 65851089563,
  99481037884, 144325727458, 201105762729, 269345996903, 347089554156, 430806704415,
  515561896511, 595448778546, 664241383483, 716160577112, 746637295669]

/-- Table 1: `10¹² c_j`. -/
def tabC : Fin 16 → ℕ := ![10515596180, 29471737793, 42934365099, 58204231966, 69037621310,
  78873099189, 84856120711, 88396082127, 88303382125, 85472321255, 78899184238, 70353471918,
  58838976615, 44421321106, 30462865791, 5959622577]

theorem tab_nested : ∀ j k : Fin 16, j ≤ k → tabA k ≤ tabA j ∧ tabB j ≤ tabB k := by decide

theorem tabA_lt_tabB : ∀ j : Fin 16, tabA j < tabB j := by decide

theorem tabB_le : ∀ j : Fin 16, tabB j ≤ 2 * 10 ^ 12 := by decide

theorem tabC_pos : ∀ j : Fin 16, 0 < tabC j := by decide

theorem sum_tabC : ∑ j, tabC j = 925000000000 := by decide

/-- The centre `(a_j + b_j)/2`. -/
noncomputable def ctr (j : Fin 16) : ℝ := ((tabA j : ℝ) + tabB j) / 2 / 10 ^ 12

/-- The half-length `(b_j - a_j)/2`. -/
noncomputable def rad (j : Fin 16) : ℝ := ((tabB j : ℝ) - tabA j) / 2 / 10 ^ 12

/-- The weight `c_j`. -/
noncomputable def wgt (j : Fin 16) : ℝ := (tabC j : ℝ) / 10 ^ 12

theorem rad_pos (j : Fin 16) : 0 < rad j := by
  have : (tabA j : ℝ) < tabB j := by exact_mod_cast tabA_lt_tabB j
  unfold rad; apply div_pos (div_pos (by linarith) two_pos); positivity

theorem wgt_pos (j : Fin 16) : 0 < wgt j := by
  have : (0 : ℝ) < tabC j := by exact_mod_cast tabC_pos j
  unfold wgt; positivity

theorem sum_wgt : ∑ j, wgt j = 37 / 40 := by
  have : (∑ j, (tabC j : ℝ)) = 925000000000 := by exact_mod_cast sum_tabC
  simp only [wgt, ← Finset.sum_div, this]
  norm_num

theorem Icc_ctr_rad (j : Fin 16) :
    Icc (ctr j - rad j) (ctr j + rad j) =
      Icc ((tabA j : ℝ) / 10 ^ 12) ((tabB j : ℝ) / 10 ^ 12) := by
  congr 1 <;> · unfold ctr rad; ring

theorem Icc_ctr_rad_subset {j k : Fin 16} (hjk : j ≤ k) :
    Icc (ctr j - rad j) (ctr j + rad j) ⊆ Icc (ctr k - rad k) (ctr k + rad k) := by
  rw [Icc_ctr_rad, Icc_ctr_rad]
  obtain ⟨h1, h2⟩ := tab_nested j k hjk
  have h1' : (tabA k : ℝ) ≤ tabA j := by exact_mod_cast h1
  have h2' : (tabB j : ℝ) ≤ tabB k := by exact_mod_cast h2
  exact Icc_subset_Icc (by gcongr) (by gcongr)

theorem Icc_ctr_rad_subset_Icc (j : Fin 16) : Icc (ctr j - rad j) (ctr j + rad j) ⊆ Icc 0 2 := by
  rw [Icc_ctr_rad]
  have h : (tabB j : ℝ) ≤ 2 * 10 ^ 12 := by exact_mod_cast tabB_le j
  refine Icc_subset_Icc (by positivity) ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### The measure -/

/-- The arcsine measure `ω[a_j, b_j]`. -/
noncomputable def omega (j : Fin 16) : Measure ℝ := arcsine (ctr j) (rad j)

instance (j : Fin 16) : IsProbabilityMeasure (omega j) := by unfold omega; infer_instance

/-- The comparison measure `ρ = ∑ c_j ω[a_j, b_j]` of Lemma 6.1. -/
noncomputable def rho : Measure ℝ := ∑ j, ENNReal.ofReal (wgt j) • omega j

theorem ae_omega (j : Fin 16) : ∀ᵐ u ∂omega j, u ∈ Icc (ctr j - rad j) (ctr j + rad j) := by
  have := ae_arcsine_mem (ctr j) (rad j)
  rwa [abs_of_pos (rad_pos j)] at this

theorem ae_omega_abs (j : Fin 16) : ∀ᵐ u ∂omega j, |u| ≤ 2 := by
  filter_upwards [ae_omega j] with u hu
  have := Icc_ctr_rad_subset_Icc j hu
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem ae_rho_of {p : ℝ → Prop} (h : ∀ j, ∀ᵐ u ∂omega j, p u) : ∀ᵐ u ∂rho, p u := by
  rw [ae_iff, rho, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [Measure.smul_apply, ae_iff.1 (h j), smul_zero]

theorem ae_rho : ∀ᵐ u ∂rho, u ∈ Icc (0 : ℝ) 2 :=
  ae_rho_of fun j => (ae_omega j).mono fun _ hu => Icc_ctr_rad_subset_Icc j hu

theorem ae_rho_abs : ∀ᵐ u ∂rho, |u| ≤ 2 := ae_rho_of ae_omega_abs

theorem rho_singleton (t : ℝ) : rho {t} = 0 := by
  rw [rho, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun j _ => by
    rw [Measure.smul_apply, omega, arcsine_singleton _ (rad_pos j).ne', smul_zero]

theorem rho_univ : rho univ = ENNReal.ofReal (37 / 40) := by
  rw [rho, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, omega, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => (wgt_pos j).le, sum_wgt]

instance : IsFiniteMeasure rho := ⟨by rw [rho_univ]; exact ENNReal.ofReal_lt_top⟩

theorem rho_real_univ : rho.real univ = 37 / 40 := by
  rw [measureReal_def, rho_univ, ENNReal.toReal_ofReal (by norm_num)]

theorem integrable_rho_of {f : ℝ → ℝ} (hf : ∀ j, Integrable f (omega j)) : Integrable f rho :=
  (integrable_finsetSum_measure).2 fun j _ => (hf j).smul_measure ENNReal.ofReal_ne_top

theorem integral_rho {f : ℝ → ℝ} (hf : ∀ j, Integrable f (omega j)) :
    ∫ u, f u ∂rho = ∑ j, wgt j * ∫ u, f u ∂omega j := by
  rw [rho, integral_finsetSum_measure fun j _ => (hf j).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (wgt_pos j).le, smul_eq_mul]

/-! ### The potential -/

/-- The logarithmic potential `U^ρ(t) = ∑ c_j U^{ω_j}(t)`, by (A.1). -/
noncomputable def Urho (t : ℝ) : ℝ := ∑ j, wgt j * arcsinePot (ctr j) (rad j) t

theorem integrable_log_rho (t : ℝ) : Integrable (fun u => log |t - u|) rho :=
  integrable_rho_of fun j => integrable_log_arcsine _ (rad_pos j) t

theorem integral_log_rho (t : ℝ) : ∫ u, log |t - u| ∂rho = Urho t := by
  rw [integral_rho fun j => integrable_log_arcsine _ (rad_pos j) t]
  exact Finset.sum_congr rfl fun j _ => by rw [omega, integral_log_arcsine _ (rad_pos j)]

theorem continuous_Urho : Continuous Urho :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_arcsinePot _ _)

/-- The regularised potentials of `ρ` converge uniformly. -/
theorem exists_regularize_rho {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ t, ∫ u, log ((t - u) ^ 2 + δ ^ 2) ∂rho ≤ 2 * Urho t + ε := by
  obtain ⟨δ, hδ, h⟩ := exists_regularize ae_rho_abs rho_singleton integrable_log_rho
    (by simp_rw [integral_log_rho]; exact continuous_Urho) hε
  exact ⟨δ, hδ, fun t => by rw [← integral_log_rho]; exact h t⟩

/-! ### The energy -/

/-- The energy (A.2) of `ρ`: `I(ρ) = ∑_{j,k} c_j c_k log((b_m - a_m)/4)`, `m = max(j, k)`. -/
noncomputable def Irho : ℝ := ∑ j, ∑ k, wgt j * wgt k * log (rad (max j k) / 2)

/-- If `μ` is a probability measure on `[m - R, m + R]`, its regularised mutual energy with the
arcsine measure is at least `2 log(R/2)`: the potential of the arcsine measure is constant on its
interval. -/
theorem logEnergy_arcsine_ge {μ : Measure ℝ} [IsProbabilityMeasure μ] {m R δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (m - R) (m + R)) :
    2 * log (R / 2) ≤ logEnergy δ μ (arcsine m R) := by
  have hμT : ∀ᵐ x ∂μ, |x| ≤ |m| + R := hμ.mono fun x hx => by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, neg_abs_le m, le_abs_self m]
  have hνT : ∀ᵐ y ∂arcsine m R, |y| ≤ |m| + R := (ae_arcsine_mem m R).mono fun y hy => by
    rw [abs_of_pos hR] at hy
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2, neg_abs_le m, le_abs_self m]
  rw [logEnergy_eq_iter hδ hμT hνT]
  calc 2 * log (R / 2) = ∫ _, 2 * log (R / 2) ∂μ := by simp
    _ ≤ _ := by
      refine integral_mono_ae (integrable_const _) (integrable_logKernel_iter hδ hμT hνT) ?_
      filter_upwards [hμ] with x hx
      rw [← arcsinePot_of_mem m hR hx, ← integral_log_arcsine m hR x, ← integral_const_mul]
      refine integral_mono_ae ((integrable_log_arcsine m hR x).const_mul 2)
        (integrable_log_sq_add hνT x hδ) ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (arcsine_singleton m hR.ne' x)] with y hy
      have hne : x - y ≠ 0 := sub_ne_zero.2 fun h => hy (h ▸ rfl)
      rw [two_mul_log_abs]
      exact log_le_log (by positivity) (by nlinarith [sq_nonneg δ])

theorem logEnergy_omega_ge {δ : ℝ} (hδ : 0 < δ) (j k : Fin 16) :
    2 * log (rad (max j k) / 2) ≤ logEnergy δ (omega j) (omega k) := by
  rcases le_total j k with h | h
  · rw [max_eq_right h, omega, omega]
    exact logEnergy_arcsine_ge (rad_pos k) hδ ((ae_omega j).mono fun _ hx =>
      Icc_ctr_rad_subset h hx)
  · rw [max_eq_left h, logEnergy_comm, omega, omega]
    exact logEnergy_arcsine_ge (rad_pos j) hδ ((ae_omega k).mono fun _ hx =>
      Icc_ctr_rad_subset h hx)

theorem logEnergy_rho_eq {δ : ℝ} (hδ : 0 < δ) :
    logEnergy δ rho rho = ∑ j, ∑ k, wgt j * wgt k * logEnergy δ (omega j) (omega k) := by
  rw [logEnergy_eq_iter hδ ae_rho_abs ae_rho_abs,
    integral_rho fun j => integrable_logKernel_iter hδ (ae_omega_abs j) ae_rho_abs]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hinner : ∀ x, ∫ y, log ((x - y) ^ 2 + δ ^ 2) ∂rho =
      ∑ k, wgt k * ∫ y, log ((x - y) ^ 2 + δ ^ 2) ∂omega k := fun x =>
    integral_rho fun k => integrable_log_sq_add (ae_omega_abs k) x hδ
  simp_rw [hinner]
  rw [integral_finsetSum _ fun k _ =>
    (integrable_logKernel_iter hδ (ae_omega_abs j) (ae_omega_abs k)).const_mul _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, logEnergy_eq_iter hδ (ae_omega_abs j) (ae_omega_abs k)]
  ring

/-- `∫∫ log((x-y)² + δ²) dρ dρ ≥ 2 I(ρ)`. -/
theorem two_Irho_le_logEnergy {δ : ℝ} (hδ : 0 < δ) : 2 * Irho ≤ logEnergy δ rho rho := by
  rw [logEnergy_rho_eq hδ, Irho, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := logEnergy_omega_ge hδ j k
  have hjk : 0 ≤ wgt j * wgt k := (mul_pos (wgt_pos j) (wgt_pos k)).le
  nlinarith

end Zeta5
