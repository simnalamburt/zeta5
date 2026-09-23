/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.LinearAlgebra.Vandermonde
import Zeta5.Andreief
import Zeta5.Energy
import Zeta5.Gram

/-!
# The size of `Δ_K(ζ(5))` (6.14)

By Andréief's identity (6.10), `h! Δ_K(ζ(5)) = ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏ ρ(y_k) dy`
with `ρ = D_N(y²)⁶ / D_K(y²) · w(y)`. Substituting `t_k = (y_k/K)²`, the Riemann sum bounds (6.12),
the weight bound (6.11) and the energy bound (6.9) give the pointwise bound
`∏_{i<j} (y_i² - y_j²)² ∏ ρ(y_k) ≤ exp(B) ∏ (1 + y_k)^17 e^{-y_k/K}` with
`B = 2h(h + 6N - K) log K + (λM₀ - I(ρ) + ε) K² + O(K log K)`, and integrating gives (6.14).
-/

open Real MeasureTheory Set Polynomial Matrix Filter

namespace Zeta5

/-! ### The Vandermonde factor -/

/-- The functions `y ↦ y^{2i}` of the Gram matrix `G_K(ζ(5))`. -/
def evenPow (n : ℕ) (i : Fin (dim n)) (y : ℝ) : ℝ := y ^ (2 * (i : ℕ))

theorem vdet_evenPow (n : ℕ) (y : Fin (dim n) → ℝ) :
    vdet (evenPow n) y = ∏ i, ∏ j ∈ Finset.Ioi i, (y j ^ 2 - y i ^ 2) := by
  rw [vdet, ← det_vandermonde, ← det_transpose]
  congr 1
  ext i k
  simp [evenPow, vandermonde_apply, pow_mul]

/-! ### The weight -/

theorem aeval_D_sq (m : ℕ) (y : ℝ) :
    aeval (y ^ 2) (D m) = ∏ j ∈ Finset.Icc 1 m, (y ^ 2 + (j : ℝ) ^ 2) := by
  simp [D, poleDen, map_prod]

theorem log_aeval_D_sq {m : ℕ} {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    Real.log (aeval (y ^ 2) (D m)) =
      2 * m * Real.log K + ∑ j ∈ Finset.Icc 1 m, Real.log ((y / K) ^ 2 + (j / K) ^ 2) := by
  rw [aeval_D_sq, Real.log_prod (fun j _ => by positivity)]
  have : ∀ j ∈ Finset.Icc 1 m, Real.log (y ^ 2 + (j : ℝ) ^ 2) =
      2 * Real.log K + Real.log ((y / K) ^ 2 + (j / K) ^ 2) := by
    intro j _
    rw [show y ^ 2 + (j : ℝ) ^ 2 = K ^ 2 * ((y / K) ^ 2 + (j / K) ^ 2) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
  simp only [add_tsub_cancel_right, nsmul_eq_mul]
  ring

/-- The constant in the pointwise bound for `log ρ`. -/
noncomputable def C1 : ℝ := 12 + Real.log (32 * π ^ 4)

/-- The weight of the Gram matrix in the scaled variable `t = (y/K)²`, via (6.11) and (6.12). -/
theorem log_gramWeight_le {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    Real.log (gramWeight n y) ≤ (12 * N n - 2 * K n) * Real.log (K n) -
      K n * Vfield ((y / K n) ^ 2) + 17 * Real.log (1 + y) + 12 * Real.log (K n) + C1 := by
  set Kr : ℝ := (K n : ℝ) with hKr
  have hK1 : (40 : ℝ) ≤ Kr := by
    rw [hKr]; simp only [K]; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : 0 < Kr := by linarith
  set t := (y / Kr) ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hDN := aeval_poleDen_pos (Finset.Icc 1 (N n)) (pow_pos hy 2)
  have hDK := aeval_poleDen_pos (Finset.Icc 1 (K n)) (pow_pos hy 2)
  have hw := wt_pos hy
  rw [gramWeight, Real.log_mul (by simp only [D]; positivity) hw.ne',
    Real.log_div (by simp only [D]; positivity) (by simp only [D]; positivity), Real.log_pow,
    log_aeval_D_sq hK0 hy, log_aeval_D_sq hK0 hy]
  -- the Riemann sums
  have hsN := sum_log_le (t := t) (K := Kr) ht0 (by linarith) (N n)
  have hsK := sum_log_ge (t := t) (K := Kr) ht0 hK0 (K n)
  have hNK : (N n : ℝ) / Kr = alpha := by
    rw [hKr]; simp only [N, K, alpha]; push_cast
    have : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have hKK : ((K n : ℕ) : ℝ) / Kr = 1 := div_self hK0.ne'
  rw [hNK] at hsN
  rw [hKK] at hsK
  -- the weight
  have hwl : Real.log (wt y) ≤ Real.log (32 * π ^ 4) + 5 * Real.log (1 + y) - 2 * π * y := by
    have := Real.log_le_log hw (wt_le hy)
    rw [Real.log_mul (by positivity) (exp_pos _).ne', Real.log_mul (by positivity)
      (by positivity), Real.log_exp, Real.log_pow] at this
    push_cast at this
    linarith
  -- `t + ((N+1)/K)² ≤ (1 + y)²`
  have hN1 : ((N n : ℝ) + 1) / Kr ≤ 1 := by
    rw [div_le_one hK0, hKr]; simp only [N, K]; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have htle : t + (((N n : ℝ) + 1) / Kr) ^ 2 ≤ (1 + y) ^ 2 := by
    have h1 : t ≤ y ^ 2 := by
      rw [ht, div_pow]
      exact div_le_self (sq_nonneg y) (by nlinarith)
    have h2 : (((N n : ℝ) + 1) / Kr) ^ 2 ≤ 1 := by
      have : 0 ≤ ((N n : ℝ) + 1) / Kr := by positivity
      nlinarith
    nlinarith
  have hlog1 : Real.log (t + (((N n : ℝ) + 1) / Kr) ^ 2) ≤ 2 * Real.log (1 + y) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
    exact Real.log_le_log (by positivity) htle
  -- `K · 2π √t = 2π y`
  have hsqrt : √t = y / Kr := by rw [ht, Real.sqrt_sq (by positivity)]
  have hV : Kr * Vfield t = 2 * π * y + Kr * Jlog t 1 - 6 * (Kr * Jlog t alpha) := by
    rw [Vfield, hsqrt]; field_simp
  rw [hV, C1]
  push_cast at hsN ⊢
  nlinarith

/-! ### The Vandermonde factor in the scaled variables -/

theorem card_pairs_le (h : ℕ) : (∑ i : Fin h, (Finset.Ioi i).card) * 2 ≤ h * h := by
  have : ∑ i : Fin h, (Finset.Ioi i).card = ∑ i ∈ Finset.range h, i := by
    simp only [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i), Finset.sum_range_reflect (fun i => i)]
  rw [this, Finset.sum_range_id_mul_two]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem sq_sub_sq_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : a ^ 2 - b ^ 2 ≠ 0 :=
  sub_ne_zero.2 fun h => hab ((sq_eq_sq₀ ha.le hb.le).1 h)

theorem log_vdet_evenPow {n : ℕ} {Kr : ℝ} (hK : 0 < Kr) {y : Fin (dim n) → ℝ}
    (hy : ∀ k, 0 < y k) (hinj : Function.Injective y) :
    Real.log (vdet (evenPow n) y) = 2 * Real.log Kr * ∑ i : Fin (dim n), ((Finset.Ioi i).card : ℝ) +
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |(y j / Kr) ^ 2 - (y i / Kr) ^ 2| := by
  have hne : ∀ i : Fin (dim n), ∀ j ∈ Finset.Ioi i, y j ^ 2 - y i ^ 2 ≠ 0 := fun i j hj =>
    sq_sub_sq_ne_zero (hy j) (hy i) fun h => (Finset.mem_Ioi.1 hj).ne' (hinj h)
  rw [vdet_evenPow, Real.log_prod fun i _ => Finset.prod_ne_zero_iff.2 (hne i), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_prod (hne i), Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd : (y j / Kr) ^ 2 - (y i / Kr) ^ 2 ≠ 0 := by
    intro h
    apply hne i j hj
    rw [show y j ^ 2 - y i ^ 2 = Kr ^ 2 * ((y j / Kr) ^ 2 - (y i / Kr) ^ 2) by field_simp, h,
      mul_zero]
  rw [show y j ^ 2 - y i ^ 2 = Kr ^ 2 * ((y j / Kr) ^ 2 - (y i / Kr) ^ 2) by field_simp,
    Real.log_mul (by positivity) hd, Real.log_pow, Real.log_abs]
  push_cast
  ring

/-! ### The majorant -/

theorem one_add_pow_le {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ 17 ≤ 2 ^ 17 * (1 + y ^ 17) := by
  have h17 := pow_nonneg hy 17
  rcases le_total y 1 with h | h
  · calc (1 + y) ^ 17 ≤ 2 ^ 17 := pow_le_pow_left₀ (by linarith) (by linarith) 17
      _ ≤ 2 ^ 17 * (1 + y ^ 17) := by nlinarith
  · calc (1 + y) ^ 17 ≤ (2 * y) ^ 17 := pow_le_pow_left₀ (by linarith) (by linarith) 17
      _ = 2 ^ 17 * y ^ 17 := mul_pow _ _ _
      _ ≤ 2 ^ 17 * (1 + y ^ 17) := by nlinarith

/-- The majorant `2^17 (1 + y^17) e^{-y/K}` of `(1 + y)^17 e^{-y/K}` on `(0, ∞)`. -/
noncomputable def psi (n : ℕ) : ℝ → ℝ :=
  (Ioi 0).indicator fun y =>
    2 ^ 17 * (y ^ 0 * exp (-((K n : ℝ)⁻¹ * y)) + y ^ 17 * exp (-((K n : ℝ)⁻¹ * y)))

theorem K_pos {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < K n := by
  simp only [K]; push_cast
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem psi_pos {n : ℕ} {y : ℝ} (hy : 0 < y) : 0 < psi n y := by
  rw [psi, indicator_of_mem (mem_Ioi.2 hy)]
  exact mul_pos (by norm_num) (add_pos (by rw [pow_zero, one_mul]; exact exp_pos _)
    (mul_pos (pow_pos hy 17) (exp_pos _)))

theorem psi_nonneg (n : ℕ) (y : ℝ) : 0 ≤ psi n y := by
  by_cases hy : 0 < y
  · exact (psi_pos hy).le
  · rw [psi, indicator_of_notMem (by simpa using hy)]

theorem integrable_psi {n : ℕ} (hn : 1 ≤ n) : Integrable (psi n) := by
  have hc : 0 < (K n : ℝ)⁻¹ := inv_pos.2 (K_pos hn)
  rw [psi, integrable_indicator_iff measurableSet_Ioi]
  exact ((integrableOn_pow_mul_exp 0 hc).add (integrableOn_pow_mul_exp 17 hc)).const_mul _

theorem integral_psi {n : ℕ} (hn : 1 ≤ n) :
    ∫ y, psi n y = 2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18) := by
  have hc : 0 < (K n : ℝ)⁻¹ := inv_pos.2 (K_pos hn)
  rw [psi, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_add (integrableOn_pow_mul_exp 0 hc) (integrableOn_pow_mul_exp 17 hc),
    integral_pow_mul_exp 0 hc, integral_pow_mul_exp 17 hc]
  simp

theorem log_le_log_psi (n : ℕ) {y : ℝ} (hy : 0 < y) :
    17 * Real.log (1 + y) - y / K n ≤ Real.log (psi n y) := by
  have h1y : 0 < 1 + y := by linarith
  have hle : (1 + y) ^ 17 * exp (-((K n : ℝ)⁻¹ * y)) ≤ psi n y := by
    rw [psi, indicator_of_mem (mem_Ioi.2 hy)]
    calc (1 + y) ^ 17 * exp (-((K n : ℝ)⁻¹ * y))
        ≤ 2 ^ 17 * (1 + y ^ 17) * exp (-((K n : ℝ)⁻¹ * y)) :=
          mul_le_mul_of_nonneg_right (one_add_pow_le hy.le) (exp_pos _).le
      _ = _ := by ring
  have := Real.log_le_log (mul_pos (pow_pos h1y 17) (exp_pos _)) hle
  rw [Real.log_mul (pow_pos h1y 17).ne' (exp_pos _).ne', Real.log_pow, Real.log_exp] at this
  rw [div_eq_inv_mul]
  push_cast at this
  linarith

/-! ### The pointwise bound -/

/-- The exponent `B` of the pointwise bound. -/
noncomputable def Bexp (n : ℕ) (E : ℝ) : ℝ :=
  2 * dim n * ((dim n : ℝ) + 6 * N n - K n) * Real.log (K n) + 12 * dim n * Real.log (K n) +
    dim n * C1 + E * (K n : ℝ) ^ 2

/-- The energy bound (6.9) at a fixed `n`, with constant `E`. -/
def EnergyLe (n : ℕ) (E : ℝ) : Prop :=
  ∀ t : Fin (dim n) → ℝ, (∀ i, 0 < t i) → Function.Injective t →
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t j - t i| - K n * ∑ i, Vfield (t i) +
      ∑ i, √(t i) ≤ E * (K n : ℝ) ^ 2

theorem integrand_le {n : ℕ} (hn : 1 ≤ n) {E : ℝ} (hE : EnergyLe n E) (y : Fin (dim n) → ℝ) :
    vdet (evenPow n) y ^ 2 * ∏ k, (Ioi 0).indicator (gramWeight n) (y k) ≤
      exp (Bexp n E) * ∏ k, psi n (y k) := by
  have hR : 0 ≤ exp (Bexp n E) * ∏ k, psi n (y k) :=
    mul_nonneg (exp_pos _).le (Finset.prod_nonneg fun k _ => psi_nonneg n _)
  by_cases hpos : ∀ k, 0 < y k
  swap
  · simp only [not_forall, not_lt] at hpos
    obtain ⟨k, hk⟩ := hpos
    have h0 : (Ioi 0).indicator (gramWeight n) (y k) = 0 :=
      indicator_of_notMem (by simpa using hk) _
    rw [Finset.prod_eq_zero (Finset.mem_univ k) h0, mul_zero]
    exact hR
  by_cases hinj : Function.Injective y
  swap
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨a, b, hab, hne⟩ := hinj
    rw [vdet, det_zero_of_column_eq hne fun i => by simp [hab]]
    simpa using hR
  set Kr : ℝ := (K n : ℝ) with hKr
  have hK0 : 0 < Kr := K_pos hn
  have hK1 : 1 ≤ Kr := by
    rw [hKr]; simp only [K]; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlogK := Real.log_nonneg hK1
  rw [Finset.prod_congr rfl fun k _ => indicator_of_mem (mem_Ioi.2 (hpos k)) _]
  have hgw : ∀ k, 0 < gramWeight n (y k) := fun k => gramWeight_pos n (hpos k)
  have hpsi : ∀ k, 0 < psi n (y k) := fun k => psi_pos (hpos k)
  have hvdet : vdet (evenPow n) y ≠ 0 := by
    rw [vdet_evenPow]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj =>
      sq_sub_sq_ne_zero (hpos j) (hpos i) fun h => (Finset.mem_Ioi.1 hj).ne' (hinj h)
  rw [← Real.log_le_log_iff (mul_pos (pow_pos (abs_pos.2 hvdet) 2 |>.trans_eq (sq_abs _))
      (Finset.prod_pos fun k _ => hgw k))
      (mul_pos (exp_pos _) (Finset.prod_pos fun k _ => hpsi k)),
    Real.log_mul (pow_ne_zero 2 hvdet) (Finset.prod_ne_zero_iff.2 fun k _ => (hgw k).ne'),
    Real.log_mul (exp_pos _).ne' (Finset.prod_ne_zero_iff.2 fun k _ => (hpsi k).ne'),
    Real.log_exp, Real.log_pow, Real.log_prod fun k _ => (hgw k).ne',
    Real.log_prod fun k _ => (hpsi k).ne', log_vdet_evenPow hK0 hpos hinj]
  -- the energy bound at `t_k = (y_k / K)²`
  set t : Fin (dim n) → ℝ := fun k => (y k / Kr) ^ 2 with ht
  have htpos : ∀ k, 0 < t k := fun k => by have := hpos k; positivity
  have htinj : Function.Injective t := fun a b h => by
    have := (sq_eq_sq₀ (div_pos (hpos a) hK0).le (div_pos (hpos b) hK0).le).1 h
    exact hinj ((div_left_inj' hK0.ne').1 this)
  have hen := hE t htpos htinj
  have hsqrt : ∑ k, √(t k) = ∑ k, y k / Kr :=
    Finset.sum_congr rfl fun k _ => Real.sqrt_sq (div_pos (hpos k) hK0).le
  rw [hsqrt] at hen
  -- the weights
  have hsgw : ∑ k, Real.log (gramWeight n (y k)) ≤
      dim n * ((12 * N n - 2 * Kr) * Real.log Kr + 12 * Real.log Kr + C1) -
        Kr * ∑ k, Vfield (t k) + 17 * ∑ k, Real.log (1 + y k) := by
    calc ∑ k, Real.log (gramWeight n (y k))
        ≤ ∑ k, ((12 * N n - 2 * Kr) * Real.log Kr - Kr * Vfield (t k) +
            17 * Real.log (1 + y k) + 12 * Real.log Kr + C1) :=
          Finset.sum_le_sum fun k _ => log_gramWeight_le hn (hpos k)
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have hspsi : 17 * ∑ k, Real.log (1 + y k) - ∑ k, y k / Kr ≤ ∑ k, Real.log (psi n (y k)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k _ => log_le_log_psi n (hpos k)
  -- the number of pairs
  have hP : (∑ i : Fin (dim n), ((Finset.Ioi i).card : ℝ)) * 2 ≤ (dim n : ℝ) * dim n := by
    exact_mod_cast card_pairs_le (dim n)
  have hP' := mul_le_mul_of_nonneg_right hP hlogK
  rw [Bexp]
  push_cast
  nlinarith

/-! ### Integration -/

theorem integral_gram_eq (n : ℕ) (i j : Fin (dim n)) :
    ∫ y, evenPow n i y * evenPow n j y * (Ioi 0).indicator (gramWeight n) y =
      aeval (riemannZeta 5).re (G n i j) := by
  rw [aeval_G, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext y
  by_cases hy : y ∈ Ioi 0 <;> simp [evenPow, hy]

theorem integrable_gram (n : ℕ) (i j : Fin (dim n)) :
    Integrable fun y => evenPow n i y * evenPow n j y * (Ioi 0).indicator (gramWeight n) y := by
  have := (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_gram n i j)
  refine this.congr (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ Ioi 0 <;> simp [evenPow, hy]

/-- (6.14) at a fixed `n`, given the energy bound (6.9) with constant `E`. -/
theorem log_Δ_le_Bexp {n : ℕ} (hn : 1 ≤ n) {E : ℝ} (hE : EnergyLe n E) :
    Real.log (aeval (riemannZeta 5).re (Δ n)) ≤
      Bexp n E + dim n * Real.log (2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18)) := by
  have hA := andreief (μ := volume) (evenPow n) ((Ioi 0).indicator (gramWeight n))
    (integrable_gram n)
  have hG : (Matrix.of fun i j => ∫ y, evenPow n i y * evenPow n j y *
      (Ioi 0).indicator (gramWeight n) y).det = aeval (riemannZeta 5).re (Δ n) := by
    rw [Δ, AlgHom.map_det]
    congr 1
    ext i j
    rw [of_apply, integral_gram_eq, AlgHom.mapMatrix_apply, map_apply]
  rw [hG] at hA
  have hmono : ∫ y, vdet (evenPow n) y ^ 2 * ∏ k, (Ioi 0).indicator (gramWeight n) (y k)
      ∂(Measure.pi fun _ => volume) ≤
        ∫ y, exp (Bexp n E) * ∏ k, psi n (y k) ∂(Measure.pi fun _ => volume) :=
    integral_mono_of_nonneg
      (ae_of_all _ fun y => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun k _ =>
        indicator_nonneg (fun z hz => (gramWeight_pos n hz).le) _))
      ((Integrable.fintype_prod (f := fun _ => psi n) fun _ => integrable_psi hn).const_mul _)
      (ae_of_all _ (integrand_le hn hE))
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun _ => psi n), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, integral_psi hn, ← hA] at hmono
  have hΔ := aeval_Δ_pos n
  have hfac : (1 : ℝ) ≤ (dim n).factorial := Nat.one_le_cast.2 (Nat.factorial_pos _)
  have hK0 := K_pos hn
  have hle : aeval (riemannZeta 5).re (Δ n) ≤
      exp (Bexp n E) * (2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18)) ^ dim n := by
    nlinarith
  calc Real.log (aeval (riemannZeta 5).re (Δ n))
      ≤ Real.log (exp (Bexp n E) * (2 ^ 17 * (K n + (17).factorial * (K n : ℝ) ^ 18)) ^ dim n) :=
        Real.log_le_log hΔ hle
    _ = _ := by
        rw [Real.log_mul (exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow]

end Zeta5
