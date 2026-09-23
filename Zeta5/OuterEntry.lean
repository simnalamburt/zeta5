/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.InnerEntry
import Zeta5.OuterClass

/-!
# The corrected functional of §4.2

The moments `κ_d` with `d ≤ 4p - 2` are `p`-integral; this is the pullback of the statement that
`μ(t^e)` is integral for `e < 2p - 3`. Write `τ = τ_low + p⁻¹ τ_high` where `τ_low` keeps the
moments of degree `≤ 4p - 2` and `τ_high` is `p` times the rest, and let `τ_RL` be `τ_X` with
`τ_low` on the polynomial part. Then `G_K = A + p⁻¹ L` as in (4.10), with `A` built from `τ_RL`
and `L` from `τ_high`.

Two estimates for `τ_RL` are used in the outer range: a per-pole bound, and integrality when the
only surviving poles satisfy `|r| < p` (the divided difference of Proposition 4.3).
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `τ` with the moments of degree `> 4p - 2` removed. -/
noncomputable def tauLow (p : ℕ) (Q : ℚ[X]) : ℚ := ∑ d ∈ range (4 * p - 1), Q.coeff d * kappa d

/-- `p` times the removed part `τ - τ_low`. -/
noncomputable def tauHigh (p : ℕ) (Q : ℚ[X]) : ℚ := p * (taup Q - tauLow p Q)

omit hp in
theorem tauLow_add (Q Q' : ℚ[X]) : tauLow p (Q + Q') = tauLow p Q + tauLow p Q' := by
  simp only [tauLow, coeff_add, add_mul, sum_add_distrib]

omit hp in
theorem tauLow_C_mul (c : ℚ) (Q : ℚ[X]) : tauLow p (C c * Q) = c * tauLow p Q := by
  simp only [tauLow, coeff_C_mul, mul_sum, mul_assoc]

omit hp in
theorem tauHigh_add (Q Q' : ℚ[X]) : tauHigh p (Q + Q') = tauHigh p Q + tauHigh p Q' := by
  simp only [tauHigh, map_add, tauLow_add]; ring

omit hp in
theorem tauHigh_C_mul (c : ℚ) (Q : ℚ[X]) : tauHigh p (C c * Q) = c * tauHigh p Q := by
  have : taup (C c * Q) = c * taup Q := by rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [tauHigh, tauHigh, tauLow_C_mul, this]; ring

theorem VGe_tauLow (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : PolyVGe p 0 Q) : VGe p 0 (tauLow p Q) :=
  VGe_sum _ fun d hd => by
    have := mem_range.1 hd
    simpa using (hQ d).mul (VGe_kappa hp5 (by omega))

theorem VGe_tauHigh (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : PolyVGe p 0 Q) : VGe p 0 (tauHigh p Q) := by
  have h1 := VGe_taup_neg hQ hp5
  have h2 := (VGe_tauLow hp5 hQ).mono (show (0 - 1 : ℤ) ≤ 0 by norm_num)
  have := (VGe_natCast (p := p) 1).mul ((VGe_p_pow (p := p) 1).mul (h1.sub h2))
  simpa [tauHigh] using this

omit hp in
theorem tauHigh_eq_zero {Q : ℚ[X]} (hdeg : Q.natDegree + 2 ≤ 4 * p) : tauHigh p Q = 0 := by
  rw [tauHigh, taup_eq_sum, Polynomial.sum_over_range' _ (by simp) (4 * p - 1) (by omega)]
  simp [tauLow]

/-- `τ_X` with `τ_low` on the polynomial part. -/
noncomputable def tauRL (p : ℕ) (R : Finset ℤ) (N : ℚ[X]) : ℚ[X] :=
  C (tauLow p (N /ₘ poleProd R) + ∑ r ∈ R, resid R N r * H5 (dd r)) - C (tauRes R N) * X

theorem tauR_eq_tauRL (R : Finset ℤ) (N : ℚ[X]) :
    tauR R N = tauRL p R N + C ((p : ℚ)⁻¹ * tauHigh p (N /ₘ poleProd R)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [tauR, tauRL, tauConst, tauHigh]
  rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul, C_add, C_add, C_sub]
  ring

omit hp in
theorem tauRL_add (R : Finset ℤ) (N M : ℚ[X]) :
    tauRL p R (N + M) = tauRL p R N + tauRL p R M := by
  simp only [tauRL, add_divByMonic, tauLow_add, tauRes_add, resid_add, add_mul, sum_add_distrib,
    C_add]
  ring

omit hp in
theorem tauRL_C_mul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) :
    tauRL p R (C c * N) = C c * tauRL p R N := by
  have h1 : (C c * N) /ₘ poleProd R = C c * (N /ₘ poleProd R) := by
    rw [← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul]
  have h2 : tauRes R (C c * N) = c * tauRes R N := by
    rw [← smul_eq_C_mul, tauRes_smul]
  have h3 : ∀ r, resid R (C c * N) r = c * resid R N r := fun r => by
    rw [← smul_eq_C_mul, resid_smul]
  simp only [tauRL, h1, h2, h3, tauLow_C_mul, C_mul, C_add, mul_assoc, ← mul_sum]
  ring

/-! ### The per-pole bound -/

theorem VGe_H5_dd_RK {Kn : ℕ} (hK2 : Kn < p ^ 2) {r : ℤ} (hr : r ∈ RK Kn) :
    VGe p (-5) (H5 (dd r)) := by
  have hdd : dd r ≤ Kn := dd_le_of_mem_RK hr
  refine VGe_sum _ fun v hv => ?_
  have hv' := mem_Icc.1 hv
  have hnd : ¬(p : ℤ) ^ 2 ∣ (v : ℤ) := by
    intro h
    have := Int.natAbs_le_of_dvd_ne_zero h (by omega)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    simp at this; omega
  have := (VGe_inv_of_not_sq_dvd (p := p) (by omega : (v : ℤ) ≠ 0) hnd).pow 5
  push_cast at this
  rw [one_div, ← inv_pow]
  exact this.mono (by norm_num)

/-- If every residue has `v ≥ E + 5` with `E ≤ 0`, then `v^G(τ_RL) ≥ E`. -/
theorem PolyVGe_tauRL_perpole (hp5 : 5 ≤ p) {R : Finset ℤ} {N : ℚ[X]} (hN : PolyVGe p 0 N)
    {E : ℤ} (hE : E ≤ 0) (hres : ∀ r ∈ R, VGe p (E + 5) (resid R N r))
    (hH : ∀ r ∈ R, VGe p (-5) (H5 (dd r))) : PolyVGe p E (tauRL p R N) := by
  refine PolyVGe_tauR' (VGe.add ((VGe_tauLow hp5 (PolyVGe_divByMonic hN (PolyVGe_poleProd R)
    (poleProd_monic R))).mono hE) (VGe_sum _ fun r hr => ?_)) ?_
  · simpa using (hres r hr).mul (hH r hr)
  · exact VGe_sum _ fun r hr => (hres r hr).mono (by omega)
where
  PolyVGe_tauR' {c d : ℚ} {w : ℤ} (h1 : VGe p w c) (h2 : VGe p w d) :
      PolyVGe p w (C c - C d * X) :=
    (PolyVGe_C h1).sub ((PolyVGe_C h2).mul PolyVGe_X |>.mono (by simp))

/-! ### Cancelling the vanishing poles -/

omit hp in
theorem poleProd_dvd_of_roots {T : Finset ℤ} {N : ℚ[X]} (hN : ∀ r ∈ T, N.eval (r : ℚ) = 0) :
    poleProd T ∣ N := by
  refine Finset.prod_dvd_of_coprime ?_ fun r hr => dvd_iff_isRoot.2 (hN r hr)
  exact ((pairwise_coprime_X_sub_C (s := fun r : ℤ => (r : ℚ)) Int.cast_injective).set_pairwise
    (T : Set ℤ))

omit hp in
/-- The residues at the roots of the numerator vanish; the others are those of the reduced
fraction. -/
theorem resid_sum_roots {R T : Finset ℤ} (hT : T ⊆ R) {N : ℚ[X]}
    (hN : ∀ r ∈ T, N.eval (r : ℚ) = 0) (φ : ℤ → ℚ) :
    ∑ r ∈ R, resid R N r * φ r = ∑ r ∈ R \ T, resid (R \ T) (N /ₘ poleProd T) r * φ r := by
  have hdvd := poleProd_dvd_of_roots hN
  set N' := N /ₘ poleProd T
  have hNeq : N = poleProd T * N' := by
    have h := modByMonic_add_div N (poleProd T)
    rw [(modByMonic_eq_zero_iff_dvd (poleProd_monic T)).2 hdvd, zero_add] at h
    exact h.symm
  rw [← sum_sdiff hT, sum_eq_zero (s := T) fun r hr => by rw [resid, hN r hr, zero_div, zero_mul],
    add_zero]
  refine sum_congr rfl fun r hr => ?_
  have hr' := mem_sdiff.1 hr
  have hRr : R.erase r = T ∪ (R \ T).erase r := by
    ext s
    simp only [mem_erase, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hs, hsR⟩
      by_cases hsT : s ∈ T
      · exact Or.inl hsT
      · exact Or.inr ⟨hs, hsR, hsT⟩
    · rintro (hs | ⟨hs, hsR, _⟩)
      · exact ⟨fun h => hr'.2 (h ▸ hs), hT hs⟩
      · exact ⟨hs, hsR⟩
  have hdisj : Disjoint T ((R \ T).erase r) := by
    rw [disjoint_left]; intro s hs hs'
    exact (mem_sdiff.1 (mem_of_mem_erase hs')).2 hs
  have hPT : (poleProd T).eval (r : ℚ) ≠ 0 := by
    rw [poleProd, eval_prod, prod_ne_zero_iff]
    intro s hs h
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at h
    exact hr'.2 (by rw [show r = s by exact_mod_cast h]; exact hs)
  rw [resid, resid, eval_derivative_poleProd hr'.1, eval_derivative_poleProd hr, hRr, poleProd,
    prod_union hdisj, ← poleProd, ← poleProd, eval_mul, hNeq, eval_mul,
    mul_div_mul_left _ _ hPT]

/-- If the numerator vanishes at every pole except some with `|r| < p`, then `τ_RL` is integral:
the surviving congruent poles `r`, `r - p` pair off by the divided difference. -/
theorem PolyVGe_tauRL_small (hp5 : 5 ≤ p) {R : Finset ℤ} {N : ℚ[X]} (hN : PolyVGe p 0 N)
    (hsmall : ∀ r ∈ R, N.eval (r : ℚ) ≠ 0 → r.natAbs < p) : PolyVGe p 0 (tauRL p R N) := by
  have hp2 : p ≠ 2 := by omega
  set T := R.filter fun r : ℤ => N.eval (r : ℚ) = 0
  have hT : T ⊆ R := filter_subset _ _
  have hTN : ∀ r ∈ T, N.eval (r : ℚ) = 0 := fun r hr => (mem_filter.1 hr).2
  have hN' : PolyVGe p 0 (N /ₘ poleProd T) :=
    PolyVGe_divByMonic hN (PolyVGe_poleProd T) (poleProd_monic T)
  have hsm : ∀ r ∈ R \ T, r.natAbs < p := fun r hr => by
    have := mem_sdiff.1 hr
    exact hsmall r this.1 fun h => this.2 (mem_filter.2 ⟨this.1, h⟩)
  have hφ : ∀ r ∈ R \ T, VGe p 0 (H5 (dd r)) := fun r hr => by
    have := hsm r hr
    refine VGe_H5_of_lt ?_
    rcases le_or_gt 0 r with h | h
    · have := dd_of_nonneg h; omega
    · have := dd_of_neg h; omega
  have hφc : ∀ r ∈ R \ T, r - p ∈ R \ T → VGe p 1 (H5 (dd r) - H5 (dd (r - p))) := by
    intro r hr hrp
    have h1 := hsm r hr; have h2 := hsm _ hrp
    have hr0 : 0 < r := by omega
    have e1 : dd r = r.toNat := by have := dd_of_nonneg hr0.le; omega
    have e2 : dd (r - p) = p - 1 - r.toNat := by
      have := dd_of_neg (show r - p < 0 by omega); omega
    rw [e1, e2]
    exact VGe_H5_reflect hp2 (by omega)
  refine PolyVGe_tauRL_perpole.PolyVGe_tauR' (VGe.add ?_ ?_) ?_
  · exact VGe_tauLow hp5 (PolyVGe_divByMonic hN (PolyVGe_poleProd R) (poleProd_monic R))
  · rw [resid_sum_roots hT hTN]
    exact VGe_resid_sum_small hsm hN' _ hφ hφc
  · have := VGe_resid_sum_small (p := p) hsm hN' (fun _ => 1) (fun _ _ => VGe_one)
      (fun _ _ _ => by simpa using VGe_zero 1)
    rw [← resid_sum_roots hT hTN] at this
    simpa [tauRes] using this

end Zeta5
