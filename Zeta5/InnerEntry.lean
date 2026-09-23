/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.GramBasis
import Zeta5.SqClass
import Zeta5.ValueTau

/-!
# The entries in the inner range

Rows of the form `E_e(t) = ∏_{0 ≤ c ≤ m} (t + c²)^{e_c}`, `m = (p-1)/2`. For two such rows the entry
`μ_X(D_N⁶ E_e E_{e'} / D_K)` has valuation at least `min_c E_c - 4`, where for the class `c`
`E_c = 5 [c = 0] + κ(c) (e_c + e'_c + 6 ℓ_N(c) - ℓ_K(c))`; these are the bounds (4.2), (4.3).

At a pole `r` of the class `c` the pulled back numerator `± r⁵ D_N(-r²)⁶ E_e(-r²) E_{e'}(-r²)`
has valuation at least `E_c + κ(c) ℓ_K(c)`, while `∏_{s ≠ r} (r - s)` has valuation exactly
`κ(c) ℓ_K(c) - 1` since `|r - s| < p²`. At a point `y > K` of the class `c` the value of the
rational function has valuation at least `E_c`. The value form `PolyVGe_tauR_of_values` of the
local estimate concludes.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-- `E_e(t) = ∏_{0 ≤ c ≤ (p-1)/2} (t + c²)^{e_c}`, over `ℤ`. -/
noncomputable def EpolyZ (p : ℕ) (e : ℕ → ℕ) : ℤ[X] :=
  ∏ c ∈ range ((p - 1) / 2 + 1), (X + C ((c : ℤ) ^ 2)) ^ e c

/-- `E_e` over `ℚ`. -/
noncomputable def Epoly (p : ℕ) (e : ℕ → ℕ) : ℚ[X] := (EpolyZ p e).map (Int.castRingHom ℚ)

omit hp in
theorem Epoly_eq (e : ℕ → ℕ) :
    Epoly p e = ∏ c ∈ range ((p - 1) / 2 + 1), (X + C ((c : ℚ) ^ 2)) ^ e c := by
  simp [Epoly, EpolyZ, Polynomial.map_prod]

omit hp in
theorem natDegree_Epoly_le (e : ℕ → ℕ) :
    (Epoly p e).natDegree ≤ ∑ c ∈ range ((p - 1) / 2 + 1), e c := by
  rw [Epoly_eq]
  refine (natDegree_prod_le _ _).trans (sum_le_sum fun c _ => ?_)
  refine natDegree_pow_le.trans ?_
  rw [natDegree_X_add_C, mul_one]

/-- `κ(c) = 1` or `2`. -/
theorem kap_pos (c : ℕ) : 1 ≤ kap c := by unfold kap; split_ifs <;> omega

/-! ### Valuations of the numerator at a point of the class `c` -/

theorem VGe_eval_D {N : ℕ} {y : ℤ} {c : ℕ} (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) :
    VGe p (kap c * Inner.ell p N c) ((D N).eval (-(y : ℚ) ^ 2)) := by
  rw [D, poleDen, eval_prod, ell_eq]
  have h := VGe_prod (p := p) (Icc 1 N)
    (w := fun j : ℕ => if (p : ℤ) ∣ (j : ℤ) ^ 2 - (c : ℤ) ^ 2 then (kap c : ℤ) else 0)
    (f := fun j : ℕ => ((((j : ℤ) ^ 2 - y ^ 2 : ℤ)) : ℚ)) fun j _ => by
      split_ifs with hj
      · exact VGe_sq_sub_sq hc hj
      · exact VGe_intCast _
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul] at h
  convert h using 1
  · ring
  · refine prod_congr rfl fun j _ => ?_
    simp only [eval_add, eval_X, eval_C]; push_cast; ring

theorem VGe_eval_Epoly {y : ℤ} {c : ℕ} (hcm : c ≤ (p - 1) / 2)
    (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) (e : ℕ → ℕ) :
    VGe p (kap c * e c) ((Epoly p e).eval (-(y : ℚ) ^ 2)) := by
  rw [Epoly_eq, eval_prod]
  have h := VGe_prod (p := p) (range ((p - 1) / 2 + 1))
    (w := fun c' => if c' = c then ((kap c * e c : ℕ) : ℤ) else 0)
    (f := fun c' => ((((c' : ℤ) ^ 2 - y ^ 2 : ℤ)) : ℚ) ^ e c') fun c' hc' => by
      split_ifs with hcc
      · subst hcc
        have := (VGe_sq_sub_sq (p := p) hc (x := (c' : ℤ)) (by simp)).pow (e c')
        push_cast at this ⊢
        simpa [mul_comm] using this
      · have := VGe_intCast (p := p) (((c' : ℤ) ^ 2 - y ^ 2) ^ e c')
        push_cast at this ⊢
        exact this
  rw [sum_ite_eq' _ c] at h
  simp only [mem_range, show c < (p - 1) / 2 + 1 by omega, ↓reduceIte] at h
  convert h using 1
  · push_cast; ring
  · refine prod_congr rfl fun c' _ => ?_
    simp only [eval_pow, eval_add, eval_X, eval_C]; push_cast; ring

theorem VGe_pow_five {y : ℤ} {c : ℕ} (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) :
    VGe p (if c = 0 then 5 else 0) ((y : ℚ) ^ 5) := by
  split_ifs with h0
  · subst h0
    have := (VGe_of_dvd_int (dvd_of_class_zero hc)).pow 5
    simpa using this
  · have := VGe_intCast (p := p) (y ^ 5)
    push_cast at this; exact this

/-- The inverse of a product `∏_{s ∈ T} (y - s)` of nonzero factors not divisible by `p²` has
valuation `≥ -#{s ∈ T | p ∣ y - s}`. -/
theorem VGe_inv_prod_sub (T : Finset ℤ) (y : ℤ)
    (hsep : ∀ s ∈ T, y ≠ s ∧ ¬(p : ℤ) ^ 2 ∣ y - s) :
    VGe p (-(#{s ∈ T | (p : ℤ) ∣ y - s} : ℤ)) ((∏ s ∈ T, ((y : ℚ) - s))⁻¹) := by
  rw [← prod_inv_distrib]
  have h := VGe_prod (p := p) T
    (w := fun s => if (p : ℤ) ∣ y - s then (-1 : ℤ) else 0)
    (f := fun s => ((y : ℚ) - s)⁻¹) fun s hs => by
      split_ifs with hd
      · have := VGe_inv_of_not_sq_dvd (p := p) (sub_ne_zero.2 (hsep s hs).1) (hsep s hs).2
        push_cast at this; exact this
      · have := VGe_inv_int (p := p) hd
        push_cast at this; exact this
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul] at h
  refine h.mono (by ring_nf; rfl)

/-! ### The entry bound -/

/-- The class exponent `E_c` of (4.2), (4.3) for rows with exponent vectors `e`, `e'`. -/
def Ecl (p Nn Kn : ℕ) (e e' : ℕ → ℕ) (c : ℕ) : ℤ :=
  (if c = 0 then 5 else 0) +
    kap c * ((e c + e' c : ℕ) + 6 * (Inner.ell p Nn c : ℤ) - Inner.ell p Kn c)

/-- The value of the pulled back numerator at an integer point. -/
theorem eval_pull_entry (Nn Kn : ℕ) (U U' : ℚ[X]) (y : ℤ) :
    (pull (Icc 1 Kn) (D Nn ^ 6 * U * U')).eval (y : ℚ) =
      (-1) ^ (Icc 1 Kn).card * (y : ℚ) ^ 5 * ((D Nn).eval (-(y : ℚ) ^ 2) ^ 6 *
        U.eval (-(y : ℚ) ^ 2) * U'.eval (-(y : ℚ) ^ 2)) := by
  simp [pull, eval_comp]

/-- The numerator of an entry at a point `y` of the class `c` has valuation
`≥ E_c + κ(c) ℓ_K(c)`. -/
theorem VGe_eval_pull_entry {Nn Kn : ℕ} (e e' : ℕ → ℕ) {y : ℤ} {c : ℕ}
    (hcm : c ≤ (p - 1) / 2) (hc : (p : ℤ) ∣ y ^ 2 - (c : ℤ) ^ 2) :
    VGe p (Ecl p Nn Kn e e' c + kap c * Inner.ell p Kn c)
      ((pull (Icc 1 Kn) (D Nn ^ 6 * Epoly p e * Epoly p e')).eval (y : ℚ)) := by
  rw [eval_pull_entry]
  have h1 : VGe p 0 ((-1 : ℚ) ^ (Icc 1 Kn).card) := by
    simpa using VGe_intCast (p := p) ((-1) ^ (Icc 1 Kn).card)
  have h := (h1.mul (VGe_pow_five hc)).mul
    ((((VGe_eval_D (N := Nn) hc).pow 6).mul (VGe_eval_Epoly hcm hc e)).mul
      (VGe_eval_Epoly hcm hc e'))
  refine h.mono (le_of_eq ?_)
  simp only [Ecl]
  push_cast
  ring

variable (p) in
/-- The window `K + 1, …, K + D` and the poles are `p`-adically close: `|y - s| < p²`. -/
def Close (Kn D : ℕ) : Prop := 2 * Kn + D < p ^ 2

/-- **The entry bound** (4.2), (4.3): if `E + 4 ≤ E_c` for every class `c`, the entry has
`v_p^G ≥ E`. -/
theorem PolyVGe_entry (hp2 : p ≠ 2) {Nn Kn : ℕ} (e e' : ℕ → ℕ) {Dw : ℕ}
    (hdeg : (pull (Icc 1 Kn) (D Nn ^ 6 * Epoly p e * Epoly p e')).natDegree < Dw + 2 * Kn)
    (hDw : 1 ≤ Dw) (hclose : Close p Kn Dw) {E : ℤ}
    (hE : ∀ c ≤ (p - 1) / 2, E + 4 ≤ Ecl p Nn Kn e e' c) :
    PolyVGe p E (muX (D Nn ^ 6 * Epoly p e * Epoly p e') (Icc 1 Kn)) := by
  unfold Close at hclose
  rw [muX_eq_tauR _ _ (by simp), poleSet_Icc]
  set Nm := pull (Icc 1 Kn) (D Nn ^ 6 * Epoly p e * Epoly p e')
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hsq : ∀ z : ℤ, z ≠ 0 → z.natAbs < p ^ 2 → ¬(p : ℤ) ^ 2 ∣ z := by
    intro z hz hlt h
    have := Int.natAbs_le_of_dvd_ne_zero h hz
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    omega
  refine PolyVGe_tauR_of_values (a := (Kn : ℤ) + 1) (D := Dw) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [natDegree_divByMonic _ (poleProd_monic _), natDegree_poleProd, card_RK]; omega
  · have hlt : Dw < p ^ 2 := by omega
    exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by omega) hlt)
  · -- residues
    intro r hr
    obtain ⟨c, hcm, hc⟩ := exists_sq_class hp2 r
    have hRK := mem_erase.1 hr
    have hrI := mem_Icc.1 hRK.2
    rw [resid, eval_derivative_poleProd hr, poleProd, eval_prod, div_eq_mul_inv]
    have hden := VGe_inv_prod_sub (p := p) ((RK Kn).erase r) r fun s hs => by
      have hs' := mem_erase.1 hs
      have hsI := mem_Icc.1 (mem_erase.1 hs'.2).2
      exact ⟨Ne.symm hs'.1, hsq _ (sub_ne_zero.2 (Ne.symm hs'.1)) (by omega)⟩
    have hcard : #{s ∈ (RK Kn).erase r | (p : ℤ) ∣ r - s} = kap c * Inner.ell p Kn c - 1 := by
      rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨hr, by simp⟩), card_RK_dvd hp2 hcm hc]
    have hpos : 1 ≤ kap c * Inner.ell p Kn c := by
      rw [← card_RK_dvd hp2 hcm hc]; exact card_pos.2 ⟨r, mem_filter.2 ⟨hr, by simp⟩⟩
    rw [hcard] at hden
    have h := (VGe_eval_pull_entry (p := p) (Nn := Nn) (Kn := Kn) e e' hcm hc).mul hden
    simp only [eval_sub, eval_X, eval_C]
    refine h.mono ?_
    have := hE c hcm
    push_cast [Nat.cast_sub hpos]
    omega
  · -- the window
    intro t ht
    obtain ⟨c, hcm, hc⟩ := exists_sq_class hp2 ((Kn : ℤ) + 1 + t)
    have hnot : ∀ s ∈ RK Kn, ((Kn : ℤ) + 1 + t) ≠ s := fun s hs h => by
      have := mem_Icc.1 (mem_erase.1 hs).2; omega
    have hPi : (poleProd (RK Kn)).eval (((Kn : ℤ) + 1 + t : ℤ) : ℚ) =
        ∏ s ∈ RK Kn, ((((Kn : ℤ) + 1 + t : ℤ) : ℚ) - s) := by
      rw [poleProd, eval_prod]; simp
    refine ⟨?_, ?_⟩
    · rw [hPi, prod_ne_zero_iff]
      intro s hs h
      rw [sub_eq_zero] at h
      exact hnot s hs (by exact_mod_cast h)
    · have hden := VGe_inv_prod_sub (p := p) (RK Kn) ((Kn : ℤ) + 1 + t) fun s hs => by
        have hsI := mem_Icc.1 (mem_erase.1 hs).2
        exact ⟨hnot s hs, hsq _ (sub_ne_zero.2 (hnot s hs)) (by omega)⟩
      rw [card_RK_dvd hp2 hcm hc] at hden
      rw [hPi, div_eq_mul_inv]
      have h := (VGe_eval_pull_entry (p := p) (Nn := Nn) (Kn := Kn) e e' hcm hc).mul hden
      refine h.mono ?_
      have := hE c hcm
      push_cast
      omega
  · intro t ht r hr
    have hrI := mem_Icc.1 (mem_erase.1 hr).2
    have hne : ((Kn : ℤ) + 1 + t) - r ≠ 0 := by omega
    have := VGe_inv_of_not_sq_dvd (p := p) hne (hsq _ hne (by omega))
    push_cast at this ⊢
    exact this
  · intro r hr
    have hrI := mem_Icc.1 (mem_erase.1 hr).2
    have hdd : dd r ≤ Kn := dd_le_of_mem_RK hr
    refine VGe_sum _ fun v hv => ?_
    have hv' := mem_Icc.1 hv
    have hnd : ¬(p : ℤ) ^ 2 ∣ (v : ℤ) := hsq _ (by omega) (by simp; omega)
    have := (VGe_inv_of_not_sq_dvd (p := p) (by omega : (v : ℤ) ≠ 0) hnd).pow 5
    push_cast at this
    rw [one_div, ← inv_pow]
    exact this.mono (by norm_num)

end Zeta5
