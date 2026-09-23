/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.DetBound
import Zeta5.InnerRange
import Zeta5.OuterEntry

/-!
# The outer range (Proposition 4.3)

For `K/3 < p ≤ K` we use the basis (4.11): for the class `c` with remaining poles `J_c ⊆ (N, K]`,
the rows `P_c q_{c,i}`, `i < #J_c`, where `P_c = ∏_{j ∈ (N, K] \ J_c} (t + j²)` and
`q_{c,i} = (t + c²)^i`, except that for an ordinary class the rows `i ≥ ℓ - 2` are
`E_c (t + c²)^{i - (ℓ - 2)}` with `E_c` the product over the poles `j > p` of the class. Modulo `p`
this is the basis of the Chinese remainder theorem, so it is unimodular.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

namespace Outer

set_option linter.unusedSectionVars false

/-! ### Consequences of (4.9) -/

section Hyp

variable {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < 3 * p) (hp2 : p ≤ K n)
include hM hK hp1 hp2

theorem hyp_n : 8000 ≤ n := by simp only [K] at hK; nlinarith

theorem hyp_p13 : 13 * n < p := by simp only [K] at hp1; omega

theorem hyp_p5 : 5 ≤ p := by have := hyp_n hM hK hp1 hp2; have := hyp_p13 hM hK hp1 hp2; omega

theorem hyp_p2 : p ≠ 2 := by have := hyp_p5 hM hK hp1 hp2; omega

theorem hyp_odd : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · exact absurd h (hyp_p2 hM hK hp1 hp2)
  · exact h

theorem hyp_two_m : 2 * ((p - 1) / 2) = p - 1 := by
  have := hyp_odd hM hK hp1 hp2; omega

theorem hyp_N_lt : 2 * N n < p := by
  have := hyp_p13 hM hK hp1 hp2; simp only [N]; omega

theorem hyp_N_le_m : N n ≤ (p - 1) / 2 := by
  have := hyp_N_lt hM hK hp1 hp2; omega

theorem hyp_5N : 5 * N n + 2 ≤ 2 * p := by
  have := hyp_p13 hM hK hp1 hp2; simp only [N]; omega

theorem hyp_sq : 2 * K n < p ^ 2 := by
  have h1 := hyp_p13 hM hK hp1 hp2
  have h2 := hyp_n hM hK hp1 hp2
  simp only [K]
  nlinarith

theorem hyp_mK : 1 ≤ K n / p ∧ K n / p ≤ 2 := by
  have hp0 : 0 < p := by have := hyp_p5 hM hK hp1 hp2; omega
  constructor
  · exact (Nat.le_div_iff_mul_le hp0).2 (by omega)
  · exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp0).2 (by omega))

theorem hyp_ellN0 : Inner.ell p (N n) 0 = 0 := by
  rw [ell_eq_zero_class, Nat.div_eq_of_lt (by have := hyp_N_lt hM hK hp1 hp2; omega)]

/-- `ℓ_N(c) = [c ≤ N]` for `1 ≤ c ≤ m`. -/
theorem hyp_ellN {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    Inner.ell p (N n) c = if c ≤ N n then 1 else 0 := by
  have hN := hyp_N_lt hM hK hp1 hp2
  have hp0 : 0 < p := by omega
  rw [ell_exact (hyp_p2 hM hK hp1 hp2) hc hcm, Nat.div_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  have : ¬ p - c ≤ N n := by omega
  simp [this]

end Hyp

/-! ### The basis (4.11) -/

section Basis

variable (p n : ℕ)

/-- The number of rows of the class `c`: its remaining poles. -/
def Lr (c : ℕ) : ℕ := #(J p (N n) (K n) c)

/-- The poles `j > p` of the class `c`. -/
def Hi (c : ℕ) : Finset ℕ := (J p (N n) (K n) c).filter fun j => p < j

/-- `ℓ - 2`: the number of rows `(t + c²)^i`. -/
def el (c : ℕ) : ℕ := #(Hi p n c)

/-- `P_c = ∏_{j ∈ (N, K] \ J_c} (t + j²)`. -/
noncomputable def Pc (c : ℕ) : ℤ[X] :=
  ∏ j ∈ Ioc (N n) (K n) \ J p (N n) (K n) c, (X + C ((j : ℤ) ^ 2))

/-- `E_c = ∏_{j ∈ J_c, j > p} (t + j²)`. -/
noncomputable def Ec (c : ℕ) : ℤ[X] := ∏ j ∈ Hi p n c, (X + C ((j : ℤ) ^ 2))

/-- `q_{c,i}`. -/
noncomputable def qc (c i : ℕ) : ℤ[X] :=
  if c ≠ 0 ∧ el p n c ≤ i then Ec p n c * (X + C ((c : ℤ) ^ 2)) ^ (i - el p n c)
  else (X + C ((c : ℤ) ^ 2)) ^ i

/-- The row `P_c q_{c,i}`. -/
noncomputable def rowZ (c i : ℕ) : ℤ[X] := Pc p n c * qc p n c i

variable {p n}

theorem el_le (c : ℕ) : el p n c ≤ Lr p n c := card_le_card (filter_subset _ _)

theorem natDegree_Pc (c : ℕ) : (Pc p n c).natDegree = (K n - N n) - Lr p n c := by
  rw [Pc, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
  rw [card_sdiff_of_subset (show J p (N n) (K n) c ⊆ Ioc (N n) (K n) from filter_subset _ _),
    Nat.card_Ioc, Lr]

theorem Pc_monic (c : ℕ) : (Pc p n c).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem Ec_monic (c : ℕ) : (Ec p n c).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem natDegree_Ec (c : ℕ) : (Ec p n c).natDegree = el p n c := by
  rw [Ec, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one, el]

theorem qc_monic (c i : ℕ) : (qc p n c i).Monic := by
  unfold qc
  split_ifs
  · exact (Ec_monic c).mul ((monic_X_add_C _).pow _)
  · exact (monic_X_add_C _).pow _

theorem natDegree_qc (c i : ℕ) : (qc p n c i).natDegree = i := by
  unfold qc
  split_ifs with h
  · rw [(Ec_monic c).natDegree_mul ((monic_X_add_C _).pow _), natDegree_Ec, natDegree_pow,
      natDegree_X_add_C]
    omega
  · rw [natDegree_pow, natDegree_X_add_C, mul_one]

theorem natDegree_rowZ (c i : ℕ) :
    (rowZ p n c i).natDegree = (K n - N n) - Lr p n c + i := by
  rw [rowZ, (Pc_monic c).natDegree_mul (qc_monic c i), natDegree_Pc, natDegree_qc]

end Basis

section Reduce

variable {n : ℕ}

/-- The sizes add up to `h`. -/
theorem sum_Lr (hp2 : p ≠ 2) : ∑ c ∈ range ((p - 1) / 2 + 1), Lr p n c = K n - N n :=
  sum_card_J hp2 _ _

/-! ### Reduction modulo `p` -/

theorem sq_zmod_of_mem_J {Nn Kn c j : ℕ} (hj : j ∈ J p Nn Kn c) :
    (((j : ℤ) ^ 2 : ℤ) : ZMod p) = (((c : ℤ) ^ 2 : ℤ) : ZMod p) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]
  exact (mem_J.1 hj).2

theorem map_prod_J {Nn Kn c : ℕ} (T : Finset ℕ) (hT : T ⊆ J p Nn Kn c) :
    (∏ j ∈ T, (X + C ((j : ℤ) ^ 2))).map (Int.castRingHom (ZMod p)) =
      (X + C (((c : ℤ) ^ 2 : ℤ) : ZMod p)) ^ #T := by
  rw [Polynomial.map_prod, ← prod_const]
  refine prod_congr rfl fun j hj => ?_
  rw [Polynomial.map_add, map_X, map_C, eq_intCast, sq_zmod_of_mem_J (hT hj)]

theorem map_Pc (hp2 : p ≠ 2) {c : ℕ} (hc : c ≤ (p - 1) / 2) :
    (Pc p n c).map (Int.castRingHom (ZMod p)) =
      ∏ c' ∈ (range ((p - 1) / 2 + 1)).erase c,
        (X + C (((c' : ℤ) ^ 2 : ℤ) : ZMod p)) ^ Lr p n c' := by
  rw [Pc, sdiff_J hp2 hc, prod_biUnion]
  · rw [Polynomial.map_prod]
    refine prod_congr rfl fun c' _ => ?_
    exact map_prod_J (c := c') _ subset_rfl
  · intro c1 h1 c2 h2 hne
    exact J_disjoint (by have := mem_range.1 (mem_of_mem_erase h1); omega)
      (by have := mem_range.1 (mem_of_mem_erase h2); omega) hne

theorem map_qc (c i : ℕ) :
    (qc p n c i).map (Int.castRingHom (ZMod p)) = (X + C (((c : ℤ) ^ 2 : ℤ) : ZMod p)) ^ i := by
  unfold qc
  split_ifs with h
  · rw [Polynomial.map_mul, Ec, map_prod_J (c := c) (Hi p n c) (filter_subset _ _),
      Polynomial.map_pow, Polynomial.map_add, map_X, map_C, eq_intCast, ← pow_add]
    congr 1
    rw [show #(Hi p n c) = el p n c from rfl]
    omega
  · simp [Polynomial.map_pow]

/-- The rows reduce to the Chinese remainder basis. -/
theorem map_rowZ (hp2 : p ≠ 2) (c : Fin ((p - 1) / 2 + 1)) (i : ℕ) :
    (rowZ p n c i).map (Int.castRingHom (ZMod p)) =
      crtRow (fun c : Fin ((p - 1) / 2 + 1) => -(((c : ℕ) : ZMod p) ^ 2))
        (fun c => Lr p n c) c i := by
  have hc : (c : ℕ) ≤ (p - 1) / 2 := Nat.lt_succ_iff.1 c.2
  rw [rowZ, Polynomial.map_mul, map_Pc hp2 hc, map_qc, crtRow]
  congr 1
  · have e1 := mul_prod_erase (range ((p - 1) / 2 + 1))
      (fun c' : ℕ => (X + C (((c' : ℤ) ^ 2 : ℤ) : ZMod p)) ^ Lr p n c') (mem_range.2 c.2)
    have e2 := mul_prod_erase (univ : Finset (Fin ((p - 1) / 2 + 1)))
      (fun c' : Fin ((p - 1) / 2 + 1) => (X - C (-(((c' : ℕ) : ZMod p) ^ 2))) ^ Lr p n c')
      (mem_univ c)
    have e3 : ∏ c' ∈ range ((p - 1) / 2 + 1), (X + C (((c' : ℤ) ^ 2 : ℤ) : ZMod p)) ^ Lr p n c' =
        ∏ c' : Fin ((p - 1) / 2 + 1), (X - C (-(((c' : ℕ) : ZMod p) ^ 2))) ^ Lr p n c' := by
      rw [prod_range]
      refine prod_congr rfl fun c' _ => ?_
      simp [sub_eq_add_neg]
    rw [← e1, ← e2] at e3
    have hne : (X + C (((((c : ℕ) : ℤ) ^ 2 : ℤ)) : ZMod p)) ^ Lr p n c ≠ 0 :=
      pow_ne_zero _ (X_add_C_ne_zero _)
    refine mul_left_cancel₀ hne (e3.trans ?_)
    congr 1
    simp [sub_eq_add_neg]
  · simp [sub_eq_add_neg]

end Reduce

/-! ### The entries -/

section Entries

/-- The weights (4.12), doubled; for the zero class `min(0, 2i - m_K + 1/2)`. -/
def wt (p n c i : ℕ) : ℤ :=
  if c = 0 then min 0 (4 * i - 2 * (K n / p : ℕ) + 1)
  else if i < el p n c then
    min 0 (2 * i + 6 * (Inner.ell p (N n) c : ℤ) - Inner.ell p (K n) c - 4)
  else 0

theorem wt_nonpos (p n c i : ℕ) : wt p n c i ≤ 0 := by
  unfold wt; split_ifs <;> omega

/-- The rows over `ℚ`. -/
noncomputable def rowQ (p n c i : ℕ) : ℚ[X] := (rowZ p n c i).map (Int.castRingHom ℚ)

/-- The numerator of the entry of the rows `(c₁, i₁)`, `(c₂, i₂)`. -/
noncomputable def numer (p n c1 i1 c2 i2 : ℕ) : ℚ[X] :=
  pull (Icc 1 (K n)) (D (N n) ^ 6 * rowQ p n c1 i1 * rowQ p n c2 i2)

variable {n : ℕ}

omit hp in
theorem eval_prod_vanish (T : Finset ℕ) {r : ℤ} (hr : r.natAbs ∈ T) :
    ((∏ j ∈ T, (X + C ((j : ℤ) ^ 2))).map (Int.castRingHom ℚ)).eval (-(r : ℚ) ^ 2) = 0 := by
  rw [Polynomial.map_prod, eval_prod]
  refine prod_eq_zero hr ?_
  rw [Polynomial.map_add, map_X, map_C, eval_add, eval_X, eval_C, eq_intCast]
  push_cast
  rw [sq_abs]
  ring

omit hp in
theorem eval_D_vanish {Nn : ℕ} {r : ℤ} (h1 : 1 ≤ r.natAbs) (h2 : r.natAbs ≤ Nn) :
    (D Nn).eval (-(r : ℚ) ^ 2) = 0 := by
  rw [D, poleDen, eval_prod]
  refine prod_eq_zero (mem_Icc.2 ⟨h1, h2⟩) ?_
  simp only [eval_add, eval_X, eval_C]
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

theorem eval_numer (c1 i1 c2 i2 : ℕ) (r : ℤ) :
    (numer p n c1 i1 c2 i2).eval (r : ℚ) = (-1) ^ (Icc 1 (K n)).card * (r : ℚ) ^ 5 *
      ((D (N n)).eval (-(r : ℚ) ^ 2) ^ 6 * (rowQ p n c1 i1).eval (-(r : ℚ) ^ 2) *
        (rowQ p n c2 i2).eval (-(r : ℚ) ^ 2)) :=
  eval_pull_entry _ _ _ _ r

theorem rowQ_eval_zero {c i : ℕ} {r : ℤ} (hj : r.natAbs ∈ Ioc (N n) (K n))
    (hjn : r.natAbs ∉ J p (N n) (K n) c) : (rowQ p n c i).eval (-(r : ℚ) ^ 2) = 0 := by
  rw [rowQ, rowZ, Polynomial.map_mul, eval_mul, Pc, eval_prod_vanish _ (mem_sdiff.2 ⟨hj, hjn⟩),
    zero_mul]

/-- The numerator vanishes unless the pole lies in both classes. -/
theorem numer_eval_zero {c1 i1 c2 i2 : ℕ} {r : ℤ} (hr : r ∈ RK (K n))
    (h : ¬(r.natAbs ∈ J p (N n) (K n) c1 ∧ r.natAbs ∈ J p (N n) (K n) c2)) :
    (numer p n c1 i1 c2 i2).eval (r : ℚ) = 0 := by
  have hrI := mem_Icc.1 (mem_erase.1 hr).2
  have hr0 := (mem_erase.1 hr).1
  rw [eval_numer]
  by_cases hjN : r.natAbs ≤ N n
  · rw [eval_D_vanish (by omega) hjN]; simp
  · have hj : r.natAbs ∈ Ioc (N n) (K n) := mem_Ioc.2 ⟨by omega, by omega⟩
    by_cases h1 : r.natAbs ∈ J p (N n) (K n) c1
    · rw [rowQ_eval_zero hj fun h2 => h ⟨h1, h2⟩]; simp
    · rw [rowQ_eval_zero hj h1]; simp

theorem PolyVGe_rowQ (c i : ℕ) : PolyVGe p 0 (rowQ p n c i) := PolyVGe_intCast_poly _

theorem PolyVGe_numer (c1 i1 c2 i2 : ℕ) : PolyVGe p 0 (numer p n c1 i1 c2 i2) := by
  refine PolyVGe_pull _ ?_
  simpa using (((PolyVGe_D (p := p) (N n)).pow 6).mul (PolyVGe_rowQ c1 i1)).mul (PolyVGe_rowQ c2 i2)

theorem p_not_mem_J {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) : p ∉ J p (N n) (K n) c := by
  intro h
  have h1 := (mem_J.1 h).2
  have h2 : (p : ℤ) ∣ (c : ℤ) ^ 2 := by
    have := dvd_sub (dvd_pow_self (p : ℤ) (by norm_num : 2 ≠ 0)) h1
    rwa [sub_sub_cancel] at this
  have h3 := (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h2
  have := Int.le_of_dvd (by omega) h3
  omega

theorem rowQ_eval_zero_Hi {c i : ℕ} (hc : c ≠ 0) (hi : el p n c ≤ i) {r : ℤ}
    (hr : r.natAbs ∈ Hi p n c) : (rowQ p n c i).eval (-(r : ℚ) ^ 2) = 0 := by
  rw [rowQ, rowZ, qc, ite_eq_left_of_eq_true _ _ (eq_true ⟨hc, hi⟩), Polynomial.map_mul,
    Polynomial.map_mul, eval_mul, eval_mul,
    Ec, eval_prod_vanish _ hr]
  simp

theorem VGe_rowQ_class {c i : ℕ} (hq : ¬(c ≠ 0 ∧ el p n c ≤ i)) {r : ℤ}
    (hc : (p : ℤ) ∣ r ^ 2 - (c : ℤ) ^ 2) :
    VGe p (kap c * i) ((rowQ p n c i).eval (-(r : ℚ) ^ 2)) := by
  rw [rowQ, rowZ, qc, ite_eq_right_of_eq_false _ _ (eq_false hq), Polynomial.map_mul, eval_mul]
  have h1 : VGe p 0 (((Pc p n c).map (Int.castRingHom ℚ)).eval (-(r : ℚ) ^ 2)) :=
    VGe_eval (PolyVGe_intCast_poly _) (by
      have := VGe_intCast (p := p) (-r ^ 2); push_cast at this; exact this)
  have h2 : (((X + C ((c : ℤ) ^ 2)) ^ i).map (Int.castRingHom ℚ)).eval (-(r : ℚ) ^ 2) =
      (((((c : ℤ) ^ 2 - r ^ 2 : ℤ)) : ℚ)) ^ i := by
    rw [Polynomial.map_pow, Polynomial.map_add, map_X, map_C, eval_pow, eval_add, eval_X, eval_C,
      eq_intCast]
    push_cast; ring
  rw [h2]
  have h3 := (VGe_sq_sub_sq (p := p) hc (x := (c : ℤ)) (by simp)).pow i
  simpa [mul_comm] using h1.mul h3

variable {M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < 3 * p) (hp2 : p ≤ K n)
include hM hK hp1 hp2

/-- The residue at a pole of the class `c` of an entry whose rows vanish to orders `a`, `b`
there. -/
theorem VGe_resid_class {U U' : ℚ[X]} {r : ℤ} (hr : r ∈ RK (K n)) {c : ℕ} (hcm : c ≤ (p - 1) / 2)
    (hc : (p : ℤ) ∣ r ^ 2 - (c : ℤ) ^ 2) {a b : ℕ}
    (hU : VGe p (kap c * a) (U.eval (-(r : ℚ) ^ 2)))
    (hU' : VGe p (kap c * b) (U'.eval (-(r : ℚ) ^ 2))) :
    VGe p (Ecl p (N n) (K n) (fun _ => a) (fun _ => b) c + 1)
      (resid (RK (K n)) (pull (Icc 1 (K n)) (D (N n) ^ 6 * U * U')) r) := by
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hsq := hyp_sq hM hK hp1 hp2
  have hsqd : ∀ z : ℤ, z ≠ 0 → z.natAbs < p ^ 2 → ¬(p : ℤ) ^ 2 ∣ z := by
    intro z hz hlt h
    have := Int.natAbs_le_of_dvd_ne_zero h hz
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    omega
  have hrI := mem_Icc.1 (mem_erase.1 hr).2
  rw [resid, eval_derivative_poleProd hr, poleProd, eval_prod, div_eq_mul_inv]
  have hden := VGe_inv_prod_sub (p := p) ((RK (K n)).erase r) r fun s hs => by
    have hs' := mem_erase.1 hs
    have hsI := mem_Icc.1 (mem_erase.1 hs'.2).2
    exact ⟨Ne.symm hs'.1, hsqd _ (sub_ne_zero.2 (Ne.symm hs'.1)) (by omega)⟩
  have hcard : #{s ∈ (RK (K n)).erase r | (p : ℤ) ∣ r - s} = kap c * Inner.ell p (K n) c - 1 := by
    rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨hr, by simp⟩), card_RK_dvd hp2' hcm hc]
  have hpos : 1 ≤ kap c * Inner.ell p (K n) c := by
    rw [← card_RK_dvd hp2' hcm hc]; exact card_pos.2 ⟨r, mem_filter.2 ⟨hr, by simp⟩⟩
  rw [hcard] at hden
  rw [eval_pull_entry]
  have h1 : VGe p 0 ((-1 : ℚ) ^ (Icc 1 (K n)).card) := by
    simpa using VGe_intCast (p := p) ((-1) ^ (Icc 1 (K n)).card)
  have h := ((h1.mul (VGe_pow_five hc)).mul
    ((((VGe_eval_D (N := N n) hc).pow 6).mul hU).mul hU')).mul hden
  simp only [eval_sub, eval_X, eval_C]
  refine h.mono (le_of_eq ?_)
  simp only [Ecl]
  push_cast [Nat.cast_sub hpos]
  ring

/-- **The entry bound (4.12)** for the corrected functional. -/
theorem entry_bound {c1 c2 i1 i2 : ℕ} (hc1 : c1 ≤ (p - 1) / 2) (hc2 : c2 ≤ (p - 1) / 2) :
    PolyVGe p ((wt p n c1 i1 + wt p n c2 i2 + 1) / 2)
      (tauRL p (RK (K n)) (numer p n c1 i1 c2 i2)) := by
  have hp5 := hyp_p5 hM hK hp1 hp2
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hsq := hyp_sq hM hK hp1 hp2
  have hH : ∀ r ∈ RK (K n), VGe p (-5) (H5 (dd r)) := fun r hr => VGe_H5_dd_RK (by omega) hr
  have hw1 := wt_nonpos p n c1 i1
  have hw2 := wt_nonpos p n c2 i2
  by_cases hcc : c1 = c2
  · subst hcc
    by_cases hsm : c1 ≠ 0 ∧ (el p n c1 ≤ i1 ∨ el p n c1 ≤ i2)
    · -- the divided difference
      refine (PolyVGe_tauRL_small hp5 (PolyVGe_numer c1 i1 c1 i2) fun r hr hne => ?_).mono
        (by omega)
      by_contra hge
      simp only [not_lt] at hge
      have hJ : r.natAbs ∈ J p (N n) (K n) c1 := by
        by_contra hJ; exact hne (numer_eval_zero hr fun h => hJ h.1)
      have hpr : r.natAbs ≠ p := fun h => p_not_mem_J (Nat.one_le_iff_ne_zero.2 hsm.1) hc1
        (h ▸ hJ)
      have hHi : r.natAbs ∈ Hi p n c1 := mem_filter.2 ⟨hJ, by omega⟩
      apply hne
      rw [eval_numer]
      rcases hsm.2 with h | h
      · rw [rowQ_eval_zero_Hi hsm.1 h hHi]; simp
      · rw [rowQ_eval_zero_Hi hsm.1 h hHi]; simp
    · -- the per-pole bound
      have hq1 : ¬(c1 ≠ 0 ∧ el p n c1 ≤ i1) := fun h => hsm ⟨h.1, Or.inl h.2⟩
      have hq2 : ¬(c1 ≠ 0 ∧ el p n c1 ≤ i2) := fun h => hsm ⟨h.1, Or.inr h.2⟩
      refine PolyVGe_tauRL_perpole hp5 (PolyVGe_numer c1 i1 c1 i2) (by omega) (fun r hr => ?_) hH
      obtain ⟨c', hc'm, hc'⟩ := exists_sq_class hp2' r
      by_cases hcc' : c' = c1
      · rw [hcc'] at hc'
        have h := VGe_resid_class hM hK hp1 hp2 hr hc1 hc' (VGe_rowQ_class hq1 hc')
          (VGe_rowQ_class hq2 hc')
        refine h.mono ?_
        have hN0 := hyp_ellN0 hM hK hp1 hp2
        have hK0 := ell_eq_zero_class (p := p) (K n)
        simp only [Ecl, wt] at hw1 hw2 ⊢
        by_cases h0 : c1 = 0
        · subst h0
          simp only [↓reduceIte, kap, hN0, hK0] at hw1 hw2 ⊢
          push_cast
          omega
        · have hi1 : i1 < el p n c1 := by by_contra h; exact hq1 ⟨h0, by omega⟩
          have hi2 : i2 < el p n c1 := by by_contra h; exact hq2 ⟨h0, by omega⟩
          simp only [h0, hi1, hi2, ↓reduceIte, kap] at hw1 hw2 ⊢
          push_cast
          omega
      · have : resid (RK (K n)) (numer p n c1 i1 c1 i2) r = 0 := by
          rw [resid, numer_eval_zero hr, zero_div]
          rintro ⟨h1, _⟩
          exact hcc' (sq_class_unique hc'm hc1 (by
            have := dvd_sub hc' (mem_J.1 h1).2
            rw [Int.natCast_natAbs, sq_abs] at this
            rwa [show r ^ 2 - (c' : ℤ) ^ 2 - (r ^ 2 - (c1 : ℤ) ^ 2) = (c1 : ℤ) ^ 2 - (c' : ℤ) ^ 2 by
              ring, ← dvd_neg, neg_sub] at this))
        rw [this]; exact VGe_zero _
  · -- different classes: the entry is a polynomial
    refine (PolyVGe_tauRL_small hp5 (PolyVGe_numer c1 i1 c2 i2) fun r hr hne => ?_).mono
      (by omega)
    exfalso
    apply hne
    refine numer_eval_zero hr fun ⟨h1, h2⟩ => ?_
    exact disjoint_left.1 (J_disjoint hc1 hc2 hcc) h1 h2

end Entries

/-! ### The correction `L` has rank at most `r_p` -/

section Correction

/-- A matrix of values of a `C`-linear map on the products `W b_k b_l`. -/
noncomputable def bil (ψ : ℚ[X] → ℚ[X]) (W : ℚ[X]) {m : ℕ} (b : Fin m → ℚ[X]) :
    Matrix (Fin m) (Fin m) ℚ[X] :=
  Matrix.of fun k l => ψ (W * b k * b l)

omit hp in
theorem bil_change (ψ : ℚ[X] → ℚ[X]) (hadd : ∀ A B, ψ (A + B) = ψ A + ψ B)
    (hC : ∀ c A, ψ (C c * A) = C c * ψ A) (W : ℚ[X]) {m : ℕ} (b : Fin m → ℚ[X])
    (hb : ∀ i, (b i).natDegree < m) :
    bil ψ W b = (coeffMat b).map C * bil ψ W (fun k => X ^ (k : ℕ)) *
      ((coeffMat b).map C).transpose := by
  have h0 : ψ 0 = 0 := by simpa using hC 0 0
  have hsum : ∀ {ι : Type} (s : Finset ι) (A : ι → ℚ[X]), ψ (∑ i ∈ s, A i) = ∑ i ∈ s, ψ (A i) := by
    intro ι s A
    classical
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [sum_insert hi, sum_insert hi, hadd, ih]
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, bil, Matrix.of_apply,
    coeffMat]
  have e : W * b i * b j = ∑ l : Fin m, ∑ k : Fin m, C ((b i).coeff k) * (C ((b j).coeff l) *
      (W * X ^ (k : ℕ) * X ^ (l : ℕ))) := by
    conv_lhs => rw [eq_sum_coeff b hb i, eq_sum_coeff b hb j]
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [e, hsum]
  refine sum_congr rfl fun l _ => ?_
  rw [hsum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [hC, hC]
  ring

omit hp in
/-- `B L Bᵀ = B_S L_{SS} B_Sᵀ` when `L` vanishes outside `S × S`. -/
theorem mul_support {m r : ℕ} (B : Matrix (Fin m) (Fin m) ℚ) (L : Matrix (Fin m) (Fin m) ℚ[X])
    (e : Fin r ↪ Fin m) (hL : ∀ k l, L k l ≠ 0 → k ∈ Set.range e ∧ l ∈ Set.range e) :
    B.map C * L * (B.map C).transpose =
      (B.submatrix id e).map C * L.submatrix e e * ((B.submatrix id e).map C).transpose := by
  have hsum : ∀ (f : Fin m → ℚ[X]), (∀ k, k ∉ Set.range e → f k = 0) →
      ∑ k, f k = ∑ s, f (e s) := by
    intro f hf
    rw [← sum_map univ e f]
    refine (sum_subset (subset_univ _) fun k _ hk => hf k fun ⟨s, hs⟩ => hk ?_).symm
    exact mem_map.2 ⟨s, mem_univ _, hs⟩
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    id]
  rw [hsum (fun l => (∑ k, C (B i k) * L k l) * C (B j l)) fun l hl => ?_]
  · refine sum_congr rfl fun s' _ => ?_
    congr 1
    exact hsum (fun k => C (B i k) * L k (e s')) fun k hk => by
      have : L k (e s') = 0 := by
        by_contra h0; exact hk (hL _ _ h0).1
      simp [this]
  · have : ∀ k, L k l = 0 := fun k => by
      by_contra h0; exact hl (hL _ _ h0).2
    simp [this]

end Correction

/-! ### The class sums -/

section Sums

omit hp in
/-- The weights of an ordinary class with `ℓ ∈ [2, 6]` poles `≤ K` and `δ ∈ {0, 1}` removed. -/
theorem class_sum (ℓ δ : ℕ) (hℓ1 : 2 ≤ ℓ) (hℓ2 : ℓ ≤ 6) (hδ : δ ≤ 1) :
    ∑ i ∈ range (ℓ - δ), (if i < ℓ - 2 then min 0 (2 * (i : ℤ) + 6 * δ - ℓ - 4) else 0) =
      if δ = 0 then -7 * ((ℓ : ℤ) - 2)
      else if ℓ ≤ 4 then -((ℓ : ℤ) - 2) else -2 * ((ℓ : ℤ) - 3) := by
  interval_cases ℓ <;> interval_cases δ <;> simp [sum_range_succ]

omit hp in
theorem class_zeros (ℓ δ : ℕ) (hℓ1 : 2 ≤ ℓ) (hℓ2 : ℓ ≤ 6) (hδ : δ ≤ 1) :
    #((range (ℓ - δ)).filter fun i =>
      (if i < ℓ - 2 then min 0 (2 * (i : ℤ) + 6 * δ - ℓ - 4) else 0) = 0) =
      2 - δ + δ * ((ℓ - 2) / 2) := by
  interval_cases ℓ <;> interval_cases δ <;> decide

omit hp in
theorem zero_class_sum (mK : ℕ) (h1 : 1 ≤ mK) (h2 : mK ≤ 2) :
    ∑ i ∈ range mK, min 0 (4 * (i : ℤ) - 2 * mK + 1) = if mK = 1 then -1 else -3 := by
  interval_cases mK <;> simp [sum_range_succ]

omit hp in
theorem zero_class_zeros (mK : ℕ) (h1 : 1 ≤ mK) (h2 : mK ≤ 2) :
    #((range mK).filter fun i : ℕ => min 0 (4 * (i : ℤ) - 2 * mK + 1) = 0) = mK - 1 := by
  interval_cases mK <;> decide

end Sums

/-! ### Counting classes -/

section Counting

theorem card_min {Nn v m : ℕ} (hN : Nn ≤ m) :
    #((Icc 1 m).filter fun c => c ≤ Nn ∧ c ≤ v) = min Nn v := by
  have : (Icc 1 m).filter (fun c => c ≤ Nn ∧ c ≤ v) = Icc 1 (min Nn v) := by
    ext c; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

theorem card_u {Nn v m : ℕ} (hN : Nn ≤ m) (hvp : v < p) :
    #((Icc 1 m).filter fun c => c ≤ Nn ∧ p - c ≤ v) = Nn + 1 - (p - v) := by
  have : (Icc 1 m).filter (fun c => c ≤ Nn ∧ p - c ≤ v) = Icc (p - v) Nn := by
    ext c; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]

end Counting

/-! ### Class sizes under (4.9) -/

section Sizes

variable {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < 3 * p) (hp2 : p ≤ K n)
include hM hK hp1 hp2

theorem Lr_eq {c : ℕ} :
    (Lr p n c : ℤ) = Inner.ell p (K n) c - Inner.ell p (N n) c := by
  have := ell_eq_add_card_J (p := p) (c := c) (show N n ≤ K n by simp only [N, K]; omega)
  simp only [Lr]; omega

theorem Lr_zero : Lr p n 0 = K n / p := by
  have h := Lr_eq hM hK hp1 hp2 (c := 0)
  rw [hyp_ellN0 hM hK hp1 hp2, ell_eq_zero_class] at h
  omega

theorem ell_p {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) : Inner.ell p p c = 2 := by
  have hp0 : 0 < p := by have := hyp_p5 hM hK hp1 hp2; omega
  rw [ell_exact (hyp_p2 hM hK hp1 hp2) hc hcm, Nat.div_self hp0, Nat.mod_self]
  have : ¬ p - c ≤ 0 := by omega
  simp [this, show ¬ c ≤ 0 by omega]

theorem el_eq {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    (el p n c : ℤ) = Inner.ell p (K n) c - 2 := by
  have hN := hyp_N_lt hM hK hp1 hp2
  have hHi : Hi p n c = J p p (K n) c := by
    ext j; simp only [Hi, mem_filter, mem_J]; omega
  have := ell_eq_add_card_J (p := p) (Nn := p) (Kn := K n) (c := c) hp2
  rw [ell_p hM hK hp1 hp2 hc hcm, ← hHi] at this
  simp only [el]; omega

/-- `ℓ_K(c) = 2m_K + [c ≤ v] + [p - c ≤ v]`. -/
theorem ell_K {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    Inner.ell p (K n) c = 2 * (K n / p) + (if c ≤ K n % p then 1 else 0) +
      (if p - c ≤ K n % p then 1 else 0) :=
  ell_exact (hyp_p2 hM hK hp1 hp2) hc hcm

theorem class_T {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    ∑ i ∈ range (Lr p n c), wt p n c i =
      if Inner.ell p (N n) c = 0 then -7 * ((Inner.ell p (K n) c : ℤ) - 2)
      else if Inner.ell p (K n) c ≤ 4 then -((Inner.ell p (K n) c : ℤ) - 2)
      else -2 * ((Inner.ell p (K n) c : ℤ) - 3) := by
  have hL := Lr_eq hM hK hp1 hp2 (c := c)
  have he := el_eq hM hK hp1 hp2 hc hcm
  have hδ := hyp_ellN hM hK hp1 hp2 hc hcm
  have hℓ := ell_K hM hK hp1 hp2 hc hcm
  have hmK := hyp_mK hM hK hp1 hp2
  have hℓ1 : 2 ≤ Inner.ell p (K n) c := by rw [hℓ]; omega
  have hℓ2 : Inner.ell p (K n) c ≤ 6 := by rw [hℓ]; split_ifs <;> omega
  have hδ1 : Inner.ell p (N n) c ≤ 1 := by rw [hδ]; split_ifs <;> omega
  have := class_sum _ _ hℓ1 hℓ2 hδ1
  rw [show Lr p n c = Inner.ell p (K n) c - Inner.ell p (N n) c by omega, ← this]
  refine sum_congr rfl fun i _ => ?_
  simp only [wt, show c ≠ 0 by omega, ↓reduceIte, show el p n c = Inner.ell p (K n) c - 2 by omega]

theorem class_Z {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    #((range (Lr p n c)).filter fun i => wt p n c i = 0) =
      2 - Inner.ell p (N n) c + Inner.ell p (N n) c * ((Inner.ell p (K n) c - 2) / 2) := by
  have hL := Lr_eq hM hK hp1 hp2 (c := c)
  have he := el_eq hM hK hp1 hp2 hc hcm
  have hδ := hyp_ellN hM hK hp1 hp2 hc hcm
  have hℓ := ell_K hM hK hp1 hp2 hc hcm
  have hmK := hyp_mK hM hK hp1 hp2
  have hℓ1 : 2 ≤ Inner.ell p (K n) c := by rw [hℓ]; omega
  have hℓ2 : Inner.ell p (K n) c ≤ 6 := by rw [hℓ]; split_ifs <;> omega
  have hδ1 : Inner.ell p (N n) c ≤ 1 := by rw [hδ]; split_ifs <;> omega
  have := class_zeros _ _ hℓ1 hℓ2 hδ1
  rw [show Lr p n c = Inner.ell p (K n) c - Inner.ell p (N n) c by omega, ← this]
  congr 1
  refine filter_congr fun i _ => ?_
  simp only [wt, show c ≠ 0 by omega, ↓reduceIte, show el p n c = Inner.ell p (K n) c - 2 by omega]

theorem zero_T : ∑ i ∈ range (Lr p n 0), wt p n 0 i = if K n / p = 1 then -1 else -3 := by
  have hmK := hyp_mK hM hK hp1 hp2
  rw [Lr_zero hM hK hp1 hp2, ← zero_class_sum _ hmK.1 hmK.2]
  simp [wt]

theorem zero_Z : #((range (Lr p n 0)).filter fun i => wt p n 0 i = 0) = K n / p - 1 := by
  have hmK := hyp_mK hM hK hp1 hp2
  rw [Lr_zero hM hK hp1 hp2, ← zero_class_zeros _ hmK.1 hmK.2]
  simp [wt]

end Sizes

/-! ### Proposition 4.3 -/

section Final

omit hp in
/-- Sums over the rows in the order of `finSigmaFinEquiv`. -/
theorem sum_rows {β : Type*} [AddCommMonoid β] {k H : ℕ} {L : ℕ → ℕ}
    (h : ∑ c : Fin (k + 1), L c = H) (f : ℕ → ℕ → β) :
    ∑ j : Fin H, f ((finSigmaFinEquiv.trans (finCongr h)).symm j).1
        ((finSigmaFinEquiv.trans (finCongr h)).symm j).2 =
      ∑ c ∈ range (k + 1), ∑ i ∈ range (L c), f c i := by
  rw [Equiv.sum_comp (finSigmaFinEquiv.trans (finCongr h)).symm
    (fun x : (Σ c : Fin (k + 1), Fin (L c)) => f x.1 x.2), Fintype.sum_sigma,
    Fin.sum_univ_eq_sum_range (fun c => ∑ i : Fin (L c), f c i) (k + 1)]
  exact sum_congr rfl fun c _ => Fin.sum_univ_eq_sum_range (fun i => f c i) (L c)

/-- The rows `(c, i)`, `c ≤ m`, `i < #J_c`. -/
abbrev Row (p n : ℕ) := Σ c : Fin ((p - 1) / 2 + 1), Fin (Lr p n c)

variable {n : ℕ}

/-- The rows in the order of `finSigmaFinEquiv`. -/
def rowEquiv (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) : Row p n ≃ Fin (dim n) :=
  finSigmaFinEquiv.trans (finCongr h)

/-- The basis (4.11) over `ℤ`. -/
noncomputable def basZ (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) (k : Fin (dim n)) :
    ℤ[X] :=
  rowZ p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2

theorem rho_inj :
    Function.Injective fun c : Fin ((p - 1) / 2 + 1) => -(((c : ℕ) : ZMod p) ^ 2) := by
  intro c c' h
  simp only [neg_inj] at h
  have h' : (((c : ℕ) : ℤ) ^ 2 - ((c' : ℕ) : ℤ) ^ 2 : ℤ) = (0 : ZMod p) := by
    push_cast; rw [h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  exact Fin.ext (sq_class_unique (Nat.lt_succ_iff.1 c.2) (Nat.lt_succ_iff.1 c'.2) h')

/-- `ψ(A) = C(τ_high(pull A /ₘ ∏_{R_K}))`: the entries of the correction `L`. -/
noncomputable def psiH (p n : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C (tauHigh p ((pull (Icc 1 (K n)) A) /ₘ poleProd (RK (K n))))

omit hp in
theorem psiH_add (A B : ℚ[X]) : psiH p n (A + B) = psiH p n A + psiH p n B := by
  simp only [psiH, pull_add, add_divByMonic, tauHigh_add, C_add]

omit hp in
theorem psiH_C_mul (c : ℚ) (A : ℚ[X]) : psiH p n (C c * A) = C c * psiH p n A := by
  have : pull (Icc 1 (K n)) (C c * A) = C c * pull (Icc 1 (K n)) A := by
    rw [← smul_eq_C_mul, pull_smul, smul_eq_C_mul]
  simp only [psiH, this]
  rw [← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul, tauHigh_C_mul, C_mul]

variable {M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < 3 * p) (hp2 : p ≤ K n)
include hM hK hp1 hp2

theorem sum_Lr_fin : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n := by
  rw [Fin.sum_univ_eq_sum_range (fun c => Lr p n c), sum_Lr (hyp_p2 hM hK hp1 hp2)]
  simp only [K, N, dim]; omega

theorem basZ_natDegree (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) (k : Fin (dim n)) :
    (basZ h k).natDegree < dim n := by
  have hL : Lr p n ((rowEquiv h).symm k).1 ≤ K n - N n := by
    have := sum_Lr (n := n) (hyp_p2 hM hK hp1 hp2)
    rw [← this]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 ((rowEquiv h).symm k).1.2)
  rw [basZ, natDegree_rowZ]
  have := ((rowEquiv h).symm k).2.2
  simp only [dim, K, N] at hL this ⊢
  omega

theorem basZ_independent (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    LinearIndependent (ZMod p) fun k => (basZ h k).map (Int.castRingHom (ZMod p)) := by
  simp_rw [basZ, map_rowZ (hyp_p2 hM hK hp1 hp2)]
  exact (crtRow_linearIndependent _ rho_inj _).comp _ (rowEquiv h).symm.injective

/-- `r_p ≤ h`. -/
theorem rN_le : (Outer.r p n).toNat ≤ dim n := by
  have := hyp_5N hM hK hp1 hp2
  simp only [Outer.r, dim, K, N] at this ⊢
  omega

/-- `L_{kl} = 0` unless `k, l ≥ h - r_p`: the polynomial part has degree `≤ 4p - 2`. -/
theorem psiH_mono_eq_zero {k l : ℕ} (hk : k < dim n) (hl : l < dim n)
    (hkl : k < dim n - (Outer.r p n).toNat ∨ l < dim n - (Outer.r p n).toNat) :
    psiH p n (D (N n) ^ 6 * X ^ k * X ^ l) = 0 := by
  have h5 := hyp_5N hM hK hp1 hp2
  rw [psiH, tauHigh_eq_zero, C_0]
  rw [natDegree_divByMonic _ (poleProd_monic _), natDegree_poleProd, card_RK]
  have h1 := Inner.natDegree_pull_le (Icc 1 (K n)) (D (N n) ^ 6 * X ^ k * X ^ l)
  have h2 : (D (N n) ^ 6 * X ^ k * X ^ l).natDegree ≤ 6 * N n + k + l := by
    refine natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans (add_le_add
      (natDegree_pow_le.trans (by rw [natDegree_D])) (natDegree_X_pow_le _)))
      (natDegree_X_pow_le _))
  simp only [Outer.r, dim, K, N] at h1 h2 h5 hk hl hkl ⊢
  omega

end Final

/-! ### Assembly -/

section Assembly

variable {n : ℕ}

/-- The basis (4.11) over `ℚ`. -/
noncomputable def basQ (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) (k : Fin (dim n)) :
    ℚ[X] :=
  (basZ h k).map (Int.castRingHom ℚ)

/-- The corrected Gram matrix `A`. -/
noncomputable def Amat (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    Matrix (Fin (dim n)) (Fin (dim n)) ℚ[X] :=
  Matrix.of fun k l => tauRL p (RK (K n)) (numer p n ((rowEquiv h).symm k).1
    ((rowEquiv h).symm k).2 ((rowEquiv h).symm l).1 ((rowEquiv h).symm l).2)

/-- The last `r` indices. -/
def emb {r H : ℕ} (hr : r ≤ H) : Fin r ↪ Fin H :=
  ⟨fun s => ⟨H - r + s, by have := s.2; omega⟩, fun s s' h => by
    simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

theorem gram_eq (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    gram (D (N n) ^ 6) (Icc 1 (K n)) (basQ h) =
      Amat h + C ((p : ℚ)⁻¹) • bil (psiH p n) (D (N n) ^ 6) (basQ h) := by
  ext k l : 1
  simp only [gram, bil, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Amat,
    psiH, numer, rowQ, basQ, basZ]
  rw [muX_eq_tauR _ _ (by simp), poleSet_Icc, tauR_eq_tauRL (p := p), C_mul]

variable {M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < 3 * p) (hp2 : p ≤ K n)
include hM hK hp1 hp2

theorem basQ_natDegree (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) (k : Fin (dim n)) :
    (basQ h k).natDegree < dim n := by
  rw [basQ, natDegree_map_eq_of_injective (RingHom.injective_int _)]
  exact basZ_natDegree hM hK hp1 hp2 h k

theorem bil_factor (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    bil (psiH p n) (D (N n) ^ 6) (basQ h) =
      ((coeffMat (basQ h)).submatrix id (emb (rN_le hM hK hp1 hp2))).map C *
        (bil (psiH p n) (D (N n) ^ 6) fun k : Fin (dim n) => X ^ (k : ℕ)).submatrix
          (emb (rN_le hM hK hp1 hp2)) (emb (rN_le hM hK hp1 hp2)) *
        (((coeffMat (basQ h)).submatrix id (emb (rN_le hM hK hp1 hp2))).map C).transpose := by
  rw [← mul_support _ _ _ fun k l hkl => ?_]
  · exact bil_change _ psiH_add psiH_C_mul _ _ (basQ_natDegree hM hK hp1 hp2 h)
  · have hrN := rN_le hM hK hp1 hp2
    by_contra hne
    simp only [Set.mem_range, not_and_or, not_exists] at hne
    apply hkl
    simp only [bil, Matrix.of_apply]
    refine psiH_mono_eq_zero hM hK hp1 hp2 k.2 l.2 ?_
    rcases hne with h' | h'
    · left; by_contra hk
      exact h' ⟨(k : ℕ) - (dim n - (Outer.r p n).toNat), by omega⟩
        (Fin.ext (show dim n - (Outer.r p n).toNat + ((k : ℕ) - (dim n - (Outer.r p n).toNat)) =
          (k : ℕ) by omega))
    · right; by_contra hl
      exact h' ⟨(l : ℕ) - (dim n - (Outer.r p n).toNat), by omega⟩
        (Fin.ext (show dim n - (Outer.r p n).toNat + ((l : ℕ) - (dim n - (Outer.r p n).toNat)) =
          (l : ℕ) by omega))

theorem PolyVGe_bil_mono (k l : Fin (dim n)) :
    PolyVGe p 0 (bil (psiH p n) (D (N n) ^ 6) (fun k : Fin (dim n) => X ^ (k : ℕ)) k l) := by
  have hp5 := hyp_p5 hM hK hp1 hp2
  simp only [bil, Matrix.of_apply, psiH]
  refine PolyVGe_C (VGe_tauHigh hp5 (PolyVGe_divByMonic (PolyVGe_pull _ ?_)
    (PolyVGe_poleProd _) (poleProd_monic _)))
  have := ((PolyVGe_D (p := p) (N n)).pow 6).mul (((PolyVGe_X (p := p)).pow (k : ℕ)).mul
    ((PolyVGe_X (p := p)).pow (l : ℕ)))
  simp only [mul_zero, add_zero] at this
  rwa [← mul_assoc] at this

theorem VGe_coeff_basQ (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) (k : Fin (dim n))
    (i : ℕ) : VGe p 0 ((basQ h k).coeff i) := by
  rw [basQ, coeff_map, eq_intCast]
  exact VGe_intCast _

/-- Lemma 4.2 applied to the basis (4.11). -/
theorem det_bound (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    PolyVGe p (∑ k, wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 -
        min ((Outer.r p n).toNat : ℤ)
          (#{k | wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 = 0} : ℕ))
      (gram (D (N n) ^ 6) (Icc 1 (K n)) (basQ h)).det := by
  have hp5 := hyp_p5 hM hK hp1 hp2
  rw [gram_eq, bil_factor hM hK hp1 hp2]
  refine lemma42 _ _ _ _ (fun k => wt_nonpos _ _ _ _) (fun k l => ?_) (fun k s => ?_)
    (fun s s' => ?_)
  · exact entry_bound hM hK hp1 hp2 (Nat.lt_succ_iff.1 ((rowEquiv h).symm k).1.2)
      (Nat.lt_succ_iff.1 ((rowEquiv h).symm l).1.2)
  · exact VGe_coeff_basQ hM hK hp1 hp2 h k _
  · exact PolyVGe_bil_mono hM hK hp1 hp2 _ _

/-! ### Comparison with `γ_p^out` -/

/-- Per ordinary class: `T_c` and a bound for `Z_c`, with `δ_c = [c ≤ N]`, `b_c = [p - c ≤ v]`. -/
theorem class_facts {c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ (p - 1) / 2) :
    (∑ i ∈ range (Lr p n c), wt p n c i =
      -7 * (Inner.ell p (K n) c : ℤ) + 14 +
        (if K n / p = 1 then 6 else 5) * ((if c ≤ N n then 1 else 0) * (Inner.ell p (K n) c : ℤ)) +
          (if K n / p = 1 then -12 else -8) * (if c ≤ N n then 1 else 0)) ∧
    ((#((range (Lr p n c)).filter fun i => wt p n c i = 0) : ℕ) : ℤ) ≤
      2 + ((K n / p : ℕ) - 2 : ℤ) * (if c ≤ N n then 1 else 0) +
        (if c ≤ N n then 1 else 0) * (if p - c ≤ K n % p then 1 else 0) := by
  have hT := class_T hM hK hp1 hp2 hc hcm
  have hZ := class_Z hM hK hp1 hp2 hc hcm
  have hδ := hyp_ellN hM hK hp1 hp2 hc hcm
  have hℓ := ell_K hM hK hp1 hp2 hc hcm
  have hmK := hyp_mK hM hK hp1 hp2
  rw [hT, hZ, hδ, hℓ]
  have hmK' : K n / p = 1 ∨ K n / p = 2 := by omega
  constructor
  · rcases hmK' with h | h <;> rw [h] <;> split_ifs <;> push_cast <;> omega
  · rcases hmK' with h | h <;> rw [h] <;> split_ifs <;> push_cast

theorem gamma_le (h : ∑ c : Fin ((p - 1) / 2 + 1), Lr p n c = dim n) :
    gammaOut p n ≤ ∑ k, wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 -
      min ((Outer.r p n).toNat : ℤ)
        (#{k | wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 = 0} : ℕ) := by
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hmK := hyp_mK hM hK hp1 hp2
  have htwo := hyp_two_m hM hK hp1 hp2
  have hNm := hyp_N_le_m hM hK hp1 hp2
  have hNp := hyp_N_lt hM hK hp1 hp2
  have hp0 : 0 < p := by have := hyp_p5 hM hK hp1 hp2; omega
  have hvp : K n % p < p := Nat.mod_lt _ hp0
  have hKv : K n = p * (K n / p) + K n % p := (Nat.div_add_mod _ _).symm
  set S := Icc 1 ((p - 1) / 2)
  have hcard : #S = (p - 1) / 2 := by simp [S]
  -- the sums over the rows
  have hS : ∑ k, wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 =
      ∑ i ∈ range (Lr p n 0), wt p n 0 i + ∑ c ∈ S, ∑ i ∈ range (Lr p n c), wt p n c i := by
    rw [rowEquiv, sum_rows h (wt p n), sum_range_succ', add_comm]
    congr 1
    exact Inner.sum_range_shift (fun c => ∑ i ∈ range (Lr p n c), wt p n c i) _
  have hZ : ((#{k | wt p n ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 = 0} : ℕ) : ℤ) =
      ((#((range (Lr p n 0)).filter fun i => wt p n 0 i = 0) : ℕ) : ℤ) +
        ∑ c ∈ S, ((#((range (Lr p n c)).filter fun i => wt p n c i = 0) : ℕ) : ℤ) := by
    have e := sum_rows (β := ℤ) h fun c i => if wt p n c i = 0 then 1 else 0
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    simp only [Nat.cast_one]
    rw [← rowEquiv] at e
    rw [e, sum_range_succ', add_comm]
    congr 1
    · simp [sum_boole]
    · rw [← Inner.sum_range_shift (fun c => ((#((range (Lr p n c)).filter
        fun i => wt p n c i = 0) : ℕ) : ℤ)) _]
      refine sum_congr rfl fun c _ => ?_
      simp [sum_boole]
  have hcls := fun c (hc : c ∈ S) =>
    class_facts hM hK hp1 hp2 (mem_Icc.1 hc).1 (mem_Icc.1 hc).2
  -- the class sums
  have hsumℓ := sum_ell_classes (p := p) hp2' (K n)
  have hsumδ := sum_ell_classes (p := p) hp2' (N n)
  rw [Nat.div_eq_of_lt (by omega : N n < p), Nat.sub_zero] at hsumδ
  have hδeq : ∀ c ∈ S, Inner.ell p (N n) c = if c ≤ N n then 1 else 0 :=
    fun c hc => hyp_ellN hM hK hp1 hp2 (mem_Icc.1 hc).1 (mem_Icc.1 hc).2
  have hℓeq : ∀ c ∈ S, Inner.ell p (K n) c = 2 * (K n / p) +
      (if c ≤ K n % p then 1 else 0) + (if p - c ≤ K n % p then 1 else 0) :=
    fun c hc => ell_K hM hK hp1 hp2 (mem_Icc.1 hc).1 (mem_Icc.1 hc).2
  have hA1 : ∑ c ∈ S, (Inner.ell p (K n) c : ℤ) = K n - (K n / p : ℕ) := by
    rw [← Nat.cast_sum, show S = Inner.classes p from rfl, hsumℓ,
      Nat.cast_sub (Nat.div_le_self _ _)]
  have hA2 : ∑ c ∈ S, (if c ≤ N n then 1 else 0 : ℤ) = N n := by
    calc ∑ c ∈ S, (if c ≤ N n then 1 else 0 : ℤ)
        = ∑ c ∈ Inner.classes p, (Inner.ell p (N n) c : ℤ) :=
          sum_congr rfl fun c hc => by rw [hδeq c hc]; split_ifs <;> simp
      _ = N n := by exact_mod_cast hsumδ
  have hA4 : ∑ c ∈ S, ((if c ≤ N n then 1 else 0 : ℤ) *
      (if p - c ≤ K n % p then 1 else 0)) = ((N n + 1 - (p - K n % p) : ℕ) : ℤ) := by
    rw [← card_u hNm hvp, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl fun c _ => ?_
    by_cases h1 : c ≤ N n <;> by_cases h2 : p - c ≤ K n % p <;> simp [h1, h2]
  have hA5 : ∑ c ∈ S, ((if c ≤ N n then 1 else 0 : ℤ) *
      (if c ≤ K n % p then 1 else 0)) = (min (N n) (K n % p) : ℕ) := by
    rw [← card_min hNm, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl fun c _ => ?_
    by_cases h1 : c ≤ N n <;> by_cases h2 : c ≤ K n % p <;> simp [h1, h2]
  have hA3 : ∑ c ∈ S, ((if c ≤ N n then 1 else 0 : ℤ) * (Inner.ell p (K n) c : ℤ)) =
      2 * (K n / p : ℕ) * N n + (min (N n) (K n % p) : ℕ) +
        ((N n + 1 - (p - K n % p) : ℕ) : ℤ) := by
    rw [← hA4, ← hA5, ← hA2, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c hc => ?_
    rw [hℓeq c hc]; push_cast; ring
  -- `∑ T_c`
  have hT : ∑ c ∈ S, ∑ i ∈ range (Lr p n c), wt p n c i =
      -7 * (K n - (K n / p : ℕ) : ℤ) + 14 * ((p - 1) / 2 : ℕ) +
        (if K n / p = 1 then 6 else 5) * (2 * (K n / p : ℕ) * N n + (min (N n) (K n % p) : ℕ) +
          ((N n + 1 - (p - K n % p) : ℕ) : ℤ)) + (if K n / p = 1 then -12 else -8) * N n := by
    rw [sum_congr rfl fun c hc => (hcls c hc).1, sum_add_distrib, sum_add_distrib,
      sum_add_distrib, sum_const, hcard, nsmul_eq_mul, ← mul_sum, ← mul_sum, ← mul_sum, hA1, hA3,
      hA2]
    push_cast; ring
  -- `∑ Z_c`
  have hZc : ∑ c ∈ S, ((#((range (Lr p n c)).filter fun i => wt p n c i = 0) : ℕ) : ℤ) ≤
      2 * ((p - 1) / 2 : ℕ) + (((K n / p : ℕ) : ℤ) - 2) * N n +
        ((N n + 1 - (p - K n % p) : ℕ) : ℤ) := by
    refine (sum_le_sum fun c hc => (hcls c hc).2).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_add_distrib, sum_const, hcard, nsmul_eq_mul, ← mul_sum, hA2, hA4]
    push_cast; ring
  have hZ0 := zero_Z hM hK hp1 hp2 (n := n)
  have hT0 := zero_T hM hK hp1 hp2 (n := n)
  rw [hS, hZ, hT0, hT]
  simp only [gammaOut, show ¬ K n < p by omega, ↓reduceIte, Outer.t, Outer.u, Outer.v, Outer.r]
  rcases (show K n / p = 1 ∨ K n / p = 2 by omega) with hm | hm
  · rw [hm] at hKv hZ0 hZc ⊢
    have hK2 : K n < 2 * p := by omega
    simp only [hK2, ↓reduceIte] at ⊢
    push_cast at hZ0 hZc ⊢
    clear hS hZ hcls hδeq hℓeq hA1 hA2 hA3 hA4 hA5 hT hsumℓ hsumδ
    omega
  · rw [hm] at hKv hZ0 hZc ⊢
    have hK2 : ¬ K n < 2 * p := by omega
    simp only [hK2, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at ⊢
    push_cast at hZ0 hZc ⊢
    clear hS hZ hcls hδeq hℓeq hA1 hA2 hA3 hA4 hA5 hT hsumℓ hsumδ
    omega

/-- **Proposition 4.3**, first part: `v_p^G(Δ_K) ≥ γ_p^out`. -/
theorem outer_bound' : PolyVGe p (gammaOut p n) (Δ n) := by
  have hsum := sum_Lr_fin hM hK hp1 hp2
  obtain ⟨h0, hB⟩ := unimodular_of_independent (p := p) (basZ hsum)
    (basZ_natDegree hM hK hp1 hp2 hsum) (basZ_independent hM hK hp1 hp2 hsum)
  exact PolyVGe_Δ_of_gram (basQ hsum) (basQ_natDegree hM hK hp1 hp2 hsum) h0 hB
    ((det_bound hM hK hp1 hp2 hsum).mono (gamma_le hM hK hp1 hp2 hsum))

end Assembly

end Outer

end Zeta5
