/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Algebra.Ring.GeomSum
import Zeta5.PBound
import Zeta5.Tau

/-!
# Local integrality of `τ_X`

Tools for the estimates of §4 at a fixed prime `p ≥ 5`:

* the subring `ℤ_(p) ∩ ℚ`, with divisibility of values `P(a) - P(b)` by `a - b` and integrality of
  quotients by monic integral polynomials;
* von Staudt–Clausen for `κ_d = d(d-1)(d-2) B_{d-3} / 24`: `v_p(κ_d) ≥ -1`, and `κ_d` is
  `p`-integral for `d ≤ 4p - 2` (so `μ(t^e)` is integral for `e < 2p - 3`, as in §4.2);
* the harmonic numbers: `H⁽⁵⁾_m ≡ H⁽⁵⁾_{p-1-m} (mod p)` for `m < p`;
* the divided difference at two poles `r ≡ r' (mod p)`.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The subring `ℤ_(p) ∩ ℚ` -/

/-- The rationals with `v_p ≥ 0`. -/
def Zp (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | VGe p 0 x}
  mul_mem' ha hb := by simpa using VGe.mul ha hb
  one_mem' := VGe_one
  add_mem' := VGe.add
  zero_mem' := VGe_zero 0
  neg_mem' := VGe.neg

theorem mem_Zp {x : ℚ} : x ∈ Zp p ↔ VGe p 0 x := Iff.rfl

theorem coeffs_subset_Zp {P : ℚ[X]} (h : PolyVGe p 0 P) : (↑P.coeffs : Set ℚ) ⊆ Zp p := by
  intro x hx
  obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hx
  exact h n

/-- `a ≡ b (mod p^w)` implies `P(a) ≡ P(b) (mod p^w)` for `P` with integral coefficients. -/
theorem VGe_eval_sub {P : ℚ[X]} (hP : PolyVGe p 0 P) {a b : ℚ} (ha : VGe p 0 a) (hb : VGe p 0 b)
    {w : ℤ} (hab : VGe p w (a - b)) : VGe p w (P.eval a - P.eval b) := by
  set P' := P.toSubring (Zp p) (coeffs_subset_Zp hP)
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub (⟨a, ha⟩ : Zp p) ⟨b, hb⟩ P'
  have hev : ∀ x : Zp p, P.eval (x : ℚ) = ((P'.eval x : Zp p) : ℚ) := fun x => by
    conv_lhs => rw [← map_toSubring P (Zp p) (coeffs_subset_Zp hP)]
    exact eval_map_apply (f := (Zp p).subtype) x
  have : P.eval a - P.eval b = (a - b) * c := by
    have h := congrArg Subtype.val hc
    rw [hev ⟨a, ha⟩, hev ⟨b, hb⟩]
    simpa using h
  rw [this]
  simpa using hab.mul c.2

theorem VGe_inv_int {z : ℤ} (hz : ¬(p : ℤ) ∣ z) : VGe p 0 ((z : ℚ)⁻¹) := by
  refine VGe_of_padicValRat fun _ => ?_
  rw [padicValRat.inv, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  simp

theorem PolyVGe_intCast_poly (P : ℤ[X]) : PolyVGe p 0 (P.map (Int.castRingHom ℚ)) := fun i => by
  rw [coeff_map]; exact VGe_intCast _

theorem PolyVGe_poleProd (R : Finset ℤ) : PolyVGe p 0 (poleProd R) := by
  refine (PolyVGe_prod R fun r _ => PolyVGe_X.sub (PolyVGe_C (VGe_intCast r))).mono ?_
  simp

theorem PolyVGe_divByMonic {N M : ℚ[X]} (hN : PolyVGe p 0 N) (hM : PolyVGe p 0 M) (hm : M.Monic) :
    PolyVGe p 0 (N /ₘ M) := by
  set N' := N.toSubring (Zp p) (coeffs_subset_Zp hN)
  set M' := M.toSubring (Zp p) (coeffs_subset_Zp hM)
  have hm' : M'.Monic := (monic_toSubring _ _ _).2 hm
  have : N /ₘ M = (N' /ₘ M').map (Zp p).subtype := by
    rw [map_divByMonic _ hm', map_toSubring, map_toSubring]
  intro i
  rw [this, coeff_map]
  exact ((N' /ₘ M').coeff i).2

theorem PolyVGe_tauR {R : Finset ℤ} {N : ℚ[X]} {w : ℤ} (h1 : VGe p w (tauConst R N))
    (h2 : VGe p w (tauRes R N)) : PolyVGe p w (tauR R N) :=
  (PolyVGe_C h1).sub ((PolyVGe_C h2).mul PolyVGe_X |>.mono (by simp))

theorem taup_C (c : ℚ) : taup (C c) = 0 := by
  simp [taup_apply]

theorem VGe_eval {P : ℚ[X]} (hP : PolyVGe p 0 P) {a : ℚ} (ha : VGe p 0 a) :
    VGe p 0 (P.eval a) := by
  rw [eval_eq_sum_range]
  refine VGe_sum _ fun i _ => ?_
  simpa using (hP i).mul (ha.pow i)

theorem VGe_of_dvd_int {z : ℤ} (h : (p : ℤ) ∣ z) : VGe p 1 (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  simpa using (VGe_p_pow (p := p) 1).mul (VGe_intCast (p := p) c)

theorem VGe_inv_of_not_sq_dvd {z : ℤ} (_hz : z ≠ 0) (h : ¬(p : ℤ) ^ 2 ∣ z) :
    VGe p (-1) ((z : ℚ)⁻¹) := by
  refine VGe_of_padicValRat fun _ => ?_
  rw [padicValRat.inv, padicValRat.of_int]
  have : ¬ 2 ≤ padicValInt p z := fun h2 => h ((padicValInt_dvd_iff 2 z).2 (Or.inr h2))
  omega

/-- `p ∣ d`, `0 < |d| < 2p` force `d = ±p`. -/
theorem eq_of_dvd_of_natAbs_lt {d : ℤ} (h : (p : ℤ) ∣ d) (hd : d.natAbs < 2 * p) (h0 : d ≠ 0) :
    d = p ∨ d = -p := by
  obtain ⟨c, rfl⟩ := h
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hc0 : c ≠ 0 := by rintro rfl; simp at h0
  have hd' : |(p : ℤ) * c| < 2 * p := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hd
  rw [abs_mul, abs_of_pos hp0] at hd'
  have : |c| < 2 := by nlinarith
  rcases abs_lt.1 this with ⟨h1, h2⟩
  have : c = 1 ∨ c = -1 := by omega
  rcases this with rfl | rfl <;> simp

/-- A residue at a pole `r` that is `p`-adically isolated is integral. -/
theorem VGe_resid_isolated {R : Finset ℤ} {N : ℚ[X]} (hN : PolyVGe p 0 N) {r : ℤ} (hr : r ∈ R)
    (hiso : ∀ s ∈ R, s ≠ r → ¬(p : ℤ) ∣ (r - s)) : VGe p 0 (resid R N r) := by
  rw [resid, eval_derivative_poleProd hr, poleProd, eval_prod, div_eq_mul_inv, ← prod_inv_distrib]
  have h := VGe_prod (p := p) (R.erase r) (w := fun _ => 0)
    (f := fun s => (eval (r : ℚ) (X - C (s : ℚ)))⁻¹) fun s hs => by
      simp only [eval_sub, eval_X, eval_C]
      have := VGe_inv_int (p := p) (hiso s (mem_of_mem_erase hs) (ne_of_mem_erase hs))
      push_cast at this
      exact this
  simp only [sum_const_zero] at h
  simpa using (VGe_eval hN (VGe_intCast r)).mul h

/-- The divided difference: at two poles `r ≡ r' (mod p)` with `v_p(r - r') = 1`, isolated from
the other poles, `Res_r · φ + Res_{r'} · φ'` is integral when `φ ≡ φ' (mod p)`. -/
theorem VGe_resid_pair {R : Finset ℤ} {N : ℚ[X]} (hN : PolyVGe p 0 N) {r r' : ℤ} (hr : r ∈ R)
    (hr' : r' ∈ R) (hne : r ≠ r') (hdvd : (p : ℤ) ∣ (r - r')) (hsq : ¬(p : ℤ) ^ 2 ∣ (r - r'))
    (hiso : ∀ s ∈ R, s ≠ r → s ≠ r' → ¬(p : ℤ) ∣ (r - s)) {φ φ' : ℚ} (hφ : VGe p 0 φ)
    (hφ' : VGe p 0 φ') (hφφ : VGe p 1 (φ - φ')) :
    VGe p 0 (resid R N r * φ + resid R N r' * φ') := by
  set R'' := (R.erase r).erase r'
  have hr'e : r' ∈ R.erase r := mem_erase.2 ⟨hne.symm, hr'⟩
  have hre : r ∈ R.erase r' := mem_erase.2 ⟨hne, hr⟩
  have e1 : (derivative (poleProd R)).eval (r : ℚ) =
      ((r : ℚ) - r') * (poleProd R'').eval (r : ℚ) := by
    rw [eval_derivative_poleProd hr, poleProd_eq_mul_erase hr'e, eval_mul]; simp [R'']
  have e2 : (derivative (poleProd R)).eval (r' : ℚ) =
      ((r' : ℚ) - r) * (poleProd R'').eval (r' : ℚ) := by
    rw [eval_derivative_poleProd hr', poleProd_eq_mul_erase hre, eval_mul, erase_right_comm]
    simp [R'']
  set V := poleProd R''
  have hunit : ∀ y : ℤ, (∀ s ∈ R'', ¬(p : ℤ) ∣ (y - s)) → VGe p 0 ((V.eval (y : ℚ))⁻¹) := by
    intro y hy
    rw [show V = poleProd R'' from rfl, poleProd, eval_prod, ← prod_inv_distrib]
    have h := VGe_prod (p := p) R'' (w := fun _ => 0)
      (f := fun s => (eval (y : ℚ) (X - C (s : ℚ)))⁻¹) fun s hs => by
        simp only [eval_sub, eval_X, eval_C]
        have := VGe_inv_int (p := p) (hy s hs)
        push_cast at this
        exact this
    simpa using h
  have hiso' : ∀ s ∈ R'', ¬(p : ℤ) ∣ (r - s) := fun s hs => by
    simp only [R'', mem_erase] at hs
    exact hiso s hs.2.2 hs.2.1 hs.1
  have hiso'' : ∀ s ∈ R'', ¬(p : ℤ) ∣ (r' - s) := fun s hs h => hiso' s hs (by
    have : r - s = (r - r') + (r' - s) := by ring
    rw [this]; exact dvd_add hdvd h)
  have hV : V.eval (r : ℚ) ≠ 0 := by
    intro h0; have := hunit r hiso'; rw [h0, inv_zero] at this
    rw [show V = poleProd R'' from rfl, poleProd, eval_prod] at h0
    obtain ⟨s, hs, hs0⟩ := prod_eq_zero_iff.1 h0
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
    exact hiso' s hs (by rw [show r = s by exact_mod_cast hs0]; simp)
  have hV' : V.eval (r' : ℚ) ≠ 0 := by
    intro h0
    rw [show V = poleProd R'' from rfl, poleProd, eval_prod] at h0
    obtain ⟨s, hs, hs0⟩ := prod_eq_zero_iff.1 h0
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
    exact hiso'' s hs (by rw [show r' = s by exact_mod_cast hs0]; simp)
  have hd : ((r : ℚ) - r') ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hne
  have hd' : ((r' : ℚ) - r) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hne.symm
  have key : resid R N r * φ + resid R N r' * φ' =
      ((N.eval (r : ℚ) * φ) * V.eval (r' : ℚ) - (N.eval (r' : ℚ) * φ') * V.eval (r : ℚ)) *
        ((V.eval (r : ℚ))⁻¹ * (V.eval (r' : ℚ))⁻¹) * (((r - r' : ℤ) : ℚ))⁻¹ := by
    rw [resid, resid, e1, e2]
    push_cast
    field_simp
    ring
  rw [key]
  have hNr := VGe_eval hN (VGe_intCast (p := p) r)
  have hNr' := VGe_eval hN (VGe_intCast (p := p) r')
  have hrr : VGe p 1 ((r : ℚ) - r') := by
    have := VGe_of_dvd_int (p := p) hdvd; push_cast at this; exact this
  have hNd : VGe p 1 (N.eval (r : ℚ) - N.eval (r' : ℚ)) :=
    VGe_eval_sub hN (VGe_intCast r) (VGe_intCast r') hrr
  have hVd : VGe p 1 (V.eval (r' : ℚ) - V.eval (r : ℚ)) := by
    have := VGe_eval_sub (PolyVGe_poleProd (p := p) R'') (VGe_intCast r') (VGe_intCast r)
      (by have := hrr.neg; rwa [neg_sub] at this)
    exact this
  have hVr := VGe_eval (PolyVGe_poleProd (p := p) R'') (VGe_intCast (p := p) r)
  have hnum : VGe p 1 ((N.eval (r : ℚ) * φ) * V.eval (r' : ℚ) -
      (N.eval (r' : ℚ) * φ') * V.eval (r : ℚ)) := by
    have e : (N.eval (r : ℚ) * φ) * V.eval (r' : ℚ) - (N.eval (r' : ℚ) * φ') * V.eval (r : ℚ) =
        N.eval (r : ℚ) * φ * (V.eval (r' : ℚ) - V.eval (r : ℚ)) +
          V.eval (r : ℚ) *
            (N.eval (r : ℚ) * (φ - φ') + φ' * (N.eval (r : ℚ) - N.eval (r' : ℚ))) := by
      ring
    rw [e]
    refine VGe.add ?_ ?_
    · simpa using (hNr.mul hφ).mul hVd
    · simpa using hVr.mul ((hNr.mul hφφ).add (by simpa using hφ'.mul hNd))
  have := (hnum.mul ((hunit r hiso').mul (hunit r' hiso''))).mul
    (VGe_inv_of_not_sq_dvd (p := p) (sub_ne_zero.2 hne) hsq)
  simpa using this

/-! ### Bernoulli numbers and `κ_d` -/

theorem VGe_one_div_prime {q : ℕ} (hq : q.Prime) : VGe p (-1) ((1 : ℚ) / q) := by
  by_cases hqp : q = p
  · subst hqp; simpa using VGe_p_pow (p := q) (-1)
  · refine (VGe_of_padicValRat fun _ => ?_).mono (by norm_num : (-1 : ℤ) ≤ 0)
    have : Fact q.Prime := ⟨hq⟩
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat_primes (Ne.symm hqp)]
    simp

theorem VGe_one_div_prime_ne {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : VGe p 0 ((1 : ℚ) / q) := by
  refine VGe_of_padicValRat fun _ => ?_
  have : Fact q.Prime := ⟨hq⟩
  rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat_primes (Ne.symm hqp)]
  simp

theorem bernoulli_even_eq (k : ℕ) : ∃ z : ℤ, _root_.bernoulli (2 * k) = z -
    ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  exact ⟨z, by rw [hz]; ring⟩

/-- von Staudt–Clausen: `v_p(B_{2k}) ≥ -1`. -/
theorem VGe_bernoulli_even (k : ℕ) : VGe p (-1) (_root_.bernoulli (2 * k)) := by
  obtain ⟨z, hz⟩ := bernoulli_even_eq k
  rw [hz]
  exact ((VGe_intCast z).mono (by norm_num)).sub
    (VGe_sum _ fun q hq => VGe_one_div_prime (mem_filter.1 hq).2.1)

/-- von Staudt–Clausen: `B_{2k}` is `p`-integral unless `p - 1 ∣ 2k`. -/
theorem VGe_bernoulli_even_of_not_dvd {k : ℕ} (h : ¬(p - 1) ∣ 2 * k) :
    VGe p 0 (_root_.bernoulli (2 * k)) := by
  obtain ⟨z, hz⟩ := bernoulli_even_eq k
  rw [hz]
  refine (VGe_intCast z).sub (VGe_sum _ fun q hq => ?_)
  have hq' := (mem_filter.1 hq).2
  exact VGe_one_div_prime_ne hq'.1 fun hqp => h (hqp ▸ hq'.2)

theorem VGe_half (hp2 : p ≠ 2) : VGe p 0 ((1 : ℚ) / 2) := by
  have := VGe_inv_int (p := p) (z := 2) (by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have h2 := hp.out.two_le
    have : p = 2 := by omega
    exact hp2 this)
  simpa using this

theorem VGe_bernoulli (hp2 : p ≠ 2) (n : ℕ) : VGe p (-1) (_root_.bernoulli n) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rw [← two_mul]; exact VGe_bernoulli_even k
  · rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1]; exact VGe_zero _
    · obtain rfl : n = 1 := by obtain ⟨k, rfl⟩ := hodd; omega
      rw [_root_.bernoulli_one, neg_div]
      exact (VGe_half hp2).neg.mono (by norm_num)

theorem VGe_bernoulli_of_not_dvd (hp2 : p ≠ 2) {n : ℕ} (h : ¬(p - 1) ∣ n) :
    VGe p 0 (_root_.bernoulli n) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rw [← two_mul] at h ⊢; exact VGe_bernoulli_even_of_not_dvd h
  · rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1]; exact VGe_zero _
    · obtain rfl : n = 1 := by obtain ⟨k, rfl⟩ := hodd; omega
      rw [_root_.bernoulli_one, neg_div]
      exact (VGe_half hp2).neg

theorem VGe_inv_24 (hp5 : 5 ≤ p) : VGe p 0 ((24 : ℚ)⁻¹) := by
  have := VGe_inv_int (p := p) (z := 24) (by
    intro h
    have h' : p ∣ 2 ^ 3 * 3 := by exact_mod_cast h
    rcases (Nat.Prime.dvd_mul hp.out).1 h' with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega)
  simpa using this

theorem descFactorial_three (d : ℕ) : d.descFactorial 3 = (d - 2) * ((d - 1) * d) := by
  simp [Nat.descFactorial_succ]

/-- `v_p(κ_d) ≥ -1`. -/
theorem VGe_kappa_neg (hp5 : 5 ≤ p) (d : ℕ) : VGe p (-1) (kappa d) := by
  rw [kappa_eq, mul_div_assoc, div_eq_mul_inv]
  have := ((VGe_natCast (p := p) (d.descFactorial 3)).mul
    ((VGe_bernoulli (p := p) (by omega) (d - 3)).mul (VGe_inv_24 hp5)))
  simpa [mul_assoc] using this

/-- `κ_d` is `p`-integral for `d ≤ 4p - 2`: if `p - 1 ∣ d - 3`, then `p ∣ d(d-1)(d-2)`. -/
theorem VGe_kappa (hp5 : 5 ≤ p) {d : ℕ} (hd : d + 2 ≤ 4 * p) : VGe p 0 (kappa d) := by
  rw [kappa_eq, mul_div_assoc, div_eq_mul_inv]
  have h24 := VGe_inv_24 hp5
  by_cases hdvd : (p - 1) ∣ (d - 3)
  · rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have : d.descFactorial 3 = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hd3
      rw [this]; simp [VGe_zero]
    obtain ⟨m, hm⟩ := hdvd
    have hm4 : m < 4 := by
      by_contra h
      have : (p - 1) * 4 ≤ (p - 1) * m := Nat.mul_le_mul_left _ (by omega)
      omega
    have hp1 : 1 ≤ p - 1 := by omega
    -- `p ∣ d (d - 1) (d - 2)` unless `m = 0`
    interval_cases m
    · have : d = 3 := by omega
      subst this
      have := (VGe_natCast (p := p) (Nat.descFactorial 3 3)).mul
        ((VGe_one (p := p)).mul h24)
      simpa using this
    all_goals
      have hpd : p ∣ d.descFactorial 3 := by
        rw [descFactorial_three]
        first
        | exact Dvd.dvd.mul_right (show p ∣ d - 2 from ⟨1, by rw [mul_one] at hm ⊢; omega⟩) _
        | exact Dvd.dvd.mul_left (Dvd.dvd.mul_right
            (show p ∣ d - 1 from ⟨2, by omega⟩) _) _
        | exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (show p ∣ d from ⟨3, by omega⟩) _) _
      obtain ⟨c, hc⟩ := hpd
      have h1 : VGe p 1 ((d.descFactorial 3 : ℕ) : ℚ) := by
        rw [hc]; push_cast
        simpa using (VGe_p_pow (p := p) 1).mul (VGe_natCast (p := p) c)
      have := h1.mul ((VGe_bernoulli (p := p) (by omega) (d - 3)).mul h24)
      simpa [mul_assoc] using this
  · have := (VGe_natCast (p := p) (d.descFactorial 3)).mul
      ((VGe_bernoulli_of_not_dvd (p := p) (by omega) hdvd).mul h24)
    simpa [mul_assoc] using this

/-- `τ(Q)` is `p`-integral for `Q` integral of degree `≤ 4p - 2`. -/
theorem VGe_taup {Q : ℚ[X]} {w : ℤ} (hQ : PolyVGe p w Q) (hp5 : 5 ≤ p)
    (hdeg : Q.natDegree + 2 ≤ 4 * p) : VGe p w (taup Q) := by
  rw [taup_eq_sum, Polynomial.sum]
  refine VGe_sum _ fun d hd => ?_
  have : d ≤ Q.natDegree := le_natDegree_of_mem_supp d hd
  simpa using (hQ d).mul (VGe_kappa hp5 (by omega))

theorem VGe_taup_neg {Q : ℚ[X]} {w : ℤ} (hQ : PolyVGe p w Q) (hp5 : 5 ≤ p) :
    VGe p (w - 1) (taup Q) := by
  rw [taup_eq_sum, Polynomial.sum]
  refine VGe_sum _ fun d _ => ?_
  simpa [sub_eq_add_neg] using (hQ d).mul (VGe_kappa_neg hp5 d)

/-! ### Harmonic numbers -/

theorem VGe_inv_nat_pow_of_lt {v : ℕ} (hv0 : v ≠ 0) (hv : v < p) : VGe p 0 (1 / (v : ℚ) ^ 5) := by
  have hnd : ¬(p : ℤ) ∣ (v : ℤ) := by
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) (by exact_mod_cast h)
    omega
  have := (VGe_inv_int (p := p) hnd).pow 5
  simpa [one_div, inv_pow] using this

theorem VGe_H5_of_lt {m : ℕ} (hm : m < p) : VGe p 0 (H5 m) :=
  VGe_sum _ fun v hv => VGe_inv_nat_pow_of_lt (by have := (mem_Icc.1 hv).1; omega)
    (by have := (mem_Icc.1 hv).2; omega)

/-- `v⁻⁵ + (p - v)⁻⁵ ≡ 0 (mod p)` for `0 < v < p`. -/
theorem VGe_inv_pow_add_reflect {v : ℕ} (hv0 : 0 < v) (hv : v < p) :
    VGe p 1 (1 / (v : ℚ) ^ 5 + 1 / ((p - v : ℕ) : ℚ) ^ 5) := by
  have hpv : 0 < p - v := by omega
  have hdvd : (p : ℤ) ∣ ((p - v : ℕ) : ℤ) ^ 5 + (v : ℤ) ^ 5 := by
    have := sub_dvd_pow_sub_pow ((p - v : ℕ) : ℤ) (-(v : ℤ)) 5
    rw [show ((p - v : ℕ) : ℤ) - -(v : ℤ) = p by push_cast [Nat.cast_sub hv.le]; ring] at this
    simpa [Odd.neg_pow (by decide : Odd 5)] using this
  obtain ⟨c, hc⟩ := hdvd
  have e : 1 / (v : ℚ) ^ 5 + 1 / ((p - v : ℕ) : ℚ) ^ 5 =
      (p : ℚ) * c * (((v : ℤ) : ℚ)⁻¹ ^ 5 * (((p - v : ℕ) : ℤ) : ℚ)⁻¹ ^ 5) := by
    have hc' : (((p - v : ℕ) : ℤ) : ℚ) ^ 5 + ((v : ℤ) : ℚ) ^ 5 = (p : ℚ) * c := by
      exact_mod_cast hc
    have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv0.ne'
    have hpv' : ((p - v : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpv.ne'
    push_cast at hc' ⊢
    rw [← hc']
    field_simp
  have hu1 := VGe_inv_int (p := p) (z := v) (by
    intro h; have := Nat.le_of_dvd hv0 (by exact_mod_cast h); omega)
  have hu2 := VGe_inv_int (p := p) (z := (p - v : ℕ)) (by
    intro h; have := Nat.le_of_dvd hpv (by exact_mod_cast h); omega)
  rw [e]
  have := ((VGe_p_pow (p := p) 1).mul (VGe_intCast (p := p) c)).mul ((hu1.pow 5).mul (hu2.pow 5))
  simpa using this

/-- `H⁽⁵⁾_{p-1} ≡ 0 (mod p)`, by pairing `v` with `p - v`. -/
theorem VGe_H5_pred (hp2 : p ≠ 2) : VGe p 1 (H5 (p - 1)) := by
  have hrefl : ∑ v ∈ Icc 1 (p - 1), 1 / ((p - v : ℕ) : ℚ) ^ 5 = H5 (p - 1) := by
    refine sum_nbij' (fun v => p - v) (fun v => p - v) ?_ ?_ ?_ ?_ ?_
    · intro v hv; simp only [mem_Icc] at hv ⊢; omega
    · intro v hv; simp only [mem_Icc] at hv ⊢; omega
    · intro v hv; simp only [mem_Icc] at hv; omega
    · intro v hv; simp only [mem_Icc] at hv; omega
    · intro v _; rfl
  have h2 : 2 * H5 (p - 1) =
      ∑ v ∈ Icc 1 (p - 1), (1 / (v : ℚ) ^ 5 + 1 / ((p - v : ℕ) : ℚ) ^ 5) := by
    rw [sum_add_distrib, hrefl, H5]; ring
  have hp1 := hp.out.two_le
  have hs : VGe p 1 (2 * H5 (p - 1)) := by
    rw [h2]
    exact VGe_sum _ fun v hv => VGe_inv_pow_add_reflect (by have := (mem_Icc.1 hv).1; omega)
      (by have := (mem_Icc.1 hv).2; omega)
  have := (VGe_half (p := p) hp2).mul hs
  simpa [← mul_assoc] using this

/-- `H⁽⁵⁾_m ≡ H⁽⁵⁾_{p-1-m} (mod p)` for `m < p`. -/
theorem VGe_H5_reflect (hp2 : p ≠ 2) {m : ℕ} (hm : m < p) :
    VGe p 1 (H5 m - H5 (p - 1 - m)) := by
  have key : ∀ m, m < p → H5 m - H5 (p - 1 - m) =
      ∑ v ∈ Icc 1 m, (1 / (v : ℚ) ^ 5 + 1 / ((p - v : ℕ) : ℚ) ^ 5) - H5 (p - 1) := by
    intro m
    induction m with
    | zero => intro _; simp [H5]
    | succ m ih =>
      intro hm
      have h1 := H5_succ_rat m
      have h2 := H5_succ_rat (p - 1 - (m + 1))
      rw [show p - 1 - (m + 1) + 1 = p - 1 - m by omega] at h2
      rw [sum_Icc_succ_top (by omega), ← sub_add_eq_add_sub, ← ih (by omega), h1, h2]
      have : ((p - 1 - (m + 1) : ℕ) : ℚ) + 1 = ((p - (m + 1) : ℕ) : ℚ) := by
        rw [show p - (m + 1) = (p - 1 - (m + 1)) + 1 by omega]; push_cast; ring
      rw [this]
      push_cast
      simp only [one_div, inv_pow]
      ring
  rw [key m hm]
  exact (VGe_sum _ fun v hv => VGe_inv_pow_add_reflect (by have := (mem_Icc.1 hv).1; omega)
    (by have := (mem_Icc.1 hv).2; omega)).sub (VGe_H5_pred hp2)

/-! ### Poles of size `< p` -/

/-- If every pole has `|r| < p`, the residue sum `∑ Res_r φ(r)` is integral whenever
`φ(r) ≡ φ(r - p) (mod p)`: the poles `r` and `r - p` are the only congruent pairs. -/
theorem VGe_resid_sum_small {R : Finset ℤ} (hR : ∀ r ∈ R, r.natAbs < p) {N : ℚ[X]}
    (hN : PolyVGe p 0 N) (φ : ℤ → ℚ) (hφ : ∀ r ∈ R, VGe p 0 (φ r))
    (hφc : ∀ r ∈ R, r - p ∈ R → VGe p 1 (φ r - φ (r - p))) :
    VGe p 0 (∑ r ∈ R, resid R N r * φ r) := by
  classical
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  -- the congruent partner of `r` can only be `r ± p`
  have hpart : ∀ r ∈ R, ∀ s ∈ R, s ≠ r → (p : ℤ) ∣ (r - s) → s = r - p ∨ s = r + p := by
    intro r hr s hs hsr h
    have := eq_of_dvd_of_natAbs_lt (p := p) h
      (by have := hR r hr; have := hR s hs; omega) (sub_ne_zero.2 (Ne.symm hsr))
    omega
  rw [← sum_filter_add_sum_filter_not R (fun r : ℤ => r - (p : ℤ) ∈ R),
    ← sum_filter_add_sum_filter_not (R.filter fun r : ℤ => r - (p : ℤ) ∉ R)
      (fun r : ℤ => r + (p : ℤ) ∈ R)]
  set P := R.filter fun r : ℤ => r - (p : ℤ) ∈ R
  have hP' : ∑ r ∈ (R.filter fun r : ℤ => r - (p : ℤ) ∉ R).filter (fun r : ℤ => r + (p : ℤ) ∈ R),
      resid R N r * φ r = ∑ r ∈ P, resid R N (r - p) * φ (r - p) := by
    refine sum_nbij' (fun r => r + p) (fun r => r - p) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [P, mem_filter] at hr ⊢
      refine ⟨hr.2, by simpa using hr.1.1⟩
    · intro r hr
      simp only [P, mem_filter] at hr ⊢
      refine ⟨⟨hr.2, fun h => ?_⟩, by simpa using hr.1⟩
      have h1 := hR _ hr.2; have h2 := hR _ h; have h3 := hR _ hr.1
      omega
    · intro r _; simp
    · intro r _; simp
    · intro r _; simp
  rw [hP', ← add_assoc, ← sum_add_distrib]
  refine VGe.add (VGe_sum _ fun r hr => ?_) (VGe_sum _ fun r hr => ?_)
  · -- a congruent pair `r, r - p`
    simp only [P, mem_filter] at hr
    have hrp : r - p ≠ r := by omega
    refine VGe_resid_pair hN hr.1 hr.2 (Ne.symm hrp) ⟨1, by ring⟩ ?_ ?_ (hφ r hr.1)
      (hφ _ hr.2) (hφc r hr.1 hr.2)
    · rw [show r - (r - p) = (p : ℤ) by ring]
      intro h
      have := Int.le_of_dvd hp0 h
      have h2 := hp.out.two_le
      nlinarith
    · intro s hs hsr hsr' h
      rcases hpart r hr.1 s hs hsr h with h' | h'
      · exact hsr' h'
      · have h1 := hR _ hr.2; have h2 := hR _ (h' ▸ hs); omega
  · -- an isolated pole
    simp only [mem_filter] at hr
    refine (VGe_resid_isolated hN hr.1.1 fun s hs hsr h => ?_).mul (hφ r hr.1.1)
    rcases hpart r hr.1.1 s hs hsr h with h' | h'
    · exact hr.1.2 (h' ▸ hs)
    · exact hr.2 (h' ▸ hs)

/-- `τ_X(N / ∏_{r ∈ R} (x - r))` is integral when all poles satisfy `|r| < p`, the numerator is
integral and the polynomial part has degree `≤ 4p - 2`. -/
theorem PolyVGe_tauR_small (hp5 : 5 ≤ p) {R : Finset ℤ} (hR : ∀ r ∈ R, r.natAbs < p) {N : ℚ[X]}
    (hN : PolyVGe p 0 N) (hdeg : (N /ₘ poleProd R).natDegree + 2 ≤ 4 * p) :
    PolyVGe p 0 (tauR R N) := by
  have hp2 : p ≠ 2 := by omega
  refine PolyVGe_tauR (VGe.add ?_ ?_) ?_
  · exact VGe_taup (PolyVGe_divByMonic hN (PolyVGe_poleProd R) (poleProd_monic R)) hp5 hdeg
  · refine VGe_resid_sum_small hR hN (fun r => H5 (dd r)) (fun r hr => VGe_H5_of_lt ?_) ?_
    · have := hR r hr
      rcases le_or_gt 0 r with h | h
      · have := dd_of_nonneg h; omega
      · have := dd_of_neg h; omega
    · intro r hr hrp
      have h1 := hR r hr; have h2 := hR _ hrp
      have hr0 : 0 < r := by omega
      have e1 : dd r = r.toNat := by have := dd_of_nonneg hr0.le; omega
      have e2 : dd (r - p) = p - 1 - r.toNat := by
        have := dd_of_neg (show r - p < 0 by omega); omega
      rw [e1, e2]
      exact VGe_H5_reflect hp2 (by omega)
  · have := VGe_resid_sum_small hR hN (fun _ => 1) (fun _ _ => VGe_one) (fun _ _ _ => by
      simpa using VGe_zero 1)
    simpa [tauRes] using this

end Zeta5
