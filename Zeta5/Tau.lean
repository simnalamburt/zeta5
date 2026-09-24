/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Zeta5.Compat
import Zeta5.PoleDen

/-!
# The local functional `τ_X` of §3

Under `t = -x²` the poles `t = -j²` of the functional `μ_X` become the integers `x = ±j`, and
`μ_X(R) = τ_X(x⁵ R(-x²))` (3.1), where

* on polynomials, `τ(P) = L(P''')/24` with `L(xᵏ) = B_k` (`B₁ = -1/2`);
* on simple poles, `τ_X(1/(x - r)) = H⁽⁵⁾_{d(r)} - X`, with `d(r) = r` for `r ≥ 0` and
  `d(r) = -r - 1` for `r < 0`.

The functional `L` is characterised by `L(1) = 1` and `L(F(x + 1) - F(x)) = F'(0)`; this gives the
difference identity (3.3) `τ(F(x + 1) - F(x)) = F⁗(0)/24` and Bernoulli's multiplication theorem
`∑_{a<p} τ(P(a + px)) = p⁴ τ(P)` (the polynomial case of Lemma 3.2).

A rational function with simple poles in a finite set `R ⊆ ℤ` is represented by its numerator
`N` over `∏_{r ∈ R} (x - r)`; `Zeta5.tauR R N` is `τ_X` of it, by polynomial division and partial
fractions.
-/

open Polynomial Finset

namespace Zeta5

/-! ### The Bernoulli functional -/

/-- `L(xⁿ) = Bₙ`. -/
noncomputable def Lber : ℚ[X] →ₗ[ℚ] ℚ := Polynomial.lsum fun n => _root_.bernoulli n • LinearMap.id

theorem Lber_apply (P : ℚ[X]) : Lber P = P.sum fun n c => _root_.bernoulli n * c := by
  simp [Lber]

theorem Lber_monomial (n : ℕ) (c : ℚ) : Lber (monomial n c) = _root_.bernoulli n * c := by
  simp [Lber_apply]

theorem Lber_X_pow (n : ℕ) : Lber (X ^ n) = _root_.bernoulli n := by
  rw [← monomial_one_right_eq_X_pow, Lber_monomial, mul_one]

theorem Lber_C_mul (c : ℚ) (P : ℚ[X]) : Lber (C c * P) = c * Lber P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem Lber_X_add_one_pow (n : ℕ) :
    Lber ((X + 1) ^ n) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * _root_.bernoulli k := by
  rw [add_pow, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, ← C_eq_natCast, mul_comm, Lber_C_mul, Lber_X_pow]

/-- `L(F(x + 1) - F(x)) = F'(0)`. -/
theorem Lber_delta (F : ℚ[X]) : Lber (F.comp (X + 1) - F) = (derivative F).eval 0 := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [add_comp, map_sub, map_add, eval_add] at *
    linarith
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← mul_sub, Lber_C_mul,
      derivative_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X, map_sub, Lber_X_add_one_pow,
      Lber_X_pow, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, add_sub_cancel_right,
      _root_.sum_bernoulli]
    rcases n with _ | _ | n
    · simp
    · simp
    · simp

/-- Every polynomial is a difference `F(x + 1) - F(x)`. -/
theorem exists_antidiff (Q : ℚ[X]) : ∃ F : ℚ[X], F.comp (X + 1) - F = Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨F, hF⟩ := hP
    obtain ⟨G, hG⟩ := hQ
    exact ⟨F + G, by rw [add_comp, ← hF, ← hG]; ring⟩
  | monomial n c =>
    refine ⟨C (c / (n + 1)) * Polynomial.bernoulli (n + 1), ?_⟩
    rw [mul_comp, C_comp, add_comm X 1, Polynomial.bernoulli_comp_one_add_X, ← mul_sub,
      add_sub_cancel_left, ← C_mul_X_pow_eq_monomial, add_tsub_cancel_right, nsmul_eq_mul,
      ← mul_assoc, ← C_eq_natCast, ← C_mul]
    congr 2
    push_cast
    field_simp

/-- Bernoulli's multiplication theorem, in the form `∑_{a<p} L(Q(a + px)) = p L(Q)`. -/
theorem Lber_mul_sum (p : ℕ) (Q : ℚ[X]) :
    ∑ a ∈ range p, Lber (Q.comp (C (a : ℚ) + C (p : ℚ) * X)) = p * Lber Q := by
  obtain ⟨F, rfl⟩ := exists_antidiff Q
  have hshift : ∀ a : ℕ, (F.comp (X + 1) - F).comp (C (a : ℚ) + C (p : ℚ) * X) =
      F.comp (C ((a + 1 : ℕ) : ℚ) + C (p : ℚ) * X) - F.comp (C (a : ℚ) + C (p : ℚ) * X) := by
    intro a
    have hq : (X + 1 : ℚ[X]).comp (C (a : ℚ) + C (p : ℚ) * X) =
        C ((a + 1 : ℕ) : ℚ) + C (p : ℚ) * X := by
      simp only [add_comp, X_comp, one_comp]
      push_cast
      rw [C_add, C_1]; ring
    rw [sub_comp, comp_assoc, hq]
  simp_rw [hshift]
  rw [← map_sum, sum_range_sub (fun a : ℕ => F.comp (C (a : ℚ) + C (p : ℚ) * X))]
  set G := F.comp (C (p : ℚ) * X) with hG
  have h1 : F.comp (C ((p : ℕ) : ℚ) + C (p : ℚ) * X) = G.comp (X + 1) := by
    rw [hG, comp_assoc]
    congr 1
    simp only [mul_comp, C_comp, X_comp]
    ring
  have h2 : F.comp (C ((0 : ℕ) : ℚ) + C (p : ℚ) * X) = G := by
    rw [hG]; simp
  rw [h1, h2, Lber_delta, Lber_delta, hG, derivative_comp]
  simp

/-! ### The functional `τ` on polynomials -/

/-- `τ(P) = L(P''')/24`. -/
noncomputable def taup : ℚ[X] →ₗ[ℚ] ℚ :=
  (24 : ℚ)⁻¹ • (Lber ∘ₗ (derivative ∘ₗ derivative ∘ₗ derivative))

theorem taup_apply (P : ℚ[X]) : taup P = Lber (derivative (derivative (derivative P))) / 24 := by
  simp [taup, div_eq_inv_mul]

theorem derivative_comp_X_add_one (F : ℚ[X]) :
    derivative (F.comp (X + 1)) = (derivative F).comp (X + 1) := by
  rw [derivative_comp]; simp

/-- (3.3): `τ(F(x + 1) - F(x)) = F⁗(0)/24`, the coefficient of `x⁴` in `F`. -/
theorem taup_delta (F : ℚ[X]) : taup (F.comp (X + 1) - F) = F.coeff 4 := by
  rw [taup_apply]
  simp only [map_sub, derivative_comp_X_add_one]
  rw [← map_sub, Lber_delta, ← coeff_zero_eq_eval_zero]
  have := coeff_iterate_derivative (k := 4) F 0
  rw [show derivative^[4] F = derivative (derivative (derivative (derivative F))) from rfl,
    zero_add, Nat.descFactorial_self, nsmul_eq_mul] at this
  rw [this]
  norm_num [Nat.factorial]

theorem taup_comp_X_add_one (F : ℚ[X]) : taup (F.comp (X + 1)) = taup F + F.coeff 4 := by
  rw [← taup_delta, map_sub]; ring

/-- Bernoulli's multiplication theorem for `τ`: `∑_{a<p} τ(P(a + px)) = p⁴ τ(P)`. -/
theorem taup_mul_sum (p : ℕ) (P : ℚ[X]) :
    ∑ a ∈ range p, taup (P.comp (C (a : ℚ) + C (p : ℚ) * X)) = (p : ℚ) ^ 4 * taup P := by
  have hd : ∀ (a : ℕ) (Q : ℚ[X]), derivative (Q.comp (C (a : ℚ) + C (p : ℚ) * X)) =
      C (p : ℚ) * (derivative Q).comp (C (a : ℚ) + C (p : ℚ) * X) := by
    intro a Q; rw [derivative_comp]; simp
  have hd3 : ∀ (a : ℕ) (Q : ℚ[X]),
      derivative (derivative (derivative (Q.comp (C (a : ℚ) + C (p : ℚ) * X)))) =
      C ((p : ℚ) ^ 3) * (derivative (derivative (derivative Q))).comp
        (C (a : ℚ) + C (p : ℚ) * X) := by
    intro a Q
    rw [hd, derivative_C_mul, hd, derivative_C_mul, derivative_C_mul, hd, ← mul_assoc,
      ← mul_assoc, ← C_mul, ← C_mul]
    ring_nf
  simp_rw [taup_apply, hd3, Lber_C_mul]
  rw [← sum_div, ← mul_sum, Lber_mul_sum]
  ring

/-- `κ_d = τ(x^d)`. -/
noncomputable def kappa (d : ℕ) : ℚ := taup (X ^ d)

theorem kappa_eq (d : ℕ) :
    kappa d = (d.descFactorial 3 : ℚ) * _root_.bernoulli (d - 3) / 24 := by
  rw [kappa, taup_apply]
  have := iterate_derivative_X_pow_eq_C_mul (R := ℚ) d 3
  rw [show derivative (derivative (derivative (X ^ d))) = derivative^[3] (X ^ d : ℚ[X]) from rfl,
    this, Lber_C_mul, Lber_X_pow]

theorem taup_eq_sum (P : ℚ[X]) : taup P = P.sum fun d c => c * kappa d := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [map_sum, sum_def]
  refine sum_congr rfl fun d _ => ?_
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, kappa]

/-! ### Harmonic numbers at integer poles -/

/-- `d(r) = r` for `r ≥ 0` and `d(r) = -r - 1` for `r < 0`. -/
def dd (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat

theorem dd_of_nonneg {r : ℤ} (h : 0 ≤ r) : (dd r : ℤ) = r := by
  simp [dd, h]

theorem dd_of_neg {r : ℤ} (h : r < 0) : (dd r : ℤ) = -r - 1 := by
  simp only [dd, not_le.2 h, ite_false]
  exact Int.toNat_of_nonneg (by omega)

theorem H5_succ_rat (n : ℕ) : H5 (n + 1) = H5 n + ((n + 1 : ℚ))⁻¹ ^ 5 := by
  rw [H5, H5, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rw [one_div, inv_pow]

/-- The harmonic increments: `H⁽⁵⁾_{d(r+1)} - H⁽⁵⁾_{d(r)} = (r + 1)⁻⁵`. -/
theorem H5_dd_add_one (r : ℤ) : H5 (dd (r + 1)) - H5 (dd r) = ((r : ℚ) + 1)⁻¹ ^ 5 := by
  rcases lt_trichotomy r (-1) with h | rfl | h
  · have e1 := dd_of_neg (show r + 1 < 0 by omega)
    have e2 := dd_of_neg (show r < 0 by omega)
    have h2 : dd r = dd (r + 1) + 1 := by omega
    rw [h2, H5_succ_rat]
    have : ((dd (r + 1) : ℚ) + 1) = -((r : ℚ) + 1) := by
      have : ((dd (r + 1) : ℤ) : ℚ) = ((-(r + 1) - 1 : ℤ) : ℚ) := by rw [e1]
      push_cast at this
      linarith
    rw [this, inv_neg, neg_pow]
    norm_num
  · simp [dd]
  · have e1 := dd_of_nonneg (show 0 ≤ r + 1 by omega)
    have e2 := dd_of_nonneg (show 0 ≤ r by omega)
    have h1 : dd (r + 1) = dd r + 1 := by omega
    rw [h1, H5_succ_rat, add_sub_cancel_left]
    have : ((dd r : ℤ) : ℚ) = (r : ℚ) := by rw [e2]
    push_cast at this
    rw [this]

/-! ### Rational functions with simple integer poles -/

/-- `∏_{r ∈ R} (x - r)`. -/
noncomputable def poleProd (R : Finset ℤ) : ℚ[X] := ∏ r ∈ R, (X - C (r : ℚ))

theorem poleProd_monic (R : Finset ℤ) : (poleProd R).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_poleProd (R : Finset ℤ) : (poleProd R).natDegree = R.card := by
  rw [poleProd, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

theorem poleProd_eq_mul_erase {R : Finset ℤ} {r : ℤ} (hr : r ∈ R) :
    poleProd R = (X - C (r : ℚ)) * poleProd (R.erase r) :=
  (Finset.mul_prod_erase R (fun r : ℤ => X - C (r : ℚ)) hr).symm

theorem eval_poleProd_of_mem {R : Finset ℤ} {r : ℤ} (hr : r ∈ R) :
    (poleProd R).eval (r : ℚ) = 0 := by
  rw [poleProd_eq_mul_erase hr]; simp

theorem eval_poleProd_erase_ne_zero (R : Finset ℤ) (r : ℤ) :
    (poleProd (R.erase r)).eval (r : ℚ) ≠ 0 := by
  rw [poleProd, eval_prod, prod_ne_zero_iff]
  intro s hs h
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at h
  exact (mem_erase.1 hs).1 (by exact_mod_cast h.symm)

theorem eval_derivative_poleProd {R : Finset ℤ} {r : ℤ} (hr : r ∈ R) :
    (derivative (poleProd R)).eval (r : ℚ) = (poleProd (R.erase r)).eval (r : ℚ) := by
  rw [poleProd_eq_mul_erase hr, derivative_mul]; simp

/-- The residue of `N / ∏_{r ∈ R} (x - r)` at `x = r`. -/
noncomputable def resid (R : Finset ℤ) (N : ℚ[X]) (r : ℤ) : ℚ :=
  N.eval (r : ℚ) / (derivative (poleProd R)).eval (r : ℚ)

theorem resid_add (R : Finset ℤ) (N M : ℚ[X]) (r : ℤ) :
    resid R (N + M) r = resid R N r + resid R M r := by
  simp [resid, add_div]

theorem resid_smul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) (r : ℤ) :
    resid R (c • N) r = c * resid R N r := by
  simp [resid, mul_div_assoc]

/-- Partial fractions: `N mod ∏ (x - r) = ∑_r Res_r · ∏_{s ≠ r} (x - s)`. -/
theorem modByMonic_poleProd (N : ℚ[X]) (R : Finset ℤ) :
    N %ₘ poleProd R = ∑ r ∈ R, C (resid R N r) * poleProd (R.erase r) := by
  have hinj : Function.Injective fun r : ℤ => (r : ℚ) := Int.cast_injective
  have hcard : (R.image fun r : ℤ => (r : ℚ)).card = R.card := card_image_of_injective _ hinj
  refine eq_of_degrees_lt_of_eval_finset_eq (s := R.image fun r : ℤ => (r : ℚ)) ?_ ?_ ?_
  · rw [hcard]
    refine (degree_modByMonic_lt N (poleProd_monic R)).trans_le ?_
    rw [degree_eq_natDegree (poleProd_monic R).ne_zero, natDegree_poleProd]
  · rw [hcard, ← mem_degreeLT]
    refine Submodule.sum_mem _ fun r hr => ?_
    rw [mem_degreeLT, ← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    rw [degree_eq_natDegree (poleProd_monic _).ne_zero, natDegree_poleProd,
      card_erase_of_mem hr]
    have := card_pos.2 ⟨r, hr⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hx
    have h := congr_arg (eval (r : ℚ)) (modByMonic_add_div N (poleProd R))
    rw [eval_add, eval_mul, eval_poleProd_of_mem hr, zero_mul, add_zero] at h
    rw [h, eval_finsetSum, sum_eq_single r]
    · rw [eval_mul, eval_C, resid, eval_derivative_poleProd hr,
        div_mul_cancel₀ _ (eval_poleProd_erase_ne_zero R r)]
    · intro s hs hsr
      rw [eval_mul, eval_poleProd_of_mem (mem_erase.2 ⟨hsr.symm, hr⟩), mul_zero]
    · intro h'; exact absurd hr h'

/-- The constant coefficient of `τ_X(N / ∏_{r ∈ R} (x - r))`. -/
noncomputable def tauConst (R : Finset ℤ) (N : ℚ[X]) : ℚ :=
  taup (N /ₘ poleProd R) + ∑ r ∈ R, resid R N r * H5 (dd r)

/-- Minus the coefficient of `X` in `τ_X(N / ∏_{r ∈ R} (x - r))`: the sum of the residues. -/
noncomputable def tauRes (R : Finset ℤ) (N : ℚ[X]) : ℚ := ∑ r ∈ R, resid R N r

/-- `τ_X(N / ∏_{r ∈ R} (x - r))`, with `τ_X(1/(x - r)) = H⁽⁵⁾_{d(r)} - X`. -/
noncomputable def tauR (R : Finset ℤ) (N : ℚ[X]) : ℚ[X] := C (tauConst R N) - C (tauRes R N) * X

theorem tauConst_add (R : Finset ℤ) (N M : ℚ[X]) :
    tauConst R (N + M) = tauConst R N + tauConst R M := by
  simp only [tauConst, add_divByMonic, map_add, resid_add, add_mul, sum_add_distrib]
  ring

theorem tauConst_smul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) :
    tauConst R (c • N) = c * tauConst R N := by
  simp only [tauConst, smul_divByMonic, map_smul, smul_eq_mul, resid_smul, mul_add, mul_sum,
    mul_assoc]

theorem tauRes_add (R : Finset ℤ) (N M : ℚ[X]) :
    tauRes R (N + M) = tauRes R N + tauRes R M := by
  simp only [tauRes, resid_add, sum_add_distrib]

theorem tauRes_smul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) :
    tauRes R (c • N) = c * tauRes R N := by
  simp only [tauRes, resid_smul, mul_sum]

theorem tauR_add (R : Finset ℤ) (N M : ℚ[X]) : tauR R (N + M) = tauR R N + tauR R M := by
  simp only [tauR, tauConst_add, tauRes_add, C_add]; ring

theorem tauR_smul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) : tauR R (c • N) = C c * tauR R N := by
  simp only [tauR, tauConst_smul, tauRes_smul, C_mul]; ring

theorem tauR_C_mul (R : Finset ℤ) (c : ℚ) (N : ℚ[X]) : tauR R (C c * N) = C c * tauR R N := by
  rw [← smul_eq_C_mul, tauR_smul]

theorem tauR_sum {ι : Type*} (s : Finset ι) (R : Finset ℤ) (N : ι → ℚ[X]) :
    tauR R (∑ i ∈ s, N i) = ∑ i ∈ s, tauR R (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tauR, tauConst, tauRes, resid]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, tauR_add, ih]

/-- On polynomials, `τ_X` is `τ`: `τ_X(P) = τ(P)` for the numerator `P · ∏ (x - r)`. -/
theorem tauR_poleProd_mul (R : Finset ℤ) (P : ℚ[X]) : tauR R (poleProd R * P) = C (taup P) := by
  have hres : ∀ r ∈ R, resid R (poleProd R * P) r = 0 := fun r hr => by
    rw [resid, eval_mul, eval_poleProd_of_mem hr, zero_mul, zero_div]
  simp only [tauR, tauConst, tauRes, mul_divByMonic_cancel_left P (poleProd_monic R)]
  rw [sum_eq_zero fun r hr => by rw [hres r hr, zero_mul], sum_eq_zero hres]
  simp

/-- `τ_X(1/(x - r)) = H⁽⁵⁾_{d(r)} - X`. -/
theorem tauR_basis {R : Finset ℤ} {r : ℤ} (hr : r ∈ R) :
    tauR R (poleProd (R.erase r)) = C (H5 (dd r)) - X := by
  have hdiv : poleProd (R.erase r) /ₘ poleProd R = 0 := by
    rw [divByMonic_eq_zero_iff (poleProd_monic R), degree_eq_natDegree (poleProd_monic _).ne_zero,
      degree_eq_natDegree (poleProd_monic _).ne_zero, natDegree_poleProd, natDegree_poleProd,
      card_erase_of_mem hr]
    have := card_pos.2 ⟨r, hr⟩
    exact_mod_cast Nat.sub_lt this one_pos
  have hres : ∀ s ∈ R, resid R (poleProd (R.erase r)) s = if s = r then 1 else 0 := by
    intro s hs
    split_ifs with h
    · subst h
      rw [resid, eval_derivative_poleProd hs, div_self (eval_poleProd_erase_ne_zero R s)]
    · rw [resid, eval_poleProd_of_mem (mem_erase.2 ⟨h, hs⟩), zero_div]
  simp only [tauR, tauConst, tauRes, hdiv, map_zero, zero_add]
  rw [sum_eq_single r (fun s hs hsr => by simp [hres s hs, hsr]) (fun h => absurd hr h),
    sum_eq_single r (fun s hs hsr => by simp [hres s hs, hsr]) (fun h => absurd hr h),
    hres r hr]
  simp

/-! ### The pullback (3.1) -/

/-- The poles `x = ±j` (`j ∈ S`) of `R(-x²)`, for `R` with poles at `t = -j²`. -/
def poleSet (S : Finset ℕ) : Finset ℤ :=
  S.image (fun j : ℕ => (j : ℤ)) ∪ S.image (fun j : ℕ => -(j : ℤ))

/-- The numerator of `x⁵ A(-x²) / ∏_{j ∈ S} (-x² + j²)` over `∏_{r ∈ poleSet S} (x - r)`. -/
noncomputable def pull (S : Finset ℕ) (A : ℚ[X]) : ℚ[X] :=
  C ((-1 : ℚ) ^ S.card) * X ^ 5 * A.comp (-X ^ 2)

theorem pull_add (S : Finset ℕ) (A B : ℚ[X]) : pull S (A + B) = pull S A + pull S B := by
  simp only [pull, add_comp]; ring

theorem pull_smul (S : Finset ℕ) (c : ℚ) (A : ℚ[X]) : pull S (c • A) = c • pull S A := by
  simp only [pull, smul_eq_C_mul, mul_comp, C_comp]; ring

theorem pull_sum {ι : Type*} (s : Finset ι) (S : Finset ℕ) (A : ι → ℚ[X]) :
    pull S (∑ i ∈ s, A i) = ∑ i ∈ s, pull S (A i) := by
  simp only [pull, Polynomial.sum_comp, mul_sum]

theorem poleProd_poleSet (S : Finset ℕ) (hS : 0 ∉ S) :
    poleProd (poleSet S) = ∏ j ∈ S, ((X - C (j : ℚ)) * (X + C (j : ℚ))) := by
  have hdisj : Disjoint (S.image fun j : ℕ => (j : ℤ)) (S.image fun j : ℕ => -(j : ℤ)) := by
    rw [disjoint_left]
    intro r hr hr'
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hr
    obtain ⟨j, hj, hij⟩ := mem_image.1 hr'
    have : (i : ℤ) = 0 := by omega
    exact hS (by rwa [show i = 0 by exact_mod_cast this] at hi)
  rw [poleProd, poleSet, prod_union hdisj, prod_image fun a _ b _ h => by exact_mod_cast h,
    prod_image fun a _ b _ h => by simpa using h, prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  push_cast
  rw [C_neg, sub_neg_eq_add]

theorem poleDen_comp_neg_sq (S : Finset ℕ) (hS : 0 ∉ S) :
    (poleDen S).comp (-X ^ 2) = C ((-1 : ℚ) ^ S.card) * poleProd (poleSet S) := by
  rw [poleProd_poleSet S hS, poleDen, Polynomial.prod_comp, ← prod_const, map_prod,
    ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [add_comp, X_comp, C_comp]
  simp only [map_pow, map_neg, map_one]
  ring

/-- On polynomials, (3.1) is `μ(Q) = τ(x⁵ Q(-x²))`, by three differentiations. -/
theorem mu_eq_taup (Q : ℚ[X]) : mu Q = taup (X ^ 5 * Q.comp (-X ^ 2)) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ, add_comp, mul_add, map_add]
  | monomial e c =>
    rw [mu_monomial, ← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow,
      ← pow_mul, show X ^ 5 * (C c * ((-1) ^ e * X ^ (2 * e))) =
        C (c * (-1) ^ e) * X ^ (2 * e + 5) by rw [C_mul, C_pow, C_neg, C_1]; ring,
      ← smul_eq_C_mul, map_smul, ← kappa, kappa_eq, muMon, smul_eq_mul]
    have : (2 * e + 5).descFactorial 3 = (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
      simp [Nat.descFactorial_succ]; ring
    rw [this, show 2 * e + 5 - 3 = 2 * e + 2 by omega]
    push_cast
    ring

theorem muX_add (A B : ℚ[X]) (S : Finset ℕ) : muX (A + B) S = muX A S + muX B S := by
  simp only [muX, add_divByMonic, map_add, residue, eval_add, add_div, add_mul,
    sum_add_distrib]
  ring

theorem muX_smul (c : ℚ) (A : ℚ[X]) (S : Finset ℕ) : muX (c • A) S = C c * muX A S := by
  simp only [muX, smul_divByMonic, map_smul, smul_eq_mul, C_mul, residue, eval_smul,
    mul_div_assoc, mul_add, mul_sum, mul_assoc]

theorem muX_eq (A : ℚ[X]) (S : Finset ℕ) :
    muX A S = C (mu (A /ₘ poleDen S)) + ∑ j ∈ S, C (residue A S j) * muPole j := rfl

theorem dd_natCast (j : ℕ) : dd (j : ℤ) = j := by simp [dd]

theorem dd_neg_natCast {j : ℕ} (hj : 1 ≤ j) : dd (-(j : ℤ)) = j - 1 := by
  have := dd_of_neg (show -(j : ℤ) < 0 by omega)
  omega

theorem poleSet_erase {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) (hS : 0 ∉ S) :
    poleProd (poleSet S) =
      (X - C (j : ℚ)) * (X + C (j : ℚ)) * poleProd (poleSet (S.erase j)) := by
  rw [poleProd_poleSet S hS, poleProd_poleSet _ (fun h => hS (mem_of_mem_erase h)),
    ← mul_prod_erase S _ hj]

/-- The pullback (3.1): `μ_X(A / D_S) = τ_X(x⁵ A(-x²) / D_S(-x²))`. -/
theorem tauR_pull_poleDen_mul (S : Finset ℕ) (hS : 0 ∉ S) (Q : ℚ[X]) :
    tauR (poleSet S) (pull S (poleDen S * Q)) = C (mu Q) := by
  have : pull S (poleDen S * Q) = poleProd (poleSet S) * (X ^ 5 * Q.comp (-X ^ 2)) := by
    rw [pull, mul_comp, poleDen_comp_neg_sq S hS]
    have h1 : C ((-1 : ℚ) ^ S.card) * C ((-1 : ℚ) ^ S.card) = 1 := by
      rw [← C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1]
    linear_combination (X ^ 5 * poleProd (poleSet S) * Q.comp (-X ^ 2)) * h1
  rw [this, tauR_poleProd_mul, mu_eq_taup]

theorem tauR_pull_poleDen_erase {S : Finset ℕ} (hS : 0 ∉ S) {j : ℕ} (hj : j ∈ S) :
    tauR (poleSet S) (pull S (poleDen (S.erase j))) = muPole j := by
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 fun h => hS (h ▸ hj)
  have hS' : 0 ∉ S.erase j := fun h => hS (mem_of_mem_erase h)
  set Pp := poleProd (poleSet (S.erase j))
  have hmem : (j : ℤ) ∈ poleSet S := mem_union_left _ (mem_image_of_mem _ hj)
  have hmem' : -(j : ℤ) ∈ poleSet S := mem_union_right _ (mem_image_of_mem _ hj)
  have hP := poleSet_erase hj hS
  have e1 : poleProd ((poleSet S).erase (j : ℤ)) = (X + C (j : ℚ)) * Pp := by
    have h := poleProd_eq_mul_erase hmem
    rw [hP] at h
    have hne : (X - C (j : ℚ)) ≠ 0 := X_sub_C_ne_zero _
    push_cast at h
    exact (mul_left_cancel₀ hne (by rw [← h]; ring)).symm
  have e2 : poleProd ((poleSet S).erase (-(j : ℤ))) = (X - C (j : ℚ)) * Pp := by
    have h := poleProd_eq_mul_erase hmem'
    rw [hP] at h
    have hne : (X + C (j : ℚ)) ≠ 0 := by
      rw [← sub_neg_eq_add, ← C_neg]; exact X_sub_C_ne_zero _
    push_cast at h
    rw [C_neg, sub_neg_eq_add] at h
    exact (mul_left_cancel₀ hne (by rw [← h]; ring)).symm
  have hpull : pull S (poleDen (S.erase j)) =
      poleProd (poleSet S) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X) +
      C (-(j : ℚ) ^ 4 / 2) * (poleProd ((poleSet S).erase (j : ℤ)) +
        poleProd ((poleSet S).erase (-(j : ℤ)))) := by
    rw [pull, poleDen_comp_neg_sq _ hS', e1, e2, hP, card_erase_of_mem hj]
    have hc : ((-1 : ℚ) ^ S.card) * (-1) ^ (S.card - 1) = -1 := by
      rw [← pow_add]
      have : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (card_pos.2 ⟨j, hj⟩)
      rw [show S.card + (S.card - 1) = 2 * (S.card - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num
    have hc' : C ((-1 : ℚ) ^ S.card) * C ((-1) ^ (S.card - 1)) = -1 := by
      rw [← C_mul, hc, C_neg, C_1]
    have h2 : 2 * C (-(j : ℚ) ^ 4 / 2) = -(C (j : ℚ)) ^ 4 := by
      rw [← C_pow, ← C_neg, show (2 : ℚ[X]) = C 2 from rfl, ← C_mul]
      congr 1; ring
    have hj2 : C ((j : ℚ) ^ 2) = C (j : ℚ) ^ 2 := C_pow
    rw [hj2]
    linear_combination (X ^ 5 * Pp) * hc' - (X * Pp) * h2
  rw [hpull, tauR_add, tauR_poleProd_mul, tauR_C_mul, tauR_add, tauR_basis hmem,
    tauR_basis hmem', dd_natCast, dd_neg_natCast hj1]
  have k3 : taup (X ^ 3) = 1 / 4 := by
    have := kappa_eq 3
    rw [kappa] at this
    rw [this]; norm_num [Nat.descFactorial]
  have k1 : taup X = 0 := by
    have := kappa_eq 1
    rw [kappa, pow_one] at this
    rw [this]; simp [Nat.descFactorial]
  have hk : taup (-X ^ 3 - C ((j : ℚ) ^ 2) * X) = -1 / 4 := by
    rw [map_sub, map_neg, ← smul_eq_C_mul, map_smul, k3, k1]; ring
  have hH : H5 j = H5 (j - 1) + ((j : ℚ))⁻¹ ^ 5 := by
    have := H5_succ_rat (j - 1)
    rwa [Nat.sub_add_cancel hj1, show ((j - 1 : ℕ) : ℚ) + 1 = j by
      rw [Nat.cast_sub hj1]; ring] at this
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [hk, muPole, hH]
  ext n
  simp only [coeff_add, coeff_sub, coeff_C, coeff_C_mul, coeff_X]
  rcases n with _ | _ | n
  · simp only [ite_true, ite_false, one_ne_zero]
    field_simp
    ring
  · simp
    ring
  · simp

/-- The pullback (3.1): `μ_X(A / D_S) = τ_X(x⁵ A(-x²) / D_S(-x²))`. -/
theorem muX_eq_tauR (A : ℚ[X]) (S : Finset ℕ) (hS : 0 ∉ S) :
    muX A S = tauR (poleSet S) (pull S A) := by
  have hA := modByMonic_add_div A (poleDen S)
  rw [modByMonic_poleDen] at hA
  conv_rhs => rw [← hA]
  rw [pull_add, tauR_add, tauR_pull_poleDen_mul S hS, pull_sum, tauR_sum, muX_eq, add_comm]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [show C (residue A S j) * poleDen (S.erase j) = residue A S j • poleDen (S.erase j) from
    (smul_eq_C_mul _).symm, pull_smul, tauR_smul, tauR_pull_poleDen_erase hS hj]

end Zeta5
