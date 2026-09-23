/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Defs

/-!
# Tests for `Zeta5.Defs`

Small cases of the definitions, compared with the exact reference implementation
`scripts/zeta5_defs.py` and `scripts/check_local.py` of Phase 0. The expected values were produced
by those scripts.
-/

open Polynomial

namespace Zeta5.Test

/-! ### (2.2), (2.3) -/

theorem muMon_zero : muMon 0 = 5 / 12 := by
  rw [muMon, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  norm_num [bernoulli'_two]

theorem muMon_one : muMon 1 = 7 / 24 := by
  rw [muMon, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  norm_num [bernoulli'_four]

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, h5, Nat.choose]
  norm_num

example : muMon 2 = 1 / 2 := by
  rw [muMon, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  norm_num [bernoulli'_six]

example : H5 2 = 33 / 32 := by
  simp [H5, Finset.sum_Icc_succ_top]
  norm_num

theorem muPole_one : muPole 1 = X - C (3 / 4) := by
  apply Polynomial.funext
  intro x
  simp [muPole, H5]
  norm_num
  ring

theorem muPole_two : muPole 2 = C 16 * X - C (33 / 2) := by
  simp only [muPole, H5]
  rw [Finset.sum_Icc_succ_top (by norm_num)]
  apply Polynomial.funext
  intro x
  simp
  norm_num
  ring

theorem poleDen_one : poleDen {1} = X + C 1 := by
  simp [poleDen]

/-- `μ_X(1/(t+1)) = X - 3/4`: the quotient is zero and the residue is one. -/
example : muX 1 {1} = X - C (3 / 4) := by
  have hq : (1 : ℚ[X]) /ₘ poleDen {1} = 0 := by
    rw [poleDen_one, divByMonic_eq_zero_iff (monic_X_add_C 1), degree_one, degree_X_add_C]
    norm_num
  rw [muX, hq]
  simp only [map_zero, residue, eval_one, poleDen_one, map_one, derivative_add, derivative_X,
    derivative_one, add_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_mul,
    Finset.sum_singleton, muPole_one, zero_add]

/-- `μ_X(t/(t+1)) = μ(1) - μ_X(1/(t+1)) = 7/6 - X`, which fixes the sign of the residue. -/
example : muX X {1} = C (7 / 6) - X := by
  have hq : (X : ℚ[X]) /ₘ poleDen {1} = 1 := by
    rw [poleDen_one]
    refine (div_modByMonic_unique 1 (C (-1)) (monic_X_add_C 1) ⟨?_, ?_⟩).1
    · simp [map_neg]
    · rw [degree_C (by norm_num), degree_X_add_C]; norm_num
  have hmu : mu 1 = 5 / 12 := by
    rw [← monomial_zero_one, mu_monomial, muMon_zero, mul_one]
  rw [muX, hq, hmu]
  simp only [residue, eval_X, poleDen_one, map_one, derivative_add, derivative_X, derivative_one,
    add_zero, eval_one, div_one, map_neg, map_pow, map_natCast, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_singleton, Nat.cast_one, one_pow, muPole_one, one_mul, neg_sub]
  rw [show (7 / 6 : ℚ) = 5 / 12 + 3 / 4 by norm_num, map_add]
  ring

theorem poleDen_one_two : poleDen {1, 2} = (X + C 1) * (X + C 4) := by
  rw [poleDen, Finset.prod_pair (by norm_num)]
  norm_num

/-- `μ_X(t³/((t+1)(t+4))) = 341X - 8485/24`: quotient `t - 5`, residues `-1/3` and `64/3`. -/
example : muX (X ^ 3) {1, 2} = C 341 * X - C (8485 / 24) := by
  have hq : (X ^ 3 : ℚ[X]) /ₘ poleDen {1, 2} = X - C 5 := by
    refine (div_modByMonic_unique (X - C 5) (C 21 * X + C 20) (poleDen_monic _) ⟨?_, ?_⟩).1
    · rw [poleDen_one_two]
      simp only [map_ofNat, map_one]
      ring
    · rw [degree_linear (by norm_num), degree_eq_natDegree (poleDen_monic _).ne_zero,
        natDegree_poleDen]
      decide
  have hmu : mu (X - C 5) = -43 / 24 := by
    rw [map_sub, ← monomial_one_one_eq_X, ← monomial_zero_left, mu_monomial, mu_monomial,
      muMon_zero, muMon_one]
    norm_num
  rw [muX, hq, hmu, Finset.sum_pair (by norm_num), muPole_one, muPole_two]
  simp only [residue, poleDen_one_two]
  apply Polynomial.funext
  intro x
  simp
  norm_num
  ring

/-! ### The exponents of §4 (values from `scripts/check_local.py`) -/

example : Inner.ell 7 40 1 = 11 ∧ Inner.ell 7 40 2 = 12 ∧ Inner.ell 7 3 3 = 1 := by decide

example : Outer.gammaOut 17 1 = -124 ∧ Outer.gammaOut 23 1 = -110 ∧ Outer.gammaOut 37 1 = -4 ∧
    Outer.gammaOut 41 1 = 0 := by decide

example : Outer.gammaOut 29 2 = -281 ∧ Outer.gammaOut 41 2 = -232 ∧ Outer.gammaOut 79 2 = -2 := by
  decide

example : Outer.gammaOut 41 3 = -410 ∧ Outer.gammaOut 53 3 = -365 ∧ Outer.gammaOut 113 3 = -8 := by
  decide

example : Inner.gammaIn 13 1 4 = -186 := by decide

example : Inner.gammaIn 23 2 4 = -216 ∧ Inner.gammaIn 29 3 5 = -273 ∧
    Inner.gammaIn 31 3 4 = -292 ∧ Inner.gammaIn 37 3 4 = -329 := by decide

example : Inner.gammaIn 37 3 10 = -441 ∧ Inner.gammaIn 41 4 4 = -365 := by decide

end Zeta5.Test
