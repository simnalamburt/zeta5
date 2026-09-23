/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Zeta5.Defs
import Zeta5.Degree
import Zeta5.Gram
import Zeta5.Integrality
import Zeta5.PrimeSum
import Zeta5.RealBound

/-!
# Theorem 2.1, split into four statements

Theorem 2.1 of the paper says that for `M ≥ 40` and `K ∈ 40ℤ_{>0}` with `K ≥ 200M²` the
polynomial `Q_{K,M}` has integer coefficients, degree `h` and a positive value at `ζ(5)`, and that
`Q_{40n,200}(ζ(5)) < exp(-139n²/5)` for all large `n`. We state the four parts separately; each is
proved in its own phase of `PLAN.md`:

* `Zeta5.QKM_natDegree`: the degree, from (2.9) (§2.3). Proved in `Zeta5.Degree`.
* `Zeta5.QKM_pos`: positivity at `ζ(5)`, from the Gram representation (Proposition 2.2).
  Proved in `Zeta5.Gram`.
* `Zeta5.QKM_mem_int`: integrality (Proposition 5.1), from the local estimates of §3–§5.
* `Zeta5.QKM_decay`: the decay (2.7), from Proposition 6.3, (5.21) and (7.2).

The degree and positivity statements hold for every `n` and `M`, since `m_{K,M}` and `S_K` are
positive for all parameters.
-/

open Polynomial Filter

namespace Zeta5

/-- Proposition 5.1: for `M ≥ 40` and `K ≥ 200M²`, `Q_{K,M} ∈ ℤ[X]`. -/
theorem QKM_mem_int {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) :
    ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = Q n M :=
  QKM_integral hM hK

/-- (2.9): `Q_{K,M}` has degree exactly `h`. Proved in `Zeta5.Degree`. -/
theorem QKM_natDegree (n M : ℕ) : (Q n M).natDegree = dim n :=
  natDegree_Q n M

/-- Proposition 2.2: `G_K(ζ(5))` is a positive definite Gram matrix, so `Q_{K,M}(ζ(5)) > 0`.
Proved in `Zeta5.Gram`. -/
theorem QKM_pos (n M : ℕ) : 0 < aeval (riemannZeta 5).re (Q n M) :=
  aeval_Q_pos n M

/-- (2.7): `Q_{40n,200}(ζ(5)) < exp(-139n²/5)` for all sufficiently large `n`.

This is (7.1) and (7.2): Proposition 6.3 (`Zeta5.realBound`) and (5.21) (`Zeta5.normFactor_growth`)
give `log Q_{K,200}(ζ(5)) ≤ (A_200 + Ū + ε) K²` eventually, and `-1600 (A_200 + Ū) > 139/5`
(`Zeta5.margin_72_pos`). -/
theorem QKM_decay :
    ∀ᶠ n : ℕ in atTop,
      aeval (riemannZeta 5).re (Q n 200) < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) := by
  set δ : ℝ := -1600 * ((AM 200 : ℝ) + Ubar) - 139 / 5 with hδ
  have hδpos : 0 < δ := by
    have h : ((139 / 5 : ℚ) : ℝ) < ((-1600 * (AM 200 + Ubar) : ℚ) : ℝ) :=
      Rat.cast_lt.2 margin_72_pos
    push_cast at h
    linarith
  have hε : 0 < δ / 6400 := by positivity
  filter_upwards [normFactor_growth (M := 200) (by norm_num) (by norm_num) hε, realBound hε,
    eventually_ge_atTop 1] with n hm hF hn
  have hmpos : (0 : ℝ) < normFactor n 200 := by exact_mod_cast normFactor_pos n 200
  have hQ : aeval (riemannZeta 5).re (Q n 200) =
      normFactor n 200 * aeval (riemannZeta 5).re (F n) := by
    rw [Q, map_mul, aeval_C, eq_ratCast]
  have hFpos : 0 < aeval (riemannZeta 5).re (F n) := by
    have h := aeval_Q_pos n 200
    rw [hQ] at h
    exact pos_of_mul_pos_right h hmpos.le
  rw [← Real.exp_log (QKM_pos n 200), Real.exp_lt_exp, hQ,
    Real.log_mul hmpos.ne' hFpos.ne']
  have hK : (K n : ℝ) = 40 * n := by simp [K]
  rw [hK] at hm hF
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU : (Ubar : ℝ) = -((139 / 5 + δ) / 1600) - AM 200 := by rw [hδ]; ring
  rw [hU] at hF
  have key : ((AM 200 : ℝ) + δ / 6400) * (40 * n) ^ 2 +
      (-((139 / 5 + δ) / 1600) - AM 200 + δ / 6400) * (40 * n) ^ 2 =
      -(139 / 5) * (n : ℝ) ^ 2 - δ / 2 * (n : ℝ) ^ 2 := by ring
  have hpos : 0 < δ / 2 * (n : ℝ) ^ 2 := by positivity
  linarith

end Zeta5
