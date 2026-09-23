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
    ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = Q n M := by
  sorry

/-- (2.9): `Q_{K,M}` has degree exactly `h`. Proved in `Zeta5.Degree`. -/
theorem QKM_natDegree (n M : ℕ) : (Q n M).natDegree = dim n :=
  natDegree_Q n M

/-- Proposition 2.2: `G_K(ζ(5))` is a positive definite Gram matrix, so `Q_{K,M}(ζ(5)) > 0`.
Proved in `Zeta5.Gram`. -/
theorem QKM_pos (n M : ℕ) : 0 < aeval (riemannZeta 5).re (Q n M) :=
  aeval_Q_pos n M

/-- (2.7): `Q_{40n,200}(ζ(5)) < exp(-139n²/5)` for all sufficiently large `n`. -/
theorem QKM_decay :
    ∀ᶠ n : ℕ in atTop,
      aeval (riemannZeta 5).re (Q n 200) < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) := by
  sorry

end Zeta5
