/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Zeta5.Constants

/-!
# The growth of the normalisation (5.21)

`limsup_{K → ∞, 40 ∣ K} K⁻² log m_{K,M} ≤ A_M` for `M ∈ 40ℤ_{>0}` (§5 and Appendix B).
-/

open Filter

namespace Zeta5

/-- (5.21), in the form: for every `ε > 0`, eventually `log m_{K,M} ≤ (A_M + ε) K²`. -/
theorem normFactor_growth {M : ℕ} (hM : 40 ≤ M) (hM40 : 40 ∣ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (normFactor n M) ≤ ((AM M : ℝ) + ε) * (K n : ℝ) ^ 2 := by
  sorry

end Zeta5
