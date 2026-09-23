/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Tactic.NormNum
import Zeta5.Defs

/-!
# The rational constants of §5–§7

* `Zeta5.Ubar`: the constant `Ū` of (6.4), an upper bound for `λM₀ - I(ρ) + C*`.
* `Zeta5.Astar`, `Zeta5.AM`: the constants (5.19) and (5.20), which bound the growth (5.21) of the
  normalisation `m_{K,M}`.
* `Zeta5.margin_72`: the inequality (7.2) with its exact margin, as in Appendix B.3.

The values of `Astar` and of the integrals behind it are reproduced exactly by
`scripts/check_constants.py`; their derivation is part of Phase 6.
-/

namespace Zeta5

/-- (6.4): `Ū = -2733991/2000000`. -/
def Ubar : ℚ := -2733991 / 2000000

/-- (5.19): `A* = I_out + ∫_3^{20} R(x) x⁻³ dx - 2689/48000`. -/
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- (5.20): `A_M = A* + 7λ/M - (2923/240 - 1/4)/M² + 32/M³`. -/
def AM (M : ℕ) : ℚ := Astar + 7 * lambda / M - (2923 / 240 - 1 / 4) / M ^ 2 + 32 / M ^ 3

theorem AM_200 : AM 200 = 127125602969131786927559 / 94195881588024216000000 := by
  norm_num [AM, Astar, lambda]

/-- (7.2) with the exact margin of Appendix B.3. -/
theorem margin_72 :
    -1600 * (AM 200 + Ubar) - 139 / 5 = 3089837638249482469 / 58872425992515135000 := by
  norm_num [AM_200, Ubar]

theorem margin_72_pos : 139 / 5 < -1600 * (AM 200 + Ubar) := by
  have := margin_72
  linarith [show (0 : ℚ) < 3089837638249482469 / 58872425992515135000 by norm_num]

end Zeta5
