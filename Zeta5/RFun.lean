/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.AffineEx

/-!
# The limiting exponent `R(x)`

With `x = K/p`, the exponent `-L_p(K, M)` of a prime `p` with `K/M < p ≤ 2h` is at most
`p R(x) + O_M(1)`, where `R` is the function `Zeta5.Rx` below (`Zeta5.Inner.neg_Lexp_le`,
`Zeta5.Outer.neg_Lexp_le`). It is written as an expression `Zeta5.eR` so that its exact integral
can be checked by evaluation (`Zeta5/RCheck.lean`).

* For `x < 3` (the outer range and beyond, §5.2) `R(x) = x T_out(1/x)`, where `T_out` is the
  integrand of (5.10): `R₀ - d - 2λ⌊1/y⌋ + ∑_j (2λ - jy)₊`.
* For `x ≥ 3` (the inner range, §5.1) `R(x) = -Γ(x) - N(x)` with `N` of (5.5). Our `Γ` is not the
  formula (5.4) but a Lagrangian lower bound for `γ_p^in / p`: for every integer `μ`,
  `γ_p^in ≥ μ(h - L₀) - ∑_a ⌊(6ℓ_N(a) - ℓ_K(a) - 5 - μ)²/4⌋ + O(1)`, and the choice
  `μ = 2⌊2Hx⌋ - ⌊2x⌋ - 5 + [{2x} < {2Hx}]` makes this equal to (5.4) (checked exactly at 15109
  rational points by `scripts/gen_rdata.py`).
-/

namespace Zeta5

open Ex

namespace RFun

/-- The variable `x`. -/
abbrev x : Ex := var
/-- A rational constant. -/
abbrev c (q : ℚ) : Ex := cst q
/-- The fractional part. -/
def fr (e : Ex) : Ex := e - floor e
/-- The distance `min({e}, 1 - {e})` to the nearest integer. -/
def d0 (e : Ex) : Ex := min (fr e) (c 1 - fr e)
/-- The positive part. -/
def pos (e : Ex) : Ex := max e (c 0)

/-- `J(λx) = m λx - m(m+1)/4` with `m = ⌊2λx⌋`. -/
def eJ : Ex :=
  floor (c (37 / 20) * x) * (c (37 / 40) * x) -
    floor (c (37 / 20) * x) * (floor (c (37 / 20) * x) + c 1) * c (1 / 4)

/-- (5.5): `N(x) = 2λx⌊x⌋ - 12λx⌊αx⌋ - 2J(λx)`, the limit of `v_p(S_K)/p`. -/
def eN : Ex := c (37 / 20) * x * floor x - c (111 / 10) * x * floor (c (3 / 40) * x) - c 2 * eJ

/-- `-γ_p^out/p` for `K/2 < p ≤ K`, i.e. `1 ≤ x < 2`: `7(x-1) - 6t/p + r/p` in the limit. -/
def eG1 : Ex :=
  c 7 * (x - c 1) - c 6 * (min (c (3 / 40) * x) (x - c 1) + pos (c (43 / 40) * x - c 2)) +
    pos (c (13 / 10) * x - c 2)

/-- `-γ_p^out/p` for `K/3 < p ≤ K/2`, i.e. `2 ≤ x < 3`. -/
def eG2 : Ex :=
  c 7 * (x - c 1) - c (9 / 10) * x -
      c 5 * (min (c (3 / 40) * x) (x - c 2) + pos (c (43 / 40) * x - c 3)) +
    min (pos (c (13 / 10) * x - c 2)) (c 1 + pos (c (43 / 40) * x - c 3))

/-- The multiplier `μ = 2⌊2Hx⌋ - ⌊2x⌋ - 5 + [{2x} < {2Hx}]`. -/
def eMu : Ex :=
  c 2 * floor (c (23 / 10) * x) - floor (c 2 * x) - c 5 +
    ite (fr (c 2 * x)) (fr (c (23 / 10) * x)) (c 1) (c 0)

/-- `D = 12⌊αx⌋ - 2⌊x⌋ - μ`. -/
def eD : Ex := c 12 * floor (c (3 / 40) * x) - c 2 * floor x - eMu

/-- `σ_K = ±1`: `ℓ_K(a) = 2⌊x⌋ + 1 + σ_K [a/p > d₀({x})]`. -/
def eSK : Ex := c 2 * floor (c 2 * fr x) - c 1

/-- `σ_N = ±1`: `ℓ_N(a) = 2⌊αx⌋ + 1 + σ_N [a/p > d₀({αx})]`. -/
def eSN : Ex := c 2 * floor (c 2 * fr (c (3 / 40) * x)) - c 1

/-- `⌊e²/4⌋`. -/
def sq4 (e : Ex) : Ex := floor (e * e * c (1 / 4))

/-- `∫_0^{1/2} ⌊(6ℓ(αx, z) - ℓ(x, z) - 5 - μ)²/4⌋ dz`. -/
def eI : Ex :=
  sq4 eD * min (d0 x) (d0 (c (3 / 40) * x)) +
    sq4 (eD - eSK) * (d0 (c (3 / 40) * x) - min (d0 x) (d0 (c (3 / 40) * x))) +
    sq4 (eD + c 6 * eSN) * (d0 x - min (d0 x) (d0 (c (3 / 40) * x))) +
    sq4 (eD + c 6 * eSN - eSK) * (c (1 / 2) - max (d0 x) (d0 (c (3 / 40) * x)))

/-- `Γ(x) = μλx - ∫_0^{1/2} ⌊(6ℓ(αx, z) - ℓ(x, z) - 5 - μ)²/4⌋ dz`, the limit of `γ_p^in/p`. -/
def eGam : Ex := eMu * c (37 / 40) * x - eI

end RFun

open RFun in
/-- The limiting exponent `R(x)`: `-L_p(K, M) ≤ p R(K/p) + O(1)`. -/
def eR : Ex := ite x (c 1) (c 0) (ite x (c 2) eG1 (ite x (c 3) eG2 (c 0 - eGam))) - eN

/-- `R(x)` as a function. -/
def Rx (y : ℚ) : ℚ := eR.eval y

namespace RFun

variable (y : ℚ)

@[simp] theorem fr_eval (e : Ex) : (fr e).eval y = e.eval y - ⌊e.eval y⌋ := rfl
@[simp] theorem d0_eval (e : Ex) :
    (d0 e).eval y = min (e.eval y - ⌊e.eval y⌋) (1 - (e.eval y - ⌊e.eval y⌋)) := rfl
@[simp] theorem pos_eval (e : Ex) : (pos e).eval y = max (e.eval y) 0 := rfl
@[simp] theorem sq4_eval (e : Ex) : (sq4 e).eval y = ⌊e.eval y * e.eval y * (1 / 4)⌋ := rfl

theorem eMu_eval : eMu.eval y = 2 * ⌊23 / 10 * y⌋ - ⌊2 * y⌋ - 5 +
    if 2 * y - ⌊2 * y⌋ < 23 / 10 * y - ⌊23 / 10 * y⌋ then 1 else 0 := rfl

theorem eD_eval : eD.eval y = 12 * ⌊3 / 40 * y⌋ - 2 * ⌊y⌋ - eMu.eval y := rfl

theorem eSK_eval : eSK.eval y = 2 * ⌊2 * (y - ⌊y⌋)⌋ - 1 := rfl

theorem eSN_eval : eSN.eval y = 2 * ⌊2 * (3 / 40 * y - ⌊3 / 40 * y⌋)⌋ - 1 := rfl

theorem eI_eval : eI.eval y =
    (sq4 eD).eval y * min ((d0 x).eval y) ((d0 (c (3 / 40) * x)).eval y) +
      (sq4 (eD - eSK)).eval y *
        ((d0 (c (3 / 40) * x)).eval y - min ((d0 x).eval y) ((d0 (c (3 / 40) * x)).eval y)) +
      (sq4 (eD + c 6 * eSN)).eval y *
        ((d0 x).eval y - min ((d0 x).eval y) ((d0 (c (3 / 40) * x)).eval y)) +
      (sq4 (eD + c 6 * eSN - eSK)).eval y *
        (1 / 2 - max ((d0 x).eval y) ((d0 (c (3 / 40) * x)).eval y)) := rfl

theorem eGam_eval : eGam.eval y = eMu.eval y * (37 / 40) * y - eI.eval y := rfl

theorem eG1_eval : eG1.eval y = 7 * (y - 1) -
    6 * (Min.min (3 / 40 * y) (y - 1) + Max.max (43 / 40 * y - 2) 0) +
    Max.max (13 / 10 * y - 2) 0 := rfl

theorem eG2_eval : eG2.eval y = 7 * (y - 1) - 9 / 10 * y -
    5 * (Min.min (3 / 40 * y) (y - 2) + Max.max (43 / 40 * y - 3) 0) +
    Min.min (Max.max (13 / 10 * y - 2) 0) (1 + Max.max (43 / 40 * y - 3) 0) := rfl

theorem eR_eval_of_lt_one (hy : y < 1) : eR.eval y = -eN.eval y := by
  simp only [eR, Ex.eval_sub, Ex.eval_ite, Ex.eval_var, Ex.eval_cst]
  rw [if_pos hy]
  ring

theorem eR_eval_of_lt_two (hy1 : 1 ≤ y) (hy : y < 2) : eR.eval y = eG1.eval y - eN.eval y := by
  simp only [eR, Ex.eval_sub, Ex.eval_ite, Ex.eval_var, Ex.eval_cst]
  rw [if_neg (by linarith), if_pos hy]

theorem eR_eval_of_lt_three (hy1 : 2 ≤ y) (hy : y < 3) :
    eR.eval y = eG2.eval y - eN.eval y := by
  simp only [eR, Ex.eval_sub, Ex.eval_ite, Ex.eval_var, Ex.eval_cst]
  rw [if_neg (by linarith), if_neg (by linarith), if_pos hy]

theorem eR_eval_of_three_le (hy : 3 ≤ y) : eR.eval y = -eGam.eval y - eN.eval y := by
  simp only [eR, Ex.eval_sub, Ex.eval_ite, Ex.eval_var, Ex.eval_cst]
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
  ring

end RFun

end Zeta5
