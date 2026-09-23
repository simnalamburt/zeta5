/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.Floor

/-!
# Rational enclosures of `log`, `√`, `arctan` and `π`

Computable rational lower and upper bounds, with proofs, for the numerical part of Appendix A
(`A.2`: rational enclosures for logarithms, arctangents and square roots). The functions are
designed to be evaluated by the kernel (`decide +kernel`), so they use structural recursion and
round intermediate results to multiples of `2⁻ᵖ` to keep the numbers small.

* `log`: `x = 2ᵉ y` with `1 ≤ y < 2`, and `log y = 2 artanh((y-1)/(y+1))`, whose series has
  nonnegative terms; the tail is bounded by a geometric series.
* `arctan`: the alternating series on `[0, 1/2]`, with `arctan x = π/4 - arctan((1-x)/(1+x))` and
  `arctan x = π/2 - arctan(1/x)` for the reduction.
* `√`: any guess `s` with `s² ≤ x` (or `x ≤ s²`) is checked; the guess is Newton's method.
* `π`: the 20-digit bounds of Mathlib.
-/

open Real

namespace Zeta5.Enclose

/-! ### Rounding -/

/-- Round down to a multiple of `2⁻ᵖ`. -/
def rdown (p : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ p⌋ : ℚ) / 2 ^ p

/-- Round up to a multiple of `2⁻ᵖ`. -/
def rup (p : ℕ) (q : ℚ) : ℚ := -rdown p (-q)

theorem rdown_le (p : ℕ) (q : ℚ) : rdown p q ≤ q := by
  unfold rdown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_rup (p : ℕ) (q : ℚ) : q ≤ rup p q := by
  unfold rup; linarith [rdown_le p (-q)]

theorem rdown_nonneg (p : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ rdown p q := by
  unfold rdown
  have : (0 : ℤ) ≤ ⌊q * 2 ^ p⌋ := Int.floor_nonneg.2 (by positivity)
  have : (0 : ℚ) ≤ ⌊q * 2 ^ p⌋ := by exact_mod_cast this
  positivity

theorem cast_rdown_le (p : ℕ) (q : ℚ) : (rdown p q : ℝ) ≤ q := by exact_mod_cast rdown_le p q

theorem le_cast_rup (p : ℕ) (q : ℚ) : (q : ℝ) ≤ rup p q := by exact_mod_cast le_rup p q

/-! ### The logarithm -/

/-- `2 ∑_{k<n} z^{2k+1}/(2k+1)`, the partial sums of `log((1+z)/(1-z))`. -/
def atanhSum (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum z n + 2 * z ^ (2 * n + 1) / (2 * n + 1)

/-- The tail bound `2 z^{2n+1} / ((2n+1)(1 - z²))`. -/
def atanhTail (z : ℚ) (n : ℕ) : ℚ := 2 * z ^ (2 * n + 1) / ((2 * n + 1) * (1 - z ^ 2))

theorem atanhSum_cast (z : ℚ) (n : ℕ) :
    (atanhSum z n : ℝ) = ∑ k ∈ Finset.range n, 2 * (1 / (2 * k + 1)) * (z : ℝ) ^ (2 * k + 1) := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih =>
    rw [atanhSum, Finset.sum_range_succ, ← ih]
    push_cast
    ring

theorem atanhSum_mono {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    atanhSum a n ≤ atanhSum b n := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih =>
    rw [atanhSum, atanhSum]
    have : a ^ (2 * n + 1) ≤ b ^ (2 * n + 1) := pow_le_pow_left₀ ha hab _
    have h2 : (0 : ℚ) < 2 * n + 1 := by positivity
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num : (0:ℚ) ≤ 2))
      h2.le
    linarith

theorem atanhTail_mono {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (n : ℕ) :
    atanhTail a n ≤ atanhTail b n := by
  unfold atanhTail
  have h1 : a ^ (2 * n + 1) ≤ b ^ (2 * n + 1) := pow_le_pow_left₀ ha hab _
  have h2 : 0 < 1 - b ^ 2 := by nlinarith
  have h3 : 1 - b ^ 2 ≤ 1 - a ^ 2 := by nlinarith
  have h4 : (0 : ℚ) < 2 * n + 1 := by positivity
  have hb0 : 0 ≤ b := ha.trans hab
  have h6 : 0 < 1 - a ^ 2 := by linarith
  rw [div_le_div_iff₀ (mul_pos h4 h6) (mul_pos h4 h2)]
  have h5 : 0 ≤ a ^ (2 * n + 1) := by positivity
  have h7 : 0 ≤ b ^ (2 * n + 1) := by positivity
  calc 2 * a ^ (2 * n + 1) * ((2 * n + 1) * (1 - b ^ 2))
      ≤ 2 * b ^ (2 * n + 1) * ((2 * n + 1) * (1 - b ^ 2)) := by gcongr
    _ ≤ 2 * b ^ (2 * n + 1) * ((2 * n + 1) * (1 - a ^ 2)) := by gcongr

theorem hasSum_log_div {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1))
      (log ((1 + z) / (1 - z))) := by
  rw [log_div (by linarith) (by linarith)]
  exact hasSum_log_sub_log_of_abs_lt_one (by rw [abs_of_nonneg hz0]; exact hz1)

theorem atanhSum_le {z : ℚ} (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    (atanhSum z n : ℝ) ≤ log ((1 + z) / (1 - z)) := by
  have hz0' : (0 : ℝ) ≤ z := by exact_mod_cast hz0
  have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
  rw [atanhSum_cast]
  exact sum_le_hasSum _ (fun k _ => by positivity) (hasSum_log_div hz0' hz1')

theorem le_atanhSum_add {z : ℚ} (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    log ((1 + z) / (1 - z)) ≤ (atanhSum z n : ℝ) + atanhTail z n := by
  have hz0' : (0 : ℝ) ≤ z := by exact_mod_cast hz0
  have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
  have h := hasSum_log_div hz0' hz1'
  have htail := (hasSum_nat_add_iff' n).2 h
  have hz2 : (z : ℝ) ^ 2 < 1 := by nlinarith
  have hgeom : HasSum (fun k : ℕ => 2 * (z : ℝ) ^ (2 * n + 1) / (2 * n + 1) * ((z : ℝ) ^ 2) ^ k)
      (2 * (z : ℝ) ^ (2 * n + 1) / (2 * n + 1) * (1 - (z : ℝ) ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle := hasSum_le (fun k => ?_) htail hgeom
  · rw [atanhSum_cast, atanhTail]
    push_cast
    have : 2 * (z : ℝ) ^ (2 * n + 1) / (2 * n + 1) * (1 - (z : ℝ) ^ 2)⁻¹ =
        2 * (z : ℝ) ^ (2 * n + 1) / ((2 * n + 1) * (1 - (z : ℝ) ^ 2)) := by
      field_simp
    linarith
  · have hk : (1 : ℝ) / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * n + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    have hp : (z : ℝ) ^ (2 * (k + n) + 1) = (z : ℝ) ^ (2 * n + 1) * ((z : ℝ) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * (z : ℝ) ^ (2 * (k + n) + 1)
        ≤ 2 * (1 / (2 * n + 1)) * (z : ℝ) ^ (2 * (k + n) + 1) := by gcongr
      _ = 2 * (z : ℝ) ^ (2 * n + 1) / (2 * n + 1) * ((z : ℝ) ^ 2) ^ k := by rw [hp]; ring

/-- For `y ≥ 1`, with `z = (y-1)/(y+1)`: `(1+z)/(1-z) = y`. -/
theorem one_add_div_one_sub {y : ℚ} (hy : 1 ≤ y) :
    (1 + ((y - 1) / (y + 1) : ℚ)) / (1 - (y - 1) / (y + 1)) = y := by
  have : y + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Lower bound of `log y` for `y ≥ 1`. -/
def logGeLo (n p : ℕ) (y : ℚ) : ℚ := atanhSum (rdown p ((y - 1) / (y + 1))) n

/-- Upper bound of `log y` for `y ≥ 1`. -/
def logGeHi (n p : ℕ) (y : ℚ) : ℚ :=
  let z := rup p ((y - 1) / (y + 1))
  if z < 1 then atanhSum z n + atanhTail z n else y - 1

theorem logGeLo_le (n p : ℕ) {y : ℚ} (hy : 1 ≤ y) : (logGeLo n p y : ℝ) ≤ log y := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have h := atanhSum_le (rdown_nonneg p hz0) ((rdown_le p z).trans_lt hz1) n
  have hmono : log ((1 + (rdown p z : ℝ)) / (1 - rdown p z)) ≤ log ((1 + (z : ℝ)) / (1 - z)) := by
    have h1 : (rdown p z : ℝ) ≤ z := cast_rdown_le p z
    have h0 : (0 : ℝ) ≤ rdown p z := by exact_mod_cast rdown_nonneg p hz0
    have hz1' : (z : ℝ) < 1 := by exact_mod_cast hz1
    refine log_le_log (div_pos (by linarith) (by linarith)) ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hy' : ((1 + (z : ℝ)) / (1 - z)) = y := by exact_mod_cast one_add_div_one_sub hy
  rw [hy'] at hmono
  exact h.trans hmono

theorem le_logGeHi (n p : ℕ) {y : ℚ} (hy : 1 ≤ y) : log y ≤ (logGeHi n p y : ℝ) := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  unfold logGeHi
  dsimp only
  split_ifs with h
  · have hzz := le_rup p z
    have h1 := le_atanhSum_add hz0 hz1 n
    have hy' : ((1 + (z : ℝ)) / (1 - z)) = y := by exact_mod_cast one_add_div_one_sub hy
    rw [hy'] at h1
    have h2 := atanhSum_mono hz0 hzz n
    have h3 := atanhTail_mono hz0 hzz h n
    have : (atanhSum z n : ℝ) + atanhTail z n ≤ atanhSum (rup p z) n + atanhTail (rup p z) n := by
      exact_mod_cast add_le_add h2 h3
    push_cast
    linarith
  · push_cast
    exact (log_le_sub_one_of_pos (by exact_mod_cast (by linarith : (0 : ℚ) < y)))

/-- A computation of `e` with `2⁻ᵉ x ∈ [1, 2)`; its correctness is not needed. -/
def findExp : ℕ → ℚ → ℤ → ℤ
  | 0, _, e => e
  | n + 1, y, e => if y < 1 then findExp n (2 * y) (e - 1) else
      if 2 ≤ y then findExp n (y / 2) (e + 1) else e

/-- `log 2 > 0.6931471805599453094`. -/
def log2Lo : ℚ := 6931471805599453094 / 10 ^ 19

/-- `log 2 < 0.6931471805599453095`. -/
def log2Hi : ℚ := 6931471805599453095 / 10 ^ 19

theorem log2Lo_le : (log2Lo : ℝ) ≤ log 2 := by
  have h := logGeLo_le 20 80 (y := 2) (by norm_num)
  have : log2Lo ≤ logGeLo 20 80 2 := by decide +kernel
  have : (log2Lo : ℝ) ≤ logGeLo 20 80 2 := by exact_mod_cast this
  push_cast at h
  linarith

theorem le_log2Hi : log 2 ≤ (log2Hi : ℝ) := by
  have h := le_logGeHi 20 80 (y := 2) (by norm_num)
  have : logGeHi 20 80 2 ≤ log2Hi := by decide +kernel
  have : (logGeHi 20 80 2 : ℝ) ≤ log2Hi := by exact_mod_cast this
  push_cast at h
  linarith

/-- Lower bound of `log y` for `y > 0`. -/
def logPosLo (n p : ℕ) (y : ℚ) : ℚ := if 1 ≤ y then logGeLo n p y else -logGeHi n p y⁻¹

/-- Upper bound of `log y` for `y > 0`. -/
def logPosHi (n p : ℕ) (y : ℚ) : ℚ := if 1 ≤ y then logGeHi n p y else -logGeLo n p y⁻¹

theorem logPosLo_le (n p : ℕ) {y : ℚ} (hy : 0 < y) : (logPosLo n p y : ℝ) ≤ log y := by
  unfold logPosLo
  split_ifs with h
  · exact logGeLo_le n p h
  · have h1 : 1 ≤ y⁻¹ := (one_le_inv₀ hy).2 (by linarith [not_le.1 h])
    have := le_logGeHi n p h1
    push_cast at this ⊢
    rw [log_inv] at this
    linarith

theorem le_logPosHi (n p : ℕ) {y : ℚ} (hy : 0 < y) : log y ≤ (logPosHi n p y : ℝ) := by
  unfold logPosHi
  split_ifs with h
  · exact le_logGeHi n p h
  · have h1 : 1 ≤ y⁻¹ := (one_le_inv₀ hy).2 (by linarith [not_le.1 h])
    have := logGeLo_le n p h1
    push_cast at this ⊢
    rw [log_inv] at this
    linarith

/-- Lower bound of `log x` for `x > 0`: `log x = e log 2 + log (2⁻ᵉ x)`. -/
def logLo (n p : ℕ) (x : ℚ) : ℚ :=
  let e := findExp 400 x 0
  rdown p (e * (if 0 ≤ e then log2Lo else log2Hi) + logPosLo n p (x / 2 ^ e))

/-- Upper bound of `log x` for `x > 0`. -/
def logHi (n p : ℕ) (x : ℚ) : ℚ :=
  let e := findExp 400 x 0
  rup p (e * (if 0 ≤ e then log2Hi else log2Lo) + logPosHi n p (x / 2 ^ e))

theorem log_eq_exp_add {x : ℝ} (hx : 0 < x) (e : ℤ) :
    log x = e * log 2 + log (x / 2 ^ e) := by
  rw [log_div hx.ne' (by positivity), Real.log_zpow]
  ring

theorem logLo_le (n p : ℕ) {x : ℚ} (hx : 0 < x) : (logLo n p x : ℝ) ≤ log x := by
  unfold logLo
  set e := findExp 400 x 0
  have hy : 0 < x / 2 ^ e := by positivity
  have h1 := logPosLo_le n p hy
  have h2 : (e : ℝ) * ((if 0 ≤ e then log2Lo else log2Hi : ℚ) : ℝ) ≤ e * log 2 := by
    split_ifs with he
    · exact mul_le_mul_of_nonneg_left log2Lo_le (by exact_mod_cast he)
    · exact mul_le_mul_of_nonpos_left le_log2Hi (by exact_mod_cast (not_le.1 he).le)
  refine (cast_rdown_le _ _).trans ?_
  rw [log_eq_exp_add (by exact_mod_cast hx) e]
  push_cast at h1 h2 ⊢
  linarith

theorem le_logHi (n p : ℕ) {x : ℚ} (hx : 0 < x) : log x ≤ (logHi n p x : ℝ) := by
  unfold logHi
  set e := findExp 400 x 0
  have hy : 0 < x / 2 ^ e := by positivity
  have h1 := le_logPosHi n p hy
  have h2 : e * log 2 ≤ (e : ℝ) * ((if 0 ≤ e then log2Hi else log2Lo : ℚ) : ℝ) := by
    split_ifs with he
    · exact mul_le_mul_of_nonneg_left le_log2Hi (by exact_mod_cast he)
    · exact mul_le_mul_of_nonpos_left log2Lo_le (by exact_mod_cast (not_le.1 he).le)
  refine le_trans ?_ (le_cast_rup _ _)
  rw [log_eq_exp_add (by exact_mod_cast hx) e]
  push_cast at h1 h2 ⊢
  linarith

/-! ### `π` -/

/-- `π > 3.14159265358979323846`. -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

/-- `π < 3.14159265358979323847`. -/
def piHi : ℚ := 314159265358979323847 / 10 ^ 20

theorem piLo_le : (piLo : ℝ) ≤ π := by
  have := pi_gt_d20
  unfold piLo
  push_cast
  norm_num at this ⊢
  linarith

theorem le_piHi : π ≤ (piHi : ℝ) := by
  have := pi_lt_d20
  unfold piHi
  push_cast
  norm_num at this ⊢
  linarith

/-! ### The arctangent -/

/-- `∑_{k<m} (-1)^k x^{2k+1}/(2k+1)`. -/
def atanSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => atanSum x m + (-1) ^ m * x ^ (2 * m + 1) / (2 * m + 1)

theorem atanSum_cast (x : ℚ) (m : ℕ) :
    (atanSum x m : ℝ) =
      ∑ i ∈ Finset.range m, (-1) ^ i * ((x : ℝ) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero => simp [atanSum]
  | succ m ih =>
    rw [atanSum, Finset.sum_range_succ, ← ih]
    push_cast
    ring

theorem tendsto_atanSum {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Filter.Tendsto (fun m => ∑ i ∈ Finset.range m,
      (-1) ^ i * ((x : ℝ) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))) Filter.atTop
      (nhds (arctan x)) := by
  have hx : ‖(x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hx0)]; exact_mod_cast hx1
  have := (Real.hasSum_arctan hx).tendsto_sum_nat
  simpa only [mul_div_assoc] using this

theorem antitone_atanTerm {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Antitone fun i : ℕ => (x : ℝ) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have h1 : (x : ℝ) ≤ 1 := by exact_mod_cast hx1.le
  refine antitone_nat_of_succ_le fun i => ?_
  have hp : (x : ℝ) ^ (2 * (i + 1) + 1) ≤ (x : ℝ) ^ (2 * i + 1) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hd : ((2 * i + 1 : ℕ) : ℝ) ≤ ((2 * (i + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * i + 1 ≤ 2 * (i + 1) + 1)
  exact div_le_div₀ (by positivity) hp (by positivity) hd

theorem atanSum_even_le {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    (atanSum x (2 * m) : ℝ) ≤ arctan x := by
  rw [atanSum_cast]
  exact Antitone.alternating_series_le_tendsto (tendsto_atanSum hx0 hx1)
    (antitone_atanTerm hx0 hx1) m

theorem le_atanSum_odd {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    arctan x ≤ (atanSum x (2 * m + 1) : ℝ) := by
  rw [atanSum_cast]
  exact Antitone.tendsto_le_alternating_series (tendsto_atanSum hx0 hx1)
    (antitone_atanTerm hx0 hx1) m

/-- Lower bound of `arctan x` for `0 ≤ x < 1`, accurate for `x ≤ 1/2`. -/
def atan0Lo (p m : ℕ) (x : ℚ) : ℚ :=
  if rdown p x < 1 then atanSum (rdown p x) (2 * m) else 0

/-- Upper bound of `arctan x` for `0 ≤ x`, accurate for `x ≤ 1/2`. -/
def atan0Hi (p m : ℕ) (x : ℚ) : ℚ :=
  if rup p x < 1 then atanSum (rup p x) (2 * m + 1) else piHi / 2

theorem atan0Lo_le (p m : ℕ) {x : ℚ} (hx : 0 ≤ x) : (atan0Lo p m x : ℝ) ≤ arctan x := by
  unfold atan0Lo
  split_ifs with h
  · refine (atanSum_even_le (rdown_nonneg p hx) h m).trans ?_
    exact arctan_strictMono.monotone (cast_rdown_le p x)
  · push_cast
    exact arctan_nonneg.2 (by exact_mod_cast hx)

theorem le_atan0Hi (p m : ℕ) {x : ℚ} (hx : 0 ≤ x) : arctan x ≤ (atan0Hi p m x : ℝ) := by
  unfold atan0Hi
  split_ifs with h
  · exact (arctan_strictMono.monotone (le_cast_rup p x)).trans
      (le_atanSum_odd (hx.trans (le_rup p x)) h m)
  · push_cast
    have := le_piHi
    linarith [arctan_lt_pi_div_two (x : ℝ)]

theorem arctan_add_arctan_div {x : ℝ} (hx0 : 0 ≤ x) :
    arctan x + arctan ((1 - x) / (1 + x)) = π / 4 := by
  have h1 : 0 < 1 + x := by linarith
  rw [arctan_add (by rw [mul_div_assoc', div_lt_one h1]; nlinarith), ← arctan_one]
  congr 1
  have e1 : x + (1 - x) / (1 + x) = (1 + x ^ 2) / (1 + x) := by field_simp; ring
  have e2 : 1 - x * ((1 - x) / (1 + x)) = (1 + x ^ 2) / (1 + x) := by field_simp; ring
  rw [e1, e2, div_self (by positivity)]

/-- Lower bound of `arctan x` for `0 ≤ x ≤ 1`. -/
def atanMidLo (p m : ℕ) (x : ℚ) : ℚ :=
  if 1 / 2 < x then piLo / 4 - atan0Hi p m ((1 - x) / (1 + x)) else atan0Lo p m x

/-- Upper bound of `arctan x` for `0 ≤ x ≤ 1`. -/
def atanMidHi (p m : ℕ) (x : ℚ) : ℚ :=
  if 1 / 2 < x then piHi / 4 - atan0Lo p m ((1 - x) / (1 + x)) else atan0Hi p m x

theorem atanMidLo_le (p m : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (atanMidLo p m x : ℝ) ≤ arctan x := by
  unfold atanMidLo
  split_ifs with h
  · have hw : 0 ≤ (1 - x) / (1 + x) := div_nonneg (by linarith) (by linarith)
    have h1 := le_atan0Hi p m hw
    have h2 := arctan_add_arctan_div (x := (x : ℝ)) (by exact_mod_cast hx0)
    have := piLo_le
    push_cast at h1 ⊢
    linarith
  · exact atan0Lo_le p m hx0

theorem le_atanMidHi (p m : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    arctan x ≤ (atanMidHi p m x : ℝ) := by
  unfold atanMidHi
  split_ifs with h
  · have hw : 0 ≤ (1 - x) / (1 + x) := div_nonneg (by linarith) (by linarith)
    have h1 := atan0Lo_le p m hw
    have h2 := arctan_add_arctan_div (x := (x : ℝ)) (by exact_mod_cast hx0)
    have := le_piHi
    push_cast at h1 ⊢
    linarith
  · exact le_atan0Hi p m hx0

/-- Lower bound of `arctan x` for `x ≥ 0`. -/
def atanLo (p m : ℕ) (x : ℚ) : ℚ :=
  if 1 < x then piLo / 2 - atanMidHi p m x⁻¹ else atanMidLo p m x

/-- Upper bound of `arctan x` for `x ≥ 0`. -/
def atanHi (p m : ℕ) (x : ℚ) : ℚ :=
  if 1 < x then piHi / 2 - atanMidLo p m x⁻¹ else atanMidHi p m x

theorem atanLo_le (p m : ℕ) {x : ℚ} (hx : 0 ≤ x) : (atanLo p m x : ℝ) ≤ arctan x := by
  unfold atanLo
  split_ifs with h
  · have hx' : (0 : ℝ) < x := by exact_mod_cast (zero_lt_one.trans h)
    have h1 := le_atanMidHi p m (inv_nonneg.2 hx) (inv_le_one_of_one_le₀ h.le)
    have h2 := arctan_inv_of_pos hx'
    have := piLo_le
    push_cast at h1 ⊢
    linarith
  · exact atanMidLo_le p m hx (not_lt.1 h)

theorem le_atanHi (p m : ℕ) {x : ℚ} (hx : 0 ≤ x) : arctan x ≤ (atanHi p m x : ℝ) := by
  unfold atanHi
  split_ifs with h
  · have hx' : (0 : ℝ) < x := by exact_mod_cast (zero_lt_one.trans h)
    have h1 := atanMidLo_le p m (inv_nonneg.2 hx) (inv_le_one_of_one_le₀ h.le)
    have h2 := arctan_inv_of_pos hx'
    have := le_piHi
    push_cast at h1 ⊢
    linarith
  · exact le_atanMidHi p m hx (not_lt.1 h)

/-! ### The square root -/

/-- Newton's method for `√x`, rounded up. -/
def sqrtNewton (p : ℕ) (x : ℚ) : ℕ → ℚ → ℚ
  | 0, s => s
  | k + 1, s => sqrtNewton p x k (rup p ((s + x / s) / 2))

/-- An upper bound of `√x` for `x ≥ 0`. -/
def sqrtHi (p : ℕ) (x : ℚ) : ℚ :=
  let s := sqrtNewton p x 10 (2 ^ (findExp 400 x 0 / 2 + 1))
  if 0 ≤ s ∧ x ≤ s * s then s else x + 1

/-- A lower bound of `√x` for `x ≥ 0`. -/
def sqrtLo (p : ℕ) (x : ℚ) : ℚ :=
  let s := rdown p (x / sqrtHi p x)
  if 0 ≤ s ∧ s * s ≤ x then s else 0

theorem le_sqrtHi (p : ℕ) {x : ℚ} (hx : 0 ≤ x) : √(x : ℝ) ≤ (sqrtHi p x : ℝ) := by
  unfold sqrtHi
  dsimp only
  split_ifs with h
  · rw [sqrt_le_left (by exact_mod_cast h.1)]
    exact_mod_cast (by nlinarith [h.2] : x ≤ _ ^ 2)
  · rw [sqrt_le_left (by push_cast; positivity)]
    push_cast
    nlinarith [(by exact_mod_cast hx : (0 : ℝ) ≤ x)]

theorem sqrtLo_le (p : ℕ) {x : ℚ} (hx : 0 ≤ x) : (sqrtLo p x : ℝ) ≤ √(x : ℝ) := by
  unfold sqrtLo
  dsimp only
  split_ifs with h
  · rw [le_sqrt (by exact_mod_cast h.1) (by exact_mod_cast hx)]
    exact_mod_cast (by nlinarith [h.2] : _ ^ 2 ≤ x)
  · push_cast
    exact sqrt_nonneg _

theorem sqrtLo_nonneg (p : ℕ) (x : ℚ) : 0 ≤ sqrtLo p x := by
  unfold sqrtLo
  dsimp only
  split_ifs with h
  · exact h.1
  · exact le_rfl

end Zeta5.Enclose
