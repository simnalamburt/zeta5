/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Enclose
import Zeta5.PotentialData
import Zeta5.Rho
import Zeta5.VClosed

/-!
# The potential inequality (6.2) on `(0, 2]`

Lemma 6.1 of the paper: `2U^ρ(t) - V(t) ≤ M₀ = -1329/200`. On `(0, 2]` this is the numerical
verification (A.9) of Appendix A. For an interval `[l, r]`:

* `U^ρ = ∑ c_j U^{ω_j}`, and each `U^{ω_j}(t)` is a nondecreasing function of `|t - m_j|`
  (`Zeta5.arcsinePot_mono`), so `U^{ω_j} ≤ max(U^{ω_j}(l), U^{ω_j}(r))` on `[l, r]`;
* `V` decreases on `(0, q₋]` and increases on `[q₊, ∞)` (`Zeta5.Vfield_antitone`,
  `Zeta5.Vfield_monotone`, with `P(√q₋) < 0 < P(√q₊)` checked numerically), and on `[q₋, q₊]` it
  is bounded below by the monotone pieces of (A.5) (`Zeta5.VLoRange_le`); this is `B(l, r)` of
  (A.7).

`Zeta5.checkIv` evaluates these bounds with the rational enclosures of `Zeta5.Enclose`, and
`Zeta5.checkChain` runs it on the consecutive points of a list; `decide +kernel` runs it on the
684 intervals of Table 2.
-/

open Real Set

namespace Zeta5

open Enclose

/-- `M₀ = -1329/200`, the bound (6.2) for `2U^ρ - V`. -/
def M0 : ℚ := -1329 / 200

theorem M0_real : (M0 : ℝ) = -1329 / 200 := by rw [M0]; push_cast; ring

/-! ### Precision -/

/-- Rounding to multiples of `2⁻⁴⁰`. -/
abbrev prec : ℕ := 40

/-- Terms of the `artanh` series for `log`. -/
abbrev nLog : ℕ := 10

/-- Terms of the `arctan` series: `2 mAtan` and `2 mAtan + 1`. -/
abbrev mAtan : ℕ := 16

/-! ### Rational data -/

/-- `m_j` as a rational. -/
def ctrQ (j : Fin 16) : ℚ := ((tabA j : ℚ) + tabB j) / 2 / 10 ^ 12

/-- `R_j` as a rational. -/
def radQ (j : Fin 16) : ℚ := ((tabB j : ℚ) - tabA j) / 2 / 10 ^ 12

/-- `c_j` as a rational. -/
def wgtQ (j : Fin 16) : ℚ := (tabC j : ℚ) / 10 ^ 12

theorem ctrQ_cast (j : Fin 16) : (ctrQ j : ℝ) = ctr j := by unfold ctrQ ctr; push_cast; ring

theorem radQ_cast (j : Fin 16) : (radQ j : ℝ) = rad j := by unfold radQ rad; push_cast; ring

theorem wgtQ_cast (j : Fin 16) : (wgtQ j : ℝ) = wgt j := by unfold wgtQ wgt; push_cast; ring

theorem radQ_pos (j : Fin 16) : 0 < radQ j := by
  have := rad_pos j
  rw [← radQ_cast] at this
  exact_mod_cast this

/-! ### The potential of `ρ` -/

theorem arcsinePot_eq (m : ℝ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    arcsinePot m R t = log (R / 2) + log (max 1 (|t - m| / R + √((|t - m| / R) ^ 2 - 1))) := by
  rw [arcsinePot, abs_div, abs_of_pos hR, div_pow, div_pow, sq_abs]

/-- The potential of an arcsine measure is a nondecreasing function of `|t - m|`. -/
theorem arcsinePot_mono (m : ℝ) {R : ℝ} (hR : 0 < R) {t t' : ℝ} (h : |t - m| ≤ |t' - m|) :
    arcsinePot m R t ≤ arcsinePot m R t' := by
  rw [arcsinePot_eq m hR, arcsinePot_eq m hR]
  have h1 : |t - m| / R ≤ |t' - m| / R := div_le_div_of_nonneg_right h hR.le
  have h2 : (|t - m| / R) ^ 2 ≤ (|t' - m| / R) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : √((|t - m| / R) ^ 2 - 1) ≤ √((|t' - m| / R) ^ 2 - 1) := sqrt_le_sqrt (by linarith)
  have h4 := max_le_max (le_refl (1 : ℝ)) (add_le_add h1 h3)
  have h5 := log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) h4
  linarith

theorem arcsinePot_le_max (m : ℝ) {R : ℝ} (hR : 0 < R) {l r t : ℝ} (hlt : l ≤ t) (htr : t ≤ r) :
    arcsinePot m R t ≤ max (arcsinePot m R l) (arcsinePot m R r) := by
  rcases le_total m t with h | h
  · refine (arcsinePot_mono m hR ?_).trans (le_max_right _ _)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · refine (arcsinePot_mono m hR ?_).trans (le_max_left _ _)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- An upper bound of `log(R_j/2)`. -/
def logRadHi (j : Fin 16) : ℚ := logHi nLog prec (radQ j / 2)

/-- An upper bound of `U^{ω_j}(t)`. -/
def potHi (j : Fin 16) (t : ℚ) : ℚ :=
  logRadHi j + if |(t - ctrQ j) / radQ j| ≤ 1 then 0 else
    logHi nLog prec (|(t - ctrQ j) / radQ j| + sqrtHi prec (((t - ctrQ j) / radQ j) ^ 2 - 1))

theorem arcsinePot_le_potHi (j : Fin 16) (t : ℚ) :
    arcsinePot (ctr j) (rad j) t ≤ potHi j t := by
  have hRQ := radQ_pos j
  rw [arcsinePot, ← ctrQ_cast, ← radQ_cast]
  unfold potHi
  set c : ℚ := (t - ctrQ j) / radQ j with hc
  have hc' : ((t : ℝ) - ctrQ j) / radQ j = (c : ℝ) := by rw [hc]; push_cast; ring
  rw [hc']
  have hlog : log ((radQ j : ℝ) / 2) ≤ logRadHi j := by
    have := le_logHi nLog prec (x := radQ j / 2) (by positivity)
    push_cast at this
    exact this
  split_ifs with h
  · have h1 : |(c : ℝ)| ≤ 1 := by exact_mod_cast h
    have h2 : (c : ℝ) ^ 2 - 1 ≤ 0 := by nlinarith [sq_abs (c : ℝ), abs_nonneg (c : ℝ)]
    rw [sqrt_eq_zero'.2 h2, add_zero, max_eq_left h1, Real.log_one]
    push_cast
    linarith
  · have h1 : 1 < |(c : ℝ)| := by exact_mod_cast not_le.1 h
    have hc2 : 0 ≤ c ^ 2 - 1 := by
      have : 1 < |c| := not_le.1 h
      nlinarith [sq_abs c, abs_nonneg c]
    have hs := le_sqrtHi prec hc2
    push_cast at hs
    have hs0 : 0 ≤ √((c : ℝ) ^ 2 - 1) := sqrt_nonneg _
    rw [max_eq_right (by linarith)]
    have hpos : 0 < |c| + sqrtHi prec (c ^ 2 - 1) := by
      have : (0 : ℝ) < |(c : ℝ)| + sqrtHi prec (c ^ 2 - 1) := by linarith
      exact_mod_cast this
    have h2 := le_logHi nLog prec hpos
    have h3 : log (|(c : ℝ)| + √((c : ℝ) ^ 2 - 1)) ≤ log (|(c : ℝ)| + sqrtHi prec (c ^ 2 - 1)) :=
      log_le_log (by linarith) (by linarith)
    push_cast at h2 ⊢
    linarith

/-- An upper bound of `U^ρ` on `[l, r]`. -/
def UHi (l r : ℚ) : ℚ := ∑ j, wgtQ j * max (potHi j l) (potHi j r)

theorem Urho_le_UHi {l r : ℚ} {t : ℝ} (hlt : (l : ℝ) ≤ t) (htr : t ≤ r) : Urho t ≤ UHi l r := by
  unfold Urho UHi
  push_cast
  refine Finset.sum_le_sum fun j _ => ?_
  rw [wgtQ_cast]
  refine mul_le_mul_of_nonneg_left ?_ (wgt_pos j).le
  exact (arcsinePot_le_max _ (rad_pos j) hlt htr).trans
    (max_le_max (arcsinePot_le_potHi j l) (arcsinePot_le_potHi j r))

/-! ### The field -/

/-- A lower bound of `V` on `[a, b]`, from the monotone pieces of (A.5). -/
def VLoRange (a b : ℚ) : ℚ :=
  -3 * piHi * sqrtHi prec b + logLo nLog prec (1 + a) -
    6 * (3 / 40) * logHi nLog prec (b + (3 / 40) ^ 2) -
    2 * sqrtHi prec b * atanHi prec mAtan (sqrtHi prec b) +
    12 * sqrtLo prec a * atanLo prec mAtan (sqrtLo prec a / (3 / 40)) - 2 + 12 * (3 / 40)

theorem VLoRange_le {a b : ℚ} (ha : 0 < a) {t : ℝ} (hat : (a : ℝ) ≤ t) (htb : t ≤ b) :
    (VLoRange a b : ℝ) ≤ Vfield t := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ht : 0 < t := ha'.trans_le hat
  have hb : (0 : ℚ) ≤ b := by exact_mod_cast (ht.le.trans htb)
  rw [Vfield_eq ht, Phi]
  set s := √t with hs
  have hs0 : 0 ≤ s := sqrt_nonneg t
  have hss : s ^ 2 = t := sq_sqrt ht.le
  set sl : ℚ := sqrtLo prec a
  set sh : ℚ := sqrtHi prec b
  have hsl : (sl : ℝ) ≤ s := (sqrtLo_le prec ha.le).trans (sqrt_le_sqrt hat)
  have hsh : s ≤ sh := (sqrt_le_sqrt htb).trans (le_sqrtHi prec hb)
  have hsl0 : (0 : ℝ) ≤ sl := by exact_mod_cast sqrtLo_nonneg prec a
  have hsh0 : (0 : ℝ) ≤ sh := hs0.trans hsh
  -- `-3πs`
  have p1 : π * s ≤ piHi * sh := mul_le_mul le_piHi hsh hs0 (by linarith [le_piHi, pi_pos])
  -- `log(1 + s²)`
  have p2 : (logLo nLog prec (1 + a) : ℝ) ≤ log (1 + s ^ 2) := by
    have := logLo_le nLog prec (x := 1 + a) (by linarith)
    push_cast at this
    rw [hss]
    exact this.trans (log_le_log (by linarith) (by linarith))
  -- `log(s² + α²)`
  have p3 : log (s ^ 2 + (3 / 40) ^ 2) ≤ (logHi nLog prec (b + (3 / 40) ^ 2) : ℝ) := by
    have := le_logHi nLog prec (x := b + (3 / 40) ^ 2) (by positivity)
    push_cast at this
    rw [hss]
    exact (log_le_log (by positivity) (by linarith)).trans this
  -- `s arctan s`
  have p4 : s * arctan s ≤ sh * (atanHi prec mAtan sh : ℝ) := by
    have h1 := (arctan_strictMono.monotone hsh).trans (le_atanHi prec mAtan (x := sh) (by
      exact_mod_cast hsh0))
    exact mul_le_mul hsh h1 (arctan_nonneg.2 hs0) hsh0
  -- `s arctan(s/α)`
  have p5 : (sl : ℝ) * (atanLo prec mAtan (sl / (3 / 40)) : ℝ) ≤ s * arctan (s / (3 / 40)) := by
    have h1 : (atanLo prec mAtan (sl / (3 / 40)) : ℝ) ≤ arctan (s / (3 / 40)) := by
      have := atanLo_le prec mAtan (x := sl / (3 / 40)) (by
        have : (0 : ℚ) ≤ sl := sqrtLo_nonneg prec a
        positivity)
      push_cast at this
      exact this.trans (arctan_strictMono.monotone (by gcongr))
    have h2 : 0 ≤ arctan (s / (3 / 40)) := arctan_nonneg.2 (by positivity)
    calc (sl : ℝ) * (atanLo prec mAtan (sl / (3 / 40)) : ℝ) ≤ sl * arctan (s / (3 / 40)) :=
          mul_le_mul_of_nonneg_left h1 hsl0
      _ ≤ s * arctan (s / (3 / 40)) := mul_le_mul_of_nonneg_right hsl h2
  unfold VLoRange
  push_cast
  linarith

/-! ### The minimum of `V` -/

/-- `q₋ = 59205077/10¹⁰`. -/
def qm : ℚ := 59205077 / 10 ^ 10

/-- `q₊ = 59205079/10¹⁰`. -/
def qp : ℚ := 59205079 / 10 ^ 10

/-- An upper bound of `P(√q)`. -/
def PdHiQ (q : ℚ) : ℚ :=
  -3 * piLo / 2 - atanLo prec mAtan (sqrtLo prec q) +
    6 * atanHi prec mAtan (sqrtHi prec q / (3 / 40))

/-- A lower bound of `P(√q)`. -/
def PdLoQ (q : ℚ) : ℚ :=
  -3 * piHi / 2 - atanHi prec mAtan (sqrtHi prec q) +
    6 * atanLo prec mAtan (sqrtLo prec q / (3 / 40))

theorem Pd_le_PdHiQ {q : ℚ} (hq : 0 ≤ q) : Pd √(q : ℝ) ≤ PdHiQ q := by
  have hsl : (sqrtLo prec q : ℝ) ≤ √(q : ℝ) := sqrtLo_le prec hq
  have hsh : √(q : ℝ) ≤ sqrtHi prec q := le_sqrtHi prec hq
  have hsl0 := sqrtLo_nonneg prec q
  have hsh0 : (0 : ℚ) ≤ sqrtHi prec q := by exact_mod_cast (sqrt_nonneg _).trans hsh
  have h1 := atanLo_le prec mAtan hsl0
  have h2 := le_atanHi prec mAtan (x := sqrtHi prec q / (3 / 40)) (by positivity)
  have h3 := arctan_strictMono.monotone hsl
  have h4 : arctan (√(q : ℝ) / (3 / 40)) ≤ arctan ((sqrtHi prec q : ℝ) / (3 / 40)) :=
    arctan_strictMono.monotone (by gcongr)
  have := piLo_le
  unfold Pd PdHiQ
  push_cast at h2 ⊢
  linarith

theorem PdLoQ_le_Pd {q : ℚ} (hq : 0 ≤ q) : (PdLoQ q : ℝ) ≤ Pd √(q : ℝ) := by
  have hsl : (sqrtLo prec q : ℝ) ≤ √(q : ℝ) := sqrtLo_le prec hq
  have hsh : √(q : ℝ) ≤ sqrtHi prec q := le_sqrtHi prec hq
  have hsl0 := sqrtLo_nonneg prec q
  have hsh0 : (0 : ℚ) ≤ sqrtHi prec q := by exact_mod_cast (sqrt_nonneg _).trans hsh
  have h1 := le_atanHi prec mAtan hsh0
  have h2 := atanLo_le prec mAtan (x := sqrtLo prec q / (3 / 40)) (by positivity)
  have h3 := arctan_strictMono.monotone hsh
  have h4 : arctan ((sqrtLo prec q : ℝ) / (3 / 40)) ≤ arctan (√(q : ℝ) / (3 / 40)) :=
    arctan_strictMono.monotone (by gcongr)
  have := le_piHi
  unfold Pd PdLoQ
  push_cast at h2 ⊢
  linarith

theorem Pd_qm_nonpos : Pd √(qm : ℝ) ≤ 0 := by
  have h : PdHiQ qm ≤ 0 := by decide +kernel
  exact (Pd_le_PdHiQ (by norm_num [qm])).trans (by exact_mod_cast h)

theorem Pd_qp_nonneg : 0 ≤ Pd √(qp : ℝ) := by
  have h : 0 ≤ PdLoQ qp := by decide +kernel
  exact le_trans (by exact_mod_cast h) (PdLoQ_le_Pd (by norm_num [qp]))

theorem sqrt_qm_le : √(qm : ℝ) ≤ 1 / 2 := by
  rw [sqrt_le_left (by norm_num)]; norm_num [qm]

theorem sqrt_qp_le : √(qp : ℝ) ≤ 1 / 2 := by
  rw [sqrt_le_left (by norm_num)]; norm_num [qp]

/-- A lower bound of `V` on `[l, r]`: `B(l, r)` of (A.7). -/
def VLo (l r : ℚ) : ℚ :=
  if r ≤ qm then VLoRange r r else if qp ≤ l then VLoRange l l else VLoRange qm qp

theorem VLo_le {l r : ℚ} {t : ℝ} (ht0 : 0 < t) (hlt : (l : ℝ) ≤ t) (htr : t ≤ r) :
    (VLo l r : ℝ) ≤ Vfield t := by
  have hqm : (0 : ℚ) < qm := by norm_num [qm]
  have hqp : (0 : ℚ) < qp := by norm_num [qp]
  have hqmp : (qm : ℝ) ≤ qp := by norm_num [qm, qp]
  unfold VLo
  split_ifs with h1 h2
  · have hr : (0 : ℚ) < r := by exact_mod_cast ht0.trans_le htr
    exact (VLoRange_le hr le_rfl le_rfl).trans
      (Vfield_antitone sqrt_qm_le Pd_qm_nonpos ht0 htr (by exact_mod_cast h1))
  · have hl : (0 : ℚ) < l := hqp.trans_le h2
    exact (VLoRange_le hl le_rfl le_rfl).trans
      (Vfield_monotone sqrt_qp_le Pd_qp_nonneg (by exact_mod_cast hqp) (by exact_mod_cast h2) hlt)
  · rcases le_total t qm with h | h
    · exact (VLoRange_le hqm le_rfl hqmp).trans
        (Vfield_antitone sqrt_qm_le Pd_qm_nonpos ht0 h le_rfl)
    · rcases le_total t qp with h' | h'
      · exact VLoRange_le hqm h h'
      · exact (VLoRange_le hqm hqmp le_rfl).trans
          (Vfield_monotone sqrt_qp_le Pd_qp_nonneg (by exact_mod_cast hqp) le_rfl h')

/-! ### The check -/

/-- The check of (A.9) on `[l, r]`. -/
def checkIv (l r : ℚ) : Bool := decide (l ≤ r) && decide (2 * UHi l r - VLo l r ≤ M0)

theorem checkIv_sound {l r : ℚ} (h : checkIv l r = true) {t : ℝ} (ht0 : 0 < t)
    (hlt : (l : ℝ) ≤ t) (htr : t ≤ r) : 2 * Urho t - Vfield t ≤ M0 := by
  unfold checkIv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := Urho_le_UHi hlt htr
  have h2 := VLo_le ht0 hlt htr
  have h3 : ((2 * UHi l r - VLo l r : ℚ) : ℝ) ≤ M0 := by exact_mod_cast h.2
  push_cast at h3
  linarith

/-- The check of (A.9) on the consecutive intervals `[a, p₁], [p₁, p₂], …` of a list. -/
def checkChain : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: rest => checkIv a b && checkChain b rest

/-- The last point of `a :: rest`. -/
def chainLast : ℚ → List ℚ → ℚ
  | a, [] => a
  | _, b :: rest => chainLast b rest

theorem checkChain_sound : ∀ (rest : List ℚ) (a : ℚ), checkChain a rest = true →
    ∀ t : ℝ, (a : ℝ) < t → t ≤ chainLast a rest → 0 < t → 2 * Urho t - Vfield t ≤ M0
  | [], a, _, t, h1, h2, _ => absurd (h1.trans_le h2) (lt_irrefl _)
  | b :: rest, a, h, t, h1, h2, h0 => by
    simp only [checkChain, Bool.and_eq_true] at h
    by_cases htb : t ≤ b
    · exact checkIv_sound h.1 h0 h1.le htb
    · exact checkChain_sound rest b h.2 t (not_le.1 htb) h2 h0

/-! ### Table 2, in nine chunks of 76 intervals -/

/-- The first point of the `k`-th chunk. -/
def chunkStart (k : ℕ) : ℚ := table2Points.getD (76 * k) 0

/-- The remaining points of the `k`-th chunk. -/
def chunkPts (k : ℕ) : List ℚ := (table2Points.drop (76 * k + 1)).take 76

theorem chunkStart_zero : chunkStart 0 = 0 := by decide +kernel

theorem chunkStart_nine : chunkStart 9 = 2 := by decide +kernel

theorem chainLast_chunk : ∀ k < 9, chainLast (chunkStart k) (chunkPts k) = chunkStart (k + 1) := by
  decide +kernel

theorem chunk_ok_0 : checkChain (chunkStart 0) (chunkPts 0) = true := by decide +kernel
theorem chunk_ok_1 : checkChain (chunkStart 1) (chunkPts 1) = true := by decide +kernel
theorem chunk_ok_2 : checkChain (chunkStart 2) (chunkPts 2) = true := by decide +kernel
theorem chunk_ok_3 : checkChain (chunkStart 3) (chunkPts 3) = true := by decide +kernel
theorem chunk_ok_4 : checkChain (chunkStart 4) (chunkPts 4) = true := by decide +kernel
theorem chunk_ok_5 : checkChain (chunkStart 5) (chunkPts 5) = true := by decide +kernel
theorem chunk_ok_6 : checkChain (chunkStart 6) (chunkPts 6) = true := by decide +kernel
theorem chunk_ok_7 : checkChain (chunkStart 7) (chunkPts 7) = true := by decide +kernel
theorem chunk_ok_8 : checkChain (chunkStart 8) (chunkPts 8) = true := by decide +kernel

theorem chunk_ok : ∀ k < 9, checkChain (chunkStart k) (chunkPts k) = true := by
  intro k hk
  interval_cases k
  exacts [chunk_ok_0, chunk_ok_1, chunk_ok_2, chunk_ok_3, chunk_ok_4, chunk_ok_5, chunk_ok_6,
    chunk_ok_7, chunk_ok_8]

/-- A point of `(s 0, s m]` lies in some `(s k, s (k+1)]`. -/
theorem exists_chunk (s : ℕ → ℝ) : ∀ m : ℕ, ∀ t : ℝ, s 0 < t → t ≤ s m →
    ∃ k < m, s k < t ∧ t ≤ s (k + 1)
  | 0, t, h1, h2 => absurd (h1.trans_le h2) (lt_irrefl _)
  | m + 1, t, h1, h2 => by
    by_cases h : t ≤ s m
    · obtain ⟨k, hk, hk'⟩ := exists_chunk s m t h1 h
      exact ⟨k, by omega, hk'⟩
    · exact ⟨m, by omega, not_le.1 h, h2⟩

/-- **Lemma 6.1**, (6.2) on `(0, 2]`: `2U^ρ(t) - V(t) ≤ M₀`. -/
theorem potential_le_M0 {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : 2 * Urho t - Vfield t ≤ M0 := by
  obtain ⟨k, hk, h1, h2⟩ := exists_chunk (fun k => (chunkStart k : ℝ)) 9 t
    (by rw [chunkStart_zero]; exact_mod_cast ht) (by rw [chunkStart_nine]; exact_mod_cast ht2)
  refine checkChain_sound _ _ (chunk_ok k hk) t h1 ?_ ht
  rw [chainLast_chunk k hk]
  exact h2

end Zeta5
