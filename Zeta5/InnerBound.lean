/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.InnerRange
import Zeta5.ValS

/-!
# The inner exponent against its limit (5.7)

For a prime in the inner range `K/M < p ≤ K/3` we show `γ_p^in ≥ p Γ(K/p) - O_M(1)`, where `Γ` is
`Zeta5.RFun.eGam`. The paper derives (5.7) by comparing the allocation (4.4) with its continuous
limit; we instead use a Lagrangian lower bound that needs no knowledge of the allocation beyond
`∑_a L_a = h - L₀`:

* the rows of the class `a` contribute `L_a (L_a + c_a)` with `c_a = 6ℓ_N(a) - ℓ_K(a) - 5`, and
  for every integer `μ`, `L (L + c) ≥ μ L - ⌊(c - μ)²/4⌋`;
* `ℓ_K(a)` and `ℓ_N(a)` take two values each, switching at explicit thresholds `t_K, t_N`, so the
  sum over `a` of `⌊(c_a - μ)²/4⌋` is `p` times the integral `∫_0^{1/2} … dz` of `Zeta5.RFun.eI`
  up to `O(1)`.
-/

open Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The counts `ℓ_A(a)` exactly -/

omit hp in
theorem ell_succ (A a : ℕ) : Inner.ell p (A + 1) a =
    Inner.ell p A a + if A + 1 ≡ a [MOD p] ∨ A + 1 + a ≡ 0 [MOD p] then 1 else 0 := by
  simp only [Inner.ell, card_filter]
  rw [sum_Icc_succ_top (by omega)]

/-- `ℓ_A(a) = 2⌊A/p⌋ + [a ≤ A mod p] + [p ≤ A mod p + a]` for `1 ≤ a ≤ (p-1)/2`. -/
theorem ell_formula (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ (p - 1) / 2) (A : ℕ) :
    Inner.ell p A a = 2 * (A / p) + (if a ≤ A % p then 1 else 0) +
      (if p ≤ A % p + a then 1 else 0) := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; have := hp2; omega
  have hp0 : 0 < p := by omega
  have hap : a < p := by omega
  induction A with
  | zero =>
    simp only [Inner.ell, Nat.zero_div, Nat.zero_mod, zero_add]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  | succ A ih =>
    rw [ell_succ, ih]
    have e := Nat.div_add_mod A p
    have r := Nat.mod_lt A hp0
    rcases (show A % p + 1 = p ∨ A % p + 1 < p by omega) with h | h
    · have hq : (A + 1) / p = A / p + 1 ∧ (A + 1) % p = 0 :=
        (Nat.div_mod_unique hp0).2 ⟨by rw [Nat.mul_add]; omega, hp0⟩
      have c1 : ¬(A + 1 ≡ a [MOD p]) := by
        unfold Nat.ModEq; rw [hq.2, Nat.mod_eq_of_lt hap]; omega
      have c2 : ¬(A + 1 + a ≡ 0 [MOD p]) := by
        unfold Nat.ModEq
        rw [Nat.add_mod, hq.2, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hap, Nat.zero_mod]
        omega
      rw [if_neg (not_or.2 ⟨c1, c2⟩), hq.1, hq.2]
      split_ifs <;> omega
    · have hq : (A + 1) / p = A / p ∧ (A + 1) % p = A % p + 1 :=
        (Nat.div_mod_unique hp0).2 ⟨by omega, h⟩
      have c1 : (A + 1 ≡ a [MOD p]) ↔ A % p + 1 = a := by
        unfold Nat.ModEq; rw [hq.2, Nat.mod_eq_of_lt hap]
      have c2 : (A + 1 + a ≡ 0 [MOD p]) ↔ A % p + 1 + a = p := by
        unfold Nat.ModEq
        rw [Nat.add_mod, hq.2, Nat.mod_eq_of_lt hap, Nat.zero_mod]
        constructor
        · intro h'
          exact Nat.eq_of_dvd_of_lt_two_mul (by omega) (Nat.dvd_of_mod_eq_zero h') (by omega)
        · intro h'; rw [h', Nat.mod_self]
      rw [hq.1, hq.2]
      simp only [c1, c2]
      split_ifs <;> omega

/-- The threshold `t_A`: `ℓ_A(a)` switches between `2⌊A/p⌋ + 1` and its neighbour `2⌊A/p⌋ + 1 + σ_A`
at `a = t_A + 1`. -/
def tt (p A : ℕ) : ℕ := if 2 * (A % p) < p then A % p else p - A % p - 1

/-- The sign `σ_A = ±1`. -/
def ss (p A : ℕ) : ℤ := if 2 * (A % p) < p then -1 else 1

theorem ell_eq_tt (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ (p - 1) / 2) (A : ℕ) :
    (Inner.ell p A a : ℤ) = 2 * (A / p : ℕ) + 1 + ss p A * (if tt p A < a then 1 else 0) := by
  rw [ell_formula hp2 ha1 ham A]
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  simp only [tt, ss]
  split_ifs <;> push_cast <;> omega

theorem tt_le (hp2 : p ≠ 2) (A : ℕ) : tt p A ≤ (p - 1) / 2 := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have := Nat.mod_lt A hp.out.pos
  simp only [tt]
  split_ifs <;> omega

/-! ### Sums of the rows of a class -/

theorem sum_range_two_mul_add (L : ℕ) (c : ℤ) :
    ∑ i ∈ range L, (2 * (i : ℤ) + c) = L * (L - 1 + c) := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `L (L + e) ≥ -⌊e²/4⌋` for integers. -/
theorem mul_add_add_sq_div_four_nonneg (L e : ℤ) : 0 ≤ L * (L + e) + e ^ 2 / 4 := by
  obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' e
  · have : (2 * t) ^ 2 / 4 = t ^ 2 := by
      rw [show (2 * t) ^ 2 = 4 * t ^ 2 by ring]; omega
    rw [this]; nlinarith [sq_nonneg (L + t)]
  · have : (2 * t + 1) ^ 2 / 4 = t ^ 2 + t := by
      rw [show (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 by ring]; omega
    rw [this]
    rcases le_or_gt 0 (L + t) with h | h
    · nlinarith
    · nlinarith

/-! ### Sums over the classes of a function of two thresholds -/

theorem card_Icc_filter_lt {m t : ℕ} (_ht : t ≤ m) : #{a ∈ Icc 1 m | t < a} = m - t := by
  have : {a ∈ Icc 1 m | t < a} = Ioc t m := by ext; simp; omega
  rw [this, Nat.card_Ioc]

/-- `∑_{a=1}^m G([t₁ < a], [t₂ < a])` in terms of the thresholds. -/
theorem sum_two_thresholds {m t₁ t₂ : ℕ} (h₁ : t₁ ≤ m) (h₂ : t₂ ≤ m) (G : ℤ → ℤ → ℤ) :
    ∑ a ∈ Icc 1 m, G (if t₁ < a then 1 else 0) (if t₂ < a then 1 else 0) =
      G 0 0 * min t₁ t₂ + G 1 0 * (t₂ - min t₁ t₂ : ℤ) + G 0 1 * (t₁ - min t₁ t₂ : ℤ) +
        G 1 1 * (m - max t₁ t₂ : ℤ) := by
  have hpt : ∀ a ∈ Icc 1 m, G (if t₁ < a then 1 else 0) (if t₂ < a then 1 else 0) =
      G 0 0 + (G 1 0 - G 0 0) * (if t₁ < a then 1 else 0) +
        (G 0 1 - G 0 0) * (if t₂ < a then 1 else 0) +
        (G 1 1 - G 1 0 - G 0 1 + G 0 0) * (if max t₁ t₂ < a then 1 else 0) := by
    intro a _
    by_cases ha : t₁ < a <;> by_cases hb : t₂ < a <;>
      simp only [ha, hb, if_true, if_false, max_lt_iff, and_true, and_false] <;> ring
  rw [sum_congr rfl hpt]
  simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, sum_boole]
  have hm : max t₁ t₂ ≤ m := max_le h₁ h₂
  rw [card_Icc_filter_lt h₁, card_Icc_filter_lt h₂, card_Icc_filter_lt hm]
  push_cast [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub hm]
  simp only [nsmul_eq_mul]
  rcases le_total t₁ t₂ with h | h
  · have h' : (t₁ : ℤ) ≤ t₂ := by exact_mod_cast h
    rw [min_eq_left h', max_eq_right h']; ring
  · have h' : (t₂ : ℤ) ≤ t₁ := by exact_mod_cast h
    rw [min_eq_right h', max_eq_left h']; ring

/-- The class sum of a function of the two thresholds against `p` times its integral over
`z ∈ (0, 1/2)`, where the thresholds `t` sit at `p d(z)` up to one. -/
theorem thresholds_le_integral {G00 G10 G01 G11 : ℚ} (h00 : 0 ≤ G00) (h10 : 0 ≤ G10)
    (h01 : 0 ≤ G01) (h11 : 0 ≤ G11) {m tK tN : ℕ} {P dK dN : ℚ} (hP : 0 < P)
    (hm : 2 * (m : ℚ) + 1 = P) (hK1 : (tK : ℚ) ≤ P * dK) (hK2 : P * dK ≤ tK + 1)
    (hN1 : (tN : ℚ) ≤ P * dN) (hN2 : P * dN ≤ tN + 1) :
    G00 * min (tK : ℚ) tN + G10 * (tN - min (tK : ℚ) tN) + G01 * (tK - min (tK : ℚ) tN) +
        G11 * (m - max (tK : ℚ) tN) ≤
      P * (G00 * min dK dN + G10 * (dN - min dK dN) + G01 * (dK - min dK dN) +
        G11 * (1 / 2 - max dK dN)) + G10 + G01 + G11 := by
  have emn : P * min dK dN = min (P * dK) (P * dN) := mul_min_of_nonneg _ _ hP.le
  have emx : P * max dK dN = max (P * dK) (P * dN) := mul_max_of_nonneg _ _ hP.le
  have A1 : min (tK : ℚ) tN ≤ P * min dK dN := emn ▸ min_le_min hK1 hN1
  have A2 : P * min dK dN ≤ min (tK : ℚ) tN + 1 := by
    rw [emn, ← min_add_add_right]; exact min_le_min hK2 hN2
  have A3 : P * max dK dN ≤ max (tK : ℚ) tN + 1 := by
    rw [emx, ← max_add_add_right]; exact max_le_max hK2 hN2
  have hs1 : min dK dN + max dK dN = dK + dN := min_add_max dK dN
  have hs2 : min (tK : ℚ) tN + max (tK : ℚ) tN = tK + tN := min_add_max _ _
  have B1 : 0 ≤ (P * dN - tN) - (P * min dK dN - min (tK : ℚ) tN) + 1 := by linarith
  have B2 : 0 ≤ (P * dK - tK) - (P * min dK dN - min (tK : ℚ) tN) + 1 := by linarith
  have B3 : 0 ≤ P / 2 - m - (P * max dK dN - max (tK : ℚ) tN) + 1 := by linarith
  nlinarith [mul_nonneg h00 (sub_nonneg.2 A1), mul_nonneg h10 B1, mul_nonneg h01 B2,
    mul_nonneg h11 B3]

/-! ### The fractional parts of `K/p` and `N/p` -/

omit hp in
theorem floor_div_natCast (A q : ℕ) : ⌊(A : ℚ) / q⌋ = ((A / q : ℕ) : ℤ) := by
  rw [Rat.floor_natCast_div_natCast, Int.natCast_div]

theorem fract_div_prime (A : ℕ) :
    (A : ℚ) / p - ⌊(A : ℚ) / p⌋ = ((A % p : ℕ) : ℚ) / p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [floor_div_natCast, Int.cast_natCast]
  have := Nat.div_add_mod A p
  rw [eq_div_iff hp0, sub_mul, div_mul_cancel₀ _ hp0]
  have h' : ((p * (A / p) + A % p : ℕ) : ℚ) = A := by rw [this]
  push_cast at h'
  linarith

theorem sigma_eval (A : ℕ) :
    (2 : ℚ) * ⌊2 * (((A % p : ℕ) : ℚ) / p)⌋ - 1 = ss p A := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hr := Nat.mod_lt A hp.out.pos
  simp only [ss]
  split_ifs with h
  · have : ⌊2 * (((A % p : ℕ) : ℚ) / p)⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; positivity
      · rw [mul_div_assoc', div_lt_iff₀ hp0]; push_cast
        exact_mod_cast (by omega : 2 * (A % p) < 1 * p)
    rw [this]; norm_num
  · have : ⌊2 * (((A % p : ℕ) : ℚ) / p)⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [mul_div_assoc', le_div_iff₀ hp0]; push_cast
        exact_mod_cast (by omega : 1 * p ≤ 2 * (A % p))
      · rw [mul_div_assoc', div_lt_iff₀ hp0]; push_cast
        exact_mod_cast (by omega : 2 * (A % p) < (1 + 1) * p)
    rw [this]; norm_num

theorem tt_le_p_mul_d0 (hp2 : p ≠ 2) (A : ℕ) :
    (tt p A : ℚ) ≤ p * min (((A % p : ℕ) : ℚ) / p) (1 - ((A % p : ℕ) : ℚ) / p) ∧
      p * min (((A % p : ℕ) : ℚ) / p) (1 - ((A % p : ℕ) : ℚ) / p) ≤ tt p A + 1 := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hr := Nat.mod_lt A hp.out.pos
  rw [mul_min_of_nonneg _ _ hp0.le, mul_div_cancel₀ _ hp0.ne', mul_sub, mul_one,
    mul_div_cancel₀ _ hp0.ne']
  simp only [tt]
  split_ifs with h
  · have : ((A % p : ℕ) : ℚ) ≤ p - (A % p : ℕ) := by
      have : 2 * (A % p) ≤ p := by omega
      have : (2 : ℚ) * (A % p : ℕ) ≤ p := by exact_mod_cast this
      linarith
    rw [min_eq_left this]
    constructor <;> linarith
  · have : (p : ℚ) - (A % p : ℕ) ≤ (A % p : ℕ) := by
      have : p ≤ 2 * (A % p) := by omega
      have : (p : ℚ) ≤ 2 * (A % p : ℕ) := by exact_mod_cast this
      linarith
    rw [min_eq_right this, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    constructor <;> linarith

omit hp in
theorem floor_sq_div_four (E : ℤ) : ⌊(E : ℚ) * E * (1 / 4)⌋ = E ^ 2 / 4 := by
  rw [show (E : ℚ) * E * (1 / 4) = ((E ^ 2 : ℤ) : ℚ) / ((4 : ℕ) : ℚ) by push_cast; ring,
    Rat.floor_intCast_div_natCast]
  rfl

/-! ### The inner bound -/

namespace Inner

section Main

variable {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n)
include hM hK hp1 hp2

/-- The rows of a class contribute `L_a (L_a + 2b_a - ℓ_K(a) - 5)`. -/
theorem sum_w2 {a : ℕ} (ha : a ∈ classes p) :
    ∑ i ∈ range (L p n M a).toNat, w2 p n a i =
      L p n M a * (L p n M a + 2 * b p n a - ell p (K n) a - 5) := by
  have hL := L_nonneg hM hK hp1 hp2 ha
  have : ∀ i ∈ range (L p n M a).toNat,
      w2 p n a i = 2 * (i : ℤ) + (2 * b p n a - ell p (K n) a - 4) := by
    intro i _; simp only [w2]; ring
  rw [sum_congr rfl this, sum_range_two_mul_add, Int.toNat_of_nonneg hL]
  ring

/-- The zero class contributes at least `-(4M + 10)(2M + 5)`. -/
theorem zero_class_ge :
    -((4 * M + 10) * (2 * M + 5) : ℤ) ≤ ∑ i ∈ range (L0 M).toNat, w02 p n M i := by
  have hmK := hyp_mK hM hK hp1 hp2
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hcap : -(2 * M + 5 : ℤ) ≤ zeroCap2 p n M := by
    unfold zeroCap2
    split_ifs with hc
    · refine le_inf' hc _ fun c hc' => ?_
      have hT := b_le_T hM hK hp1 hp2 hc'
      have hb : 0 ≤ b p n c := by simp only [b]; positivity
      have hc'' := mem_Icc.1 hc'
      have hell := ell_formula hp2' hc''.1 hc''.2 (K n)
      have hell' : ell p (K n) c ≤ 2 * (K n / p) + 2 := by rw [hell]; split_ifs <;> omega
      have hell'' : (ell p (K n) c : ℤ) ≤ 2 * M := by
        have : ell p (K n) c ≤ 2 * M := by omega
        exact_mod_cast this
      simp only [Z, eps]
      have : (1 : ℤ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
      split_ifs <;> omega
    · omega
  have hw : ∀ i ∈ range (L0 M).toNat, -(2 * M + 5 : ℤ) ≤ w02 p n M i := by
    intro i _
    simp only [w02]
    refine le_min ?_ hcap
    have : ((K n / p : ℕ) : ℤ) ≤ M - 1 := by omega
    have : (0 : ℤ) ≤ (N n / p : ℕ) := by positivity
    have : (0 : ℤ) ≤ (i : ℤ) := by positivity
    omega
  have hL0 : (L0 M).toNat = 4 * M + 10 := by simp only [L0]; omega
  have := sum_le_sum hw
  rw [sum_const, card_range, hL0, nsmul_eq_mul] at this
  rw [hL0]
  push_cast at this
  linarith

/-- The Lagrangian bound: for every integer `μ`,
`∑_a ∑_i w_{a,i} ≥ μ(h - L₀) - ∑_a ⌊(2b_a - ℓ_K(a) - 5 - μ)²/4⌋`. -/
theorem gammaClasses_ge (μ : ℤ) :
    μ * (dim n - L0 M) - ∑ a ∈ classes p, (2 * b p n a - ell p (K n) a - 5 - μ) ^ 2 / 4 ≤
      ∑ a ∈ classes p, ∑ i ∈ range (L p n M a).toNat, w2 p n a i := by
  rw [sum_congr rfl fun a ha => sum_w2 hM hK hp1 hp2 ha]
  have hsum := sum_L hM hK hp1 hp2
  have h1 : ∀ a ∈ classes p, μ * L p n M a - (2 * b p n a - ell p (K n) a - 5 - μ) ^ 2 / 4 ≤
      L p n M a * (L p n M a + 2 * b p n a - ell p (K n) a - 5) := by
    intro a _
    have := mul_add_add_sq_div_four_nonneg (L p n M a) (2 * b p n a - ell p (K n) a - 5 - μ)
    nlinarith
  have h2 := sum_le_sum h1
  rw [sum_sub_distrib, ← mul_sum] at h2
  have : ∑ a ∈ classes p, L p n M a = dim n - L0 M := by linarith
  rw [this] at h2
  exact h2

/-- The squares in the Lagrangian bound, as a function of the two thresholds. -/
theorem sum_sq_eq (μ : ℤ) :
    ∑ a ∈ classes p, (2 * b p n a - ell p (K n) a - 5 - μ) ^ 2 / 4 =
      ∑ a ∈ Icc 1 ((p - 1) / 2), (fun u v : ℤ =>
        (12 * (N n / p : ℕ) - 2 * (K n / p : ℕ) - μ + 6 * ss p (N n) * v - ss p (K n) * u) ^ 2 / 4)
        (if tt p (K n) < a then 1 else 0) (if tt p (N n) < a then 1 else 0) := by
  have hp2' := hyp_p2 hM hK hp1 hp2
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_Icc.1 ha
  simp only [b]
  rw [ell_eq_tt hp2' ha'.1 ha'.2 (K n), ell_eq_tt hp2' ha'.1 ha'.2 (N n)]
  congr 2
  ring

omit hp hM hK hp1 hp2 in
theorem inner_const_le {M : ℚ} (hM : 40 ≤ M) :
    (4 * M + 10) * (2 * M + 5) + 3 * M * (4 * M + 10) + 3 * (12 * M + 7) ^ 2 ≤
      1000 * (M + 1) ^ 2 := by
  nlinarith

omit hp hM hK hp1 hp2 in
theorem ss_cases (A : ℕ) : ss p A = -1 ∨ ss p A = 1 := by
  unfold ss; split_ifs <;> simp

/-- (5.7) in the inner range: `-L_p(K, M) ≤ p R(K/p) + 1000 (M + 1)²`. -/
theorem neg_Lexp_le :
    -(Lexp p n M : ℚ) ≤ p * Rx ((K n : ℚ) / p) + 1000 * ((M : ℚ) + 1) ^ 2 := by
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hsq : 2 * dim n < p ^ 2 := by
    have := hyp_sq hM hK hp1 hp2; simp only [K, dim] at this ⊢; omega
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hmK := hyp_mK hM hK hp1 hp2
  have hx3 : 3 ≤ (K n : ℚ) / p := by
    rw [le_div_iff₀ hp0]; exact_mod_cast (by omega : 3 * p ≤ K n)
  have hxM : (K n : ℚ) / p < M := by
    rw [div_lt_iff₀ hp0]; exact_mod_cast (by rw [mul_comm]; exact hp1 : K n < M * p)
  have hLexp : Lexp p n M = padicValRat p (S n) + gammaIn p n M := by
    simp only [Lexp, if_neg (not_le.2 hp1), if_pos hp2]
  have hS := p_mul_N_le (n := n) hp2' hsq
  -- the multiplier `μ`
  set x : ℚ := (K n : ℚ) / p with hx
  set δ : ℤ := if 2 * x - ⌊2 * x⌋ < 23 / 10 * x - ⌊23 / 10 * x⌋ then 1 else 0 with hδ
  set μZ : ℤ := 2 * ⌊23 / 10 * x⌋ - ⌊2 * x⌋ - 5 + δ with hμZ
  have hμ : RFun.eMu.eval x = μZ := by
    rw [RFun.eMu_eval, hμZ, hδ]; push_cast; split_ifs <;> simp
  have hδ01 : (0 : ℚ) ≤ δ ∧ (δ : ℚ) ≤ 1 := by rw [hδ]; split_ifs <;> norm_num
  have hμ0 : 0 ≤ μZ := by
    have h1 := Int.lt_floor_add_one (23 / 10 * x)
    have h2 := Int.floor_le (2 * x)
    have : (-1 : ℚ) < μZ := by rw [hμZ]; push_cast; linarith
    have : (-1 : ℤ) < μZ := by exact_mod_cast this
    omega
  have hμM : μZ ≤ 3 * M := by
    have h1 := Int.floor_le (23 / 10 * x)
    have h2 := Int.lt_floor_add_one (2 * x)
    have : (μZ : ℚ) < 3 * M := by rw [hμZ]; push_cast; linarith
    have : μZ < 3 * M := by exact_mod_cast this
    omega
  -- the evaluations at `x = K/p`
  have hαx : 3 / 40 * x = ((N n : ℕ) : ℚ) / p := by
    rw [hx]; simp only [K, N]; push_cast; ring
  set D : ℤ := 12 * (N n / p : ℕ) - 2 * (K n / p : ℕ) - μZ with hDdef
  have hD : RFun.eD.eval x = D := by
    rw [RFun.eD_eval, hαx, floor_div_natCast, hx, floor_div_natCast, ← hx, hμ, hDdef]
    push_cast; ring
  have hSK : RFun.eSK.eval x = ss p (K n) := by
    rw [RFun.eSK_eval, hx, fract_div_prime, sigma_eval]
  have hSN : RFun.eSN.eval x = ss p (N n) := by
    rw [RFun.eSN_eval, hαx, fract_div_prime, sigma_eval]
  have hdK : (RFun.d0 RFun.x).eval x =
      min (((K n % p : ℕ) : ℚ) / p) (1 - ((K n % p : ℕ) : ℚ) / p) := by
    simp only [RFun.d0_eval, RFun.x, Ex.eval_var]
    rw [hx, fract_div_prime]
  have hdN : (RFun.d0 (RFun.c (3 / 40) * RFun.x)).eval x =
      min (((N n % p : ℕ) : ℚ) / p) (1 - ((N n % p : ℕ) : ℚ) / p) := by
    simp only [RFun.d0_eval, RFun.c, RFun.x, Ex.eval_mul, Ex.eval_cst, Ex.eval_var]
    rw [hαx, fract_div_prime]
  have h00 : (RFun.sq4 RFun.eD).eval x = ((D ^ 2 / 4 : ℤ) : ℚ) := by
    rw [RFun.sq4_eval, hD, floor_sq_div_four]
  have h10 : (RFun.sq4 (RFun.eD - RFun.eSK)).eval x = (((D - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ) := by
    rw [RFun.sq4_eval, Ex.eval_sub, hD, hSK, ← Int.cast_sub, floor_sq_div_four]
  have h01 : (RFun.sq4 (RFun.eD + RFun.c 6 * RFun.eSN)).eval x =
      (((D + 6 * ss p (N n)) ^ 2 / 4 : ℤ) : ℚ) := by
    rw [RFun.sq4_eval, Ex.eval_add, Ex.eval_mul, hD, hSN, RFun.c, Ex.eval_cst,
      show (D : ℚ) + 6 * (ss p (N n) : ℚ) = ((D + 6 * ss p (N n) : ℤ) : ℚ) by push_cast; ring,
      floor_sq_div_four]
  have h11 : (RFun.sq4 (RFun.eD + RFun.c 6 * RFun.eSN - RFun.eSK)).eval x =
      (((D + 6 * ss p (N n) - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ) := by
    rw [RFun.sq4_eval, Ex.eval_sub, Ex.eval_add, Ex.eval_mul, hD, hSN, hSK, RFun.c, Ex.eval_cst,
      show (D : ℚ) + 6 * (ss p (N n) : ℚ) - ss p (K n) =
        ((D + 6 * ss p (N n) - ss p (K n) : ℤ) : ℚ) by push_cast; ring,
      floor_sq_div_four]
  -- the class sum
  have hγc := gammaClasses_ge hM hK hp1 hp2 μZ
  have hsum := (sum_sq_eq hM hK hp1 hp2 μZ).trans (sum_two_thresholds (tt_le hp2' (K n))
    (tt_le hp2' (N n)) (fun u v : ℤ => (12 * ((N n / p : ℕ) : ℤ) - 2 * ((K n / p : ℕ) : ℤ) - μZ +
      6 * ss p (N n) * v - ss p (K n) * u) ^ 2 / 4))
  rw [hsum] at hγc
  simp only [mul_zero, add_zero, sub_zero, mul_one] at hγc
  rw [← hDdef] at hγc
  have hγ0 := zero_class_ge hM hK hp1 hp2
  have hγ : gammaIn p n M = (∑ a ∈ classes p, ∑ i ∈ range (L p n M a).toNat, w2 p n a i) +
      ∑ i ∈ range (L0 M).toNat, w02 p n M i := rfl
  -- the thresholds against the fractional parts
  have htK := tt_le_p_mul_d0 hp2' (K n)
  have htN := tt_le_p_mul_d0 hp2' (N n)
  have hm : 2 * (((p - 1) / 2 : ℕ) : ℚ) + 1 = p := by
    have := hyp_two_m hM hK hp1 hp2
    have h5 := hyp_p5 hM hK hp1 hp2
    have : 2 * ((p - 1) / 2) + 1 = p := by omega
    exact_mod_cast this
  have hG : ∀ e : ℤ, 0 ≤ e ^ 2 / 4 := fun e => Int.ediv_nonneg (sq_nonneg e) (by norm_num)
  have hth := thresholds_le_integral (G00 := ((D ^ 2 / 4 : ℤ) : ℚ))
    (G10 := (((D - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ)) (G01 := (((D + 6 * ss p (N n)) ^ 2 / 4 : ℤ) : ℚ))
    (G11 := (((D + 6 * ss p (N n) - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ)) (by exact_mod_cast hG _)
    (by exact_mod_cast hG _) (by exact_mod_cast hG _) (by exact_mod_cast hG _) hp0 hm
    htK.1 htK.2 htN.1 htN.2
  -- bounds on the constants
  have hkN : N n / p ≤ K n / p := Nat.div_le_div_right (by simp only [N, K]; omega)
  have hDlo : -(5 * M : ℤ) ≤ D := by
    rw [hDdef]
    have : ((K n / p : ℕ) : ℤ) ≤ M - 1 := by omega
    have : (0 : ℤ) ≤ (N n / p : ℕ) := by positivity
    omega
  have hDhi : D ≤ 12 * M := by
    rw [hDdef]
    have : ((N n / p : ℕ) : ℤ) ≤ (K n / p : ℕ) := by exact_mod_cast hkN
    have : ((K n / p : ℕ) : ℤ) ≤ M - 1 := by omega
    omega
  have hbound : ∀ e : ℤ, -(5 * M + 7 : ℤ) ≤ e → e ≤ 12 * M + 7 →
      e ^ 2 / 4 ≤ (12 * M + 7) ^ 2 := by
    intro e h1 h2
    exact (Int.ediv_le_self _ (sq_nonneg e)).trans (sq_le_sq' (by omega) h2)
  have hsK := ss_cases (p := p) (K n)
  have hsN := ss_cases (p := p) (N n)
  have b10 : (D - ss p (K n)) ^ 2 / 4 ≤ (12 * M + 7) ^ 2 := hbound _ (by omega) (by omega)
  have b01 : (D + 6 * ss p (N n)) ^ 2 / 4 ≤ (12 * M + 7) ^ 2 := hbound _ (by omega) (by omega)
  have b11 : (D + 6 * ss p (N n) - ss p (K n)) ^ 2 / 4 ≤ (12 * M + 7) ^ 2 :=
    hbound _ (by omega) (by omega)
  have hμL : μZ * L0 M ≤ 3 * M * (4 * M + 10) := by
    simp only [L0]; exact mul_le_mul_of_nonneg_right hμM (by positivity)
  -- assemble
  generalize (p - 1) / 2 = m at hγc hth
  rw [hLexp, Rx, RFun.eR_eval_of_three_le _ hx3, RFun.eGam_eval, RFun.eI_eval, hμ, hdK, hdN,
    h00, h10, h01, h11]
  have hμh : (p : ℚ) * ((μZ : ℚ) * (37 / 40) * x) = μZ * dim n := by
    rw [hx]; simp only [K, dim]; push_cast; field_simp
  have hγc' : ((μZ * (dim n - L0 M) - ((D ^ 2 / 4) * min (tt p (K n) : ℤ) (tt p (N n)) +
      ((D - ss p (K n)) ^ 2 / 4) * ((tt p (N n) : ℤ) - min (tt p (K n) : ℤ) (tt p (N n))) +
      ((D + 6 * ss p (N n)) ^ 2 / 4) * ((tt p (K n) : ℤ) - min (tt p (K n) : ℤ) (tt p (N n))) +
      ((D + 6 * ss p (N n) - ss p (K n)) ^ 2 / 4) * ((m : ℤ) -
        max (tt p (K n) : ℤ) (tt p (N n)))) : ℤ) : ℚ) ≤
      ((∑ a ∈ classes p, ∑ i ∈ range (L p n M a).toNat, w2 p n a i : ℤ) : ℚ) := by
    exact_mod_cast hγc
  have hγ0' : (-((4 * M + 10) * (2 * M + 5) : ℤ) : ℚ) ≤
      ((∑ i ∈ range (L0 M).toNat, w02 p n M i : ℤ) : ℚ) := by exact_mod_cast hγ0
  have hγ' : ((gammaIn p n M : ℤ) : ℚ) =
      ((∑ a ∈ classes p, ∑ i ∈ range (L p n M a).toNat, w2 p n a i : ℤ) : ℚ) +
      ((∑ i ∈ range (L0 M).toNat, w02 p n M i : ℤ) : ℚ) := by rw [hγ]; push_cast; ring
  have b10' : (((D - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ) ≤ (12 * M + 7) ^ 2 := by exact_mod_cast b10
  have b01' : (((D + 6 * ss p (N n)) ^ 2 / 4 : ℤ) : ℚ) ≤ (12 * M + 7) ^ 2 := by exact_mod_cast b01
  have b11' : (((D + 6 * ss p (N n) - ss p (K n)) ^ 2 / 4 : ℤ) : ℚ) ≤ (12 * M + 7) ^ 2 := by
    exact_mod_cast b11
  have hμL' : (μZ : ℚ) * (L0 M : ℤ) ≤ 3 * M * (4 * M + 10) := by exact_mod_cast hμL
  have hL0 : ((L0 M : ℤ) : ℚ) = 4 * M + 10 := by simp [L0]
  push_cast at hγc' hγ0' hγ' hth hμL' ⊢
  rw [hL0] at hγc' hμL'
  have hC := inner_const_le (M := (M : ℚ)) (by exact_mod_cast hM)
  linarith only [hS, hγc', hγ0', hγ', hth, hμh, b10', b01', b11', hμL', hC]

end Main

end Inner

end Zeta5
