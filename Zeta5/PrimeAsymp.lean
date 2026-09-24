/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import PrimeNumberTheoremAnd.Consequences
import Zeta5.Defs

/-!
# Prime sums over ranges of `K/p`

From the prime number theorem `θ(x) ~ x` (`chebyshev_asymptotic`, PrimeNumberTheoremAnd) we derive
`∑_{p ≤ x} p log p ~ x²/2` by discrete partial summation, and from both the limits of the prime
sums of §5 over a range `l ≤ K/p < r`:

`K⁻² ∑_{l ≤ K/p < r} (A K + B p) log p → A (1/l - 1/r) + (B/2)(1/l² - 1/r²)`,

which is `∫_l^r (Ax + B) x⁻³ dx`.
-/

open Filter Asymptotics Finset Real Chebyshev
open scoped Topology

namespace Zeta5

/-- `∑_{p ≤ x} p log p`. -/
noncomputable def splog (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (p : ℝ) * log p

/-- The prime number theorem in the form `θ(x)/x → 1`. -/
theorem theta_div_tendsto : Tendsto (fun x => θ x / x) atTop (𝓝 1) := by
  have h := (isEquivalent_iff_tendsto_one (u := θ) (v := id) ?_).1 chebyshev_asymptotic
  · exact h
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact hx.ne'

/-- `θ(cx)/x → c`. -/
theorem theta_mul_div {c : ℝ} (hc : 0 < c) : Tendsto (fun x => θ (c * x) / x) atTop (𝓝 c) := by
  have h1 := (theta_div_tendsto.comp (tendsto_id.const_mul_atTop hc)).const_mul c
  have : ∀ᶠ x in atTop, c * (θ (c * x) / (c * x)) = θ (c * x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  simpa using h1.congr' this

theorem theta_nat (N : ℕ) : θ N = ∑ p ∈ Ioc 0 N, if p.Prime then log p else 0 := by
  rw [Chebyshev.theta, Nat.floor_natCast, sum_filter]

theorem splog_nat (N : ℕ) : splog N = ∑ p ∈ Ioc 0 N, if p.Prime then (p : ℝ) * log p else 0 := by
  rw [splog, Nat.floor_natCast, sum_filter]

/-- Discrete partial summation: `∑_{p ≤ N} p log p = N θ(N) - ∑_{n < N} θ(n)`. -/
theorem splog_abel (N : ℕ) : splog N = N * θ N - ∑ n ∈ range N, θ n := by
  induction N with
  | zero => rw [splog_nat, theta_nat]; simp
  | succ N ih =>
    rw [splog_nat, sum_Ioc_succ_top (Nat.zero_le _), ← splog_nat, ih, theta_nat (N + 1),
      sum_Ioc_succ_top (Nat.zero_le _), ← theta_nat, Finset.sum_range_succ]
    push_cast
    split_ifs <;> ring

theorem sum_range_natCast (N : ℕ) : ∑ i ∈ range N, (i : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem splog_nat_div : Tendsto (fun N : ℕ => splog N / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have hθ : Tendsto (fun N : ℕ => θ N / N) atTop (𝓝 1) :=
    theta_div_tendsto.comp tendsto_natCast_atTop_atTop
  have ho : (fun N : ℕ => θ N - N) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
    chebyshev_asymptotic.isLittleO.comp_tendsto tendsto_natCast_atTop_atTop
  have hs := ho.sum_range (fun N => Nat.cast_nonneg N) (by
    simp only [sum_range_natCast]
    refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 3] with N hN
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith)
  have hO : (fun N : ℕ => ∑ i ∈ range N, (i : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 2) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun N => ?_)
    rw [sum_range_natCast, Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ N := by exact_mod_cast h
      rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
      nlinarith
  have hE := (hs.trans_isBigO hO).tendsto_div_nhds_zero
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (2 * N)) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun N => ?_
    field_simp
  have key := (hθ.sub hE).sub ((tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hinv)
  norm_num at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hN)
  rw [splog_abel]
  have : ∑ n ∈ range N, θ n = ∑ i ∈ range N, (θ i - i) + ∑ i ∈ range N, (i : ℝ) := by
    rw [← sum_add_distrib]; simp
  rw [this, sum_range_natCast]
  field_simp
  ring

theorem splog_div : Tendsto (fun x : ℝ => splog x / x ^ 2) atTop (𝓝 (1 / 2)) := by
  have h1 := splog_nat_div.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 := (tendsto_nat_floor_div_atTop (R := ℝ)).pow 2
  have := h1.mul h2
  simp only [one_pow, mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hf : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.floor_eq_zero, not_lt]; exact hx)
  have hs : splog x = splog ⌊x⌋₊ := by rw [splog, splog, Nat.floor_natCast]
  simp only [Function.comp_apply, hs]
  field_simp

/-- `∑_{p ≤ cx} p log p / x² → c²/2`. -/
theorem splog_mul_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => splog (c * x) / x ^ 2) atTop (𝓝 (c ^ 2 / 2)) := by
  have h1 := (splog_div.comp (tendsto_id.const_mul_atTop hc)).const_mul (c ^ 2)
  have : ∀ᶠ x in atTop, c ^ 2 * (splog (c * x) / (c * x) ^ 2) = splog (c * x) / x ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  convert h1.congr' this using 2
  ring

/-- The primes `p ≤ 2h`, over which `m_{K,M}` is a product. -/
def Ps (n : ℕ) : Finset ℕ := (range (2 * dim n + 1)).filter Nat.Prime

/-- `∑_{p ≤ 2h, a ≤ K/p < b} g(p)`. -/
noncomputable def psum (n : ℕ) (a b : ℚ) (g : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Ps n, if a ≤ (K n : ℚ) / p ∧ (K n : ℚ) / p < b then g p else 0

theorem psum_add {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) (n : ℕ) (g : ℕ → ℝ) :
    psum n a c g = psum n a b g + psum n b c g := by
  rw [psum, psum, psum, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  set y := (K n : ℚ) / p
  by_cases h : y < b
  · have e1 : (a ≤ y ∧ y < c) ↔ (a ≤ y ∧ y < b) :=
      ⟨fun h' => ⟨h'.1, h⟩, fun h' => ⟨h'.1, h.trans_le hbc⟩⟩
    have e2 : ¬(b ≤ y ∧ y < c) := fun h' => absurd h'.1 (not_le.2 h)
    simp only [e1, e2, if_false, add_zero]
  · have hb := le_of_not_gt h
    have e1 : (a ≤ y ∧ y < c) ↔ (b ≤ y ∧ y < c) :=
      ⟨fun h' => ⟨hb, h'.2⟩, fun h' => ⟨hab.trans hb, h'.2⟩⟩
    have e2 : ¬(a ≤ y ∧ y < b) := fun h' => h h'.2
    simp only [e1, e2, if_false, zero_add]

theorem psum_self (n : ℕ) (a : ℚ) (g : ℕ → ℝ) : psum n a a g = 0 := by
  refine sum_eq_zero fun p _ => if_neg fun h => ?_
  exact absurd (h.1.trans_lt h.2) (lt_irrefl a)

theorem K_real (n : ℕ) : (K n : ℝ) = 40 * n := by simp [K]

theorem tendsto_K : Tendsto (fun n => (K n : ℝ)) atTop atTop := by
  simp only [K_real]
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)

theorem mem_Ps {n p : ℕ} : p ∈ Ps n ↔ p < 2 * dim n + 1 ∧ p.Prime := by
  simp [Ps]

/-- For `0 ≤ y ≤ 2h`, a sum over the primes `p ≤ y` is a sum over `Ps n` restricted to `p ≤ y`. -/
theorem sum_primes_le_eq {n : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 2 * dim n) (g : ℕ → ℝ) :
    ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, g p = ∑ p ∈ Ps n, if (p : ℝ) ≤ y then g p else 0 := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, mem_Ps]
  constructor
  · rintro ⟨⟨_, hp⟩, hpr⟩
    have h1 : (p : ℝ) ≤ y := (Nat.le_floor_iff hy0).1 hp
    have h2 : (p : ℝ) < 2 * dim n + 1 := by linarith
    exact ⟨⟨by exact_mod_cast h2, hpr⟩, h1⟩
  · rintro ⟨⟨_, hpr⟩, hp⟩
    exact ⟨⟨hpr.pos, (Nat.le_floor_iff hy0).2 hp⟩, hpr⟩

/-- For `p > 0`, `l > 0`: `l ≤ K/p ↔ p ≤ K/l`. -/
theorem le_div_iff_real {k p : ℕ} (hp : 0 < p) {l : ℚ} (hl : 0 < l) :
    l ≤ (k : ℚ) / p ↔ (p : ℝ) ≤ (k : ℝ) / l := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hp', le_div_iff₀ hl', ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [mul_comm]

theorem div_lt_iff_real {k p : ℕ} (hp : 0 < p) {r : ℚ} (hr : 0 < r) :
    (k : ℚ) / p < r ↔ ¬ (p : ℝ) ≤ (k : ℝ) / r := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [not_le, div_lt_iff₀ hp', div_lt_iff₀ hr', ← Rat.cast_lt (K := ℝ)]
  push_cast
  rw [mul_comm]

/-- `∑_{l ≤ K/p < r} g(p) = ∑_{p ≤ K/l} g(p) - ∑_{p ≤ K/r} g(p)`. -/
theorem psum_eq_sub {n : ℕ} {l r : ℚ} (hl : 0 < l) (hlr : l < r) (g : ℕ → ℝ) :
    psum n l r g = (∑ p ∈ Ps n, if (p : ℝ) ≤ (K n : ℝ) / l then g p else 0) -
      ∑ p ∈ Ps n, if (p : ℝ) ≤ (K n : ℝ) / r then g p else 0 := by
  rw [psum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hp0 := (mem_Ps.1 hp).2.pos
  have hr : 0 < r := hl.trans hlr
  simp only [le_div_iff_real hp0 hl, div_lt_iff_real hp0 hr]
  have hK : (K n : ℝ) / r ≤ (K n : ℝ) / l := by
    have : (l : ℝ) ≤ r := by exact_mod_cast hlr.le
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hl) this
  by_cases h1 : (p : ℝ) ≤ (K n : ℝ) / r
  · rw [if_neg (fun h => h.2 h1), if_pos (h1.trans hK), if_pos h1, sub_self]
  · rw [if_neg h1, sub_zero]
    by_cases h2 : (p : ℝ) ≤ (K n : ℝ) / l
    · rw [if_pos ⟨h2, h1⟩, if_pos h2]
    · rw [if_neg (fun h => h2 h.1), if_neg h2]

theorem K_div_le {n : ℕ} {l : ℚ} (hl : 20 / 37 ≤ l) : (K n : ℝ) / l ≤ 2 * dim n := by
  have hl' : (20 / 37 : ℝ) ≤ l := by
    have := (Rat.cast_le (K := ℝ)).2 hl
    norm_num at this
    exact this
  have hl0 : (0 : ℝ) < l := by linarith
  rw [div_le_iff₀ hl0, K_real]
  simp only [dim]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `K⁻² ∑_{l ≤ K/p < r} (A K + B p) log p → ∫_l^r (Ax + B) x⁻³ dx`. -/
theorem tendsto_psum_affine {l r : ℚ} (hl : 20 / 37 ≤ l) (hlr : l < r) (A B : ℝ) :
    Tendsto (fun n => psum n l r (fun p => (A * K n + B * p) * log p) / (K n : ℝ) ^ 2) atTop
      (𝓝 (A * (1 / l - 1 / r) + B / 2 * (1 / l ^ 2 - 1 / r ^ 2))) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hr0 : 0 < r := hl0.trans hlr
  have hl0' : (0 : ℝ) < l := by exact_mod_cast hl0
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hsum : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → y ≤ 2 * dim n →
      (∑ p ∈ Ps n, if (p : ℝ) ≤ y then (A * K n + B * p) * log p else 0) =
        A * K n * θ y + B * splog y := by
    intro n y hy0 hy
    rw [Chebyshev.theta, splog, sum_primes_le_eq hy0 hy, sum_primes_le_eq hy0 hy, mul_sum,
      mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  have hform : ∀ n : ℕ, psum n l r (fun p => (A * K n + B * p) * log p) / (K n : ℝ) ^ 2 =
      A * (θ ((1 / l) * K n) / K n - θ ((1 / r) * K n) / K n) +
        B * (splog ((1 / l) * K n) / (K n : ℝ) ^ 2 - splog ((1 / r) * K n) / (K n : ℝ) ^ 2) := by
    intro n
    have e1 : (1 / (l : ℝ)) * K n = K n / l := by ring
    have e2 : (1 / (r : ℝ)) * K n = K n / r := by ring
    rw [psum_eq_sub hl0 hlr, hsum n _ (by positivity) (K_div_le hl),
      hsum n _ (by positivity) (K_div_le (hl.trans hlr.le)), e1, e2]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [K]
    · have : (K n : ℝ) ≠ 0 := by rw [K_real]; positivity
      field_simp
      ring
  have t1 := (theta_mul_div (c := 1 / (l : ℝ)) (by positivity)).comp tendsto_K
  have t2 := (theta_mul_div (c := 1 / (r : ℝ)) (by positivity)).comp tendsto_K
  have t3 := (splog_mul_div (c := 1 / (l : ℝ)) (by positivity)).comp tendsto_K
  have t4 := (splog_mul_div (c := 1 / (r : ℝ)) (by positivity)).comp tendsto_K
  have key := ((t1.sub t2).const_mul A).add ((t3.sub t4).const_mul B)
  have e : A * (1 / (l : ℝ) - 1 / r) + B / 2 * (1 / (l : ℝ) ^ 2 - 1 / (r : ℝ) ^ 2) =
      A * (1 / l - 1 / r) + B * ((1 / (l : ℝ)) ^ 2 / 2 - (1 / (r : ℝ)) ^ 2 / 2) := by ring
  rw [e]
  exact key.congr fun n => (hform n).symm

theorem natCast_eq_of_div_eq {k p : ℕ} {l : ℚ} (hl : 0 < l) (h : (k : ℚ) / p = l) :
    (p : ℚ) = (k : ℚ) / l := by
  have hk : (k : ℚ) ≠ 0 := by
    intro h'; rw [h', zero_div] at h; exact hl.ne' h.symm
  have hp : (p : ℚ) ≠ 0 := by
    intro h'; rw [h', div_zero] at h; exact hl.ne' h.symm
  rw [← h]; field_simp

/-- A single value of `K/p` contributes `o(K²)`. -/
theorem tendsto_point {l : ℚ} (hl : 0 < l) (c : ℝ) :
    Tendsto (fun n => (∑ p ∈ Ps n, if (K n : ℚ) / p = l then c * p * log p else 0) /
      (K n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  set t : ℕ → ℝ := fun n => c * ((K n : ℝ) / l) * log ((K n : ℝ) / l)
  have hsum : ∀ n, (∑ p ∈ Ps n, if (K n : ℚ) / p = l then c * p * log p else 0) =
      #((Ps n).filter fun p : ℕ => (K n : ℚ) / p = l) * t n := by
    intro n
    rw [← sum_filter, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨hp, hpl⟩ := mem_filter.1 hp
    have : (p : ℝ) = (K n : ℝ) / l := by
      have h1 : (p : ℚ) = (K n : ℚ) / l := natCast_eq_of_div_eq hl hpl
      have := congrArg (fun q : ℚ => (q : ℝ)) h1
      push_cast at this
      exact this
    simp only [t, this]
  have hcard : ∀ n, #((Ps n).filter fun p : ℕ => (K n : ℚ) / p = l) ≤ 1 := by
    intro n
    refine card_le_one.2 fun p hp q hq => ?_
    obtain ⟨hp, hpl⟩ := mem_filter.1 hp
    obtain ⟨hq, hql⟩ := mem_filter.1 hq
    exact_mod_cast (natCast_eq_of_div_eq hl hpl).trans (natCast_eq_of_div_eq hl hql).symm
  -- `t n / K² = (c / l²) log(K/l) / (K/l) → 0`
  have hlog : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have ht : Tendsto (fun n => t n / (K n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h1 := (hlog.comp ((tendsto_K).atTop_div_const hl')).const_mul (c / (l : ℝ) ^ 2)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (K n : ℝ) ≠ 0 := by rw [K_real]; positivity
    simp only [t, Function.comp_apply]
    field_simp
  refine squeeze_zero_norm' ?_ (by simpa using ht.norm)
  filter_upwards with n
  rw [hsum, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K n : ℝ) ^ 2)]
  have h1 : |(#((Ps n).filter fun p : ℕ => (K n : ℚ) / p = l) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hcard n
  gcongr
  calc |(#((Ps n).filter fun p : ℕ => (K n : ℚ) / p = l) : ℝ)| * |t n| ≤ 1 * |t n| := by gcongr
    _ = |t n| := one_mul _

/-- `K⁻¹ θ(cK) → c`. -/
theorem tendsto_theta_K {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => θ (c * K n) / (K n : ℝ)) atTop (𝓝 c) :=
  (theta_mul_div hc).comp tendsto_K

end Zeta5
