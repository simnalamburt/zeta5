/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.InnerBound
import Zeta5.OuterBound
import Zeta5.RCheck

/-!
# The growth of the normalisation (5.21)

`limsup_{K → ∞, 40 ∣ K} K⁻² log m_{K,200} ≤ A_200` (§5 and Appendix B), in the form: for every
`ε > 0`, eventually `log m_{K,200} ≤ (A_200 + ε) K²`.

`log m_{K,M} = ∑_{p ≤ 2h} (-L_p) log p`, and

* for `p ≤ K/M` (5.3), `-L_p = 6h⌊log_p 5K⌋ + h v_p(24)`, and
  `∑_{p ≤ K/M} ⌊log_p 5K⌋ log p ≤ θ(K/M) + ψ(5K) - θ(5K) = K/M + o(K)` by the prime number theorem
  for `θ` and `ψ`;
* for `K/M < p ≤ 2h`, `-L_p ≤ p R(K/p) + O(1)` (`Zeta5.Inner.neg_Lexp_le`,
  `Zeta5.Outer.neg_Lexp_le`), and `K⁻² ∑ p R(K/p) log p` tends to `∫_{20/37}^M R(x) x⁻³ dx`,
  which the kernel bounds by `A_200 - 6λ/200` (`Zeta5.rBounds_sum`).

The paper states (5.21) for every `M ∈ 40ℤ`, bounding `∫_{20}^M R x⁻³` by the tail estimates
(5.15)–(5.17). We only need `M = 200` (Theorem 2.1), where we integrate exactly instead.
-/

open Filter Finset Real Chebyshev
open scoped Topology

namespace Zeta5

/-- `log m_{K,M} = ∑_{p ≤ 2h} (-L_p) log p`. -/
theorem log_normFactor (n M : ℕ) :
    Real.log (normFactor n M) = ∑ p ∈ Ps n, (-(Lexp p n M : ℝ)) * Real.log p := by
  unfold normFactor
  rw [Rat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun p _ => ?_
    rw [Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow]
    push_cast; ring
  · intro p hp
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_filter.1 hp).2.ne_zero
    rw [Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ this

/-! ### The prime number theorem for `ψ` -/

theorem psi_mul_div {c : ℝ} (hc : 0 < c) : Tendsto (fun x => ψ (c * x) / x) atTop (𝓝 c) := by
  have h0 : Tendsto (fun x => ψ x / x) atTop (𝓝 1) := by
    have h := (Asymptotics.isEquivalent_iff_tendsto_one (u := ψ) (v := fun x => x) ?_).1 WeakPNT''
    · exact h
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact hx.ne'
  have h1 := (h0.comp (tendsto_id.const_mul_atTop hc)).const_mul c
  have : ∀ᶠ x in atTop, c * (ψ (c * x) / (c * x)) = ψ (c * x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  simpa using h1.congr' this

theorem tendsto_psi_K {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => ψ (c * K n) / (K n : ℝ)) atTop (𝓝 c) :=
  (psi_mul_div hc).comp tendsto_K

/-! ### The small primes (5.3) -/

theorem neg_Lexp_small {n M p : ℕ} (hp : p * M ≤ K n) :
    -(Lexp p n M : ℝ) = 6 * dim n * Nat.log p (5 * K n) + dim n * padicValNat p 24 := by
  simp only [Lexp, if_pos hp, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
    Int.cast_ofNat]
  ring

/-- `∑_{p ≤ y} ⌊log_p N⌋ log p ≤ θ(y) + ψ(N) - θ(N)` for `y ≤ N`. -/
theorem sum_natLog_mul_log_le {y N : ℕ} (hyN : y ≤ N) :
    ∑ p ∈ Nat.primesLE y, (Nat.log p N : ℝ) * Real.log p ≤ θ y + ψ N - θ N := by
  have hsub : Nat.primesLE y ⊆ Nat.primesLE N := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hyN, hp.2⟩
  rw [psi_eq_sum_mul_log_prime, theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log,
    ← sum_sdiff hsub, ← sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))]
  have : ∑ p ∈ Nat.primesLE N \ Nat.primesLE y, Real.log p ≤
      ∑ p ∈ Nat.primesLE N \ Nat.primesLE y, (Nat.log p N : ℝ) * Real.log p := by
    refine sum_le_sum fun p hp => ?_
    have hp' := Nat.mem_primesLE.1 (mem_sdiff.1 hp).1
    have h1 : 1 ≤ Nat.log p N := Nat.le_log_of_pow_le hp'.2.one_lt (by simpa using hp'.1)
    have h2 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le)
    have : (1 : ℝ) ≤ Nat.log p N := by exact_mod_cast h1
    nlinarith
  linarith

/-- `v_p(24) log p ≤ log 24`, and it vanishes for `p > 24`. -/
theorem padicValNat_24_log_le {p : ℕ} (hp : p.Prime) :
    (padicValNat p 24 : ℝ) * Real.log p ≤ if p ≤ 24 then Real.log 24 else 0 := by
  haveI := Fact.mk hp
  split_ifs with h
  · have hdvd : p ^ padicValNat p 24 ∣ 24 := pow_padicValNat_dvd
    have hle : p ^ padicValNat p 24 ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    rw [← Real.log_pow]
    exact Real.log_le_log (by have := hp.pos; positivity) (by exact_mod_cast hle)
  · have : ¬p ∣ 24 := fun hd => h (Nat.le_of_dvd (by norm_num) hd)
    simp [padicValNat.eq_zero_of_not_dvd this]

theorem small_primes_le (n : ℕ) :
    ∑ p ∈ Ps n, (if p * 200 ≤ K n then -(Lexp p n 200 : ℝ) * Real.log p else 0) ≤
      6 * dim n * (θ ((K n : ℝ) / 200) + ψ (5 * K n) - θ (5 * K n)) +
        dim n * (25 * Real.log 24) := by
  have hset : (Ps n).filter (fun p => p * 200 ≤ K n) = Nat.primesLE (K n / 200) := by
    ext p
    simp only [mem_filter, mem_Ps, Nat.mem_primesLE]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 200)]
    constructor
    · rintro ⟨⟨_, hp⟩, h⟩; exact ⟨h, hp⟩
    · rintro ⟨h, hp⟩; refine ⟨⟨?_, hp⟩, h⟩; simp only [K, dim] at h ⊢; omega
  rw [← sum_filter, hset]
  have hterm : ∀ p ∈ Nat.primesLE (K n / 200), -(Lexp p n 200 : ℝ) * Real.log p ≤
      6 * dim n * ((Nat.log p (5 * K n) : ℝ) * Real.log p) +
        dim n * (if p ≤ 24 then Real.log 24 else 0) := by
    intro p hp
    have hp' := Nat.mem_primesLE.1 hp
    rw [neg_Lexp_small ((Nat.le_div_iff_mul_le (by norm_num)).1 hp'.1)]
    have := padicValNat_24_log_le hp'.2
    have hd : (0 : ℝ) ≤ dim n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hd]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 := sum_natLog_mul_log_le (y := K n / 200) (N := 5 * K n) (by omega)
  have hθ : θ ((K n : ℝ) / 200) = θ ((K n / 200 : ℕ) : ℝ) := by
    rw [theta_eq_theta_coe_floor,
      show ((K n : ℝ) / 200) = ((K n : ℕ) : ℝ) / ((200 : ℕ) : ℝ) by norm_num,
      Nat.floor_div_eq_div]
  have h2 : ∑ p ∈ Nat.primesLE (K n / 200), (if p ≤ 24 then Real.log 24 else 0) ≤
      25 * Real.log 24 := by
    rw [← sum_filter]
    have hc : #((Nat.primesLE (K n / 200)).filter (· ≤ 24)) ≤ 25 := by
      calc #((Nat.primesLE (K n / 200)).filter (· ≤ 24)) ≤ #(range 25) :=
            card_le_card fun p hp => by simp only [mem_filter] at hp; simp; omega
        _ = 25 := card_range 25
    rw [sum_const, nsmul_eq_mul]
    have : (0 : ℝ) ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    have : (#((Nat.primesLE (K n / 200)).filter (· ≤ 24)) : ℝ) ≤ 25 := by exact_mod_cast hc
    nlinarith
  have hd : (0 : ℝ) ≤ dim n := by positivity
  push_cast at h1
  rw [hθ]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 6 * dim n),
    mul_le_mul_of_nonneg_left h2 hd]

/-! ### The large primes -/

theorem neg_Lexp_le_large {n p : ℕ} (hp : p.Prime) (hK : 200 * 200 ^ 2 ≤ K n)
    (hp1 : K n < p * 200) :
    -(Lexp p n 200 : ℚ) ≤ p * Rx ((K n : ℚ) / p) + 1000 * 201 ^ 2 := by
  haveI := Fact.mk hp
  by_cases h3 : 3 * p ≤ K n
  · have := Inner.neg_Lexp_le (M := 200) (by norm_num) hK hp1 h3
    push_cast at this
    linarith
  · have hn : 1 ≤ n := by simp only [K] at hK; omega
    have := Outer.neg_Lexp_le (M := 200) hn (by norm_num) (not_le.1 h3)
    linarith

theorem large_primes_le (n : ℕ) (hK : 200 * 200 ^ 2 ≤ K n) :
    ∑ p ∈ Ps n, (if p * 200 ≤ K n then 0 else -(Lexp p n 200 : ℝ) * Real.log p) ≤
      psum n (20 / 37) 200 (fun p => p * (Rx ((K n : ℚ) / p) : ℝ) * Real.log p) +
        1000 * 201 ^ 2 * θ (37 / 20 * K n) := by
  have hθ : θ (37 / 20 * K n) = ∑ p ∈ Ps n, Real.log p := by
    have h2h : (37 / 20 : ℝ) * K n = 2 * dim n := by simp only [K, dim]; push_cast; ring
    rw [Chebyshev.theta, h2h, sum_primes_le_eq (by positivity) le_rfl]
    refine sum_congr rfl fun p hp => ?_
    rw [if_pos]
    have := (mem_Ps.1 hp).1
    exact_mod_cast (by omega : p ≤ 2 * dim n)
  rw [hθ, psum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun p hp => ?_
  have hp' := mem_Ps.1 hp
  have hp0 : 0 < p := hp'.2.pos
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le)
  have hp0' : (0 : ℚ) < p := by exact_mod_cast hp0
  by_cases h1 : p * 200 ≤ K n
  · have hc : ¬(20 / 37 ≤ (K n : ℚ) / p ∧ (K n : ℚ) / p < 200) := by
      rintro ⟨-, h⟩
      rw [div_lt_iff₀ hp0'] at h
      have : (K n : ℚ) < 200 * p := h
      have : K n < 200 * p := by exact_mod_cast this
      omega
    rw [if_pos h1, if_neg hc]
    linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000 * 201 ^ 2) hlog]
  · have hc : 20 / 37 ≤ (K n : ℚ) / p ∧ (K n : ℚ) / p < 200 := by
      constructor
      · rw [le_div_iff₀ hp0']
        have : p ≤ 2 * dim n := by omega
        have : (p : ℚ) ≤ 2 * dim n := by exact_mod_cast this
        have e : (2 * dim n : ℚ) = 37 / 20 * K n := by simp only [K, dim]; push_cast; ring
        linarith
      · rw [div_lt_iff₀ hp0']
        exact_mod_cast (by omega : K n < 200 * p)
    rw [if_neg h1, if_pos hc]
    have hb := neg_Lexp_le_large hp'.2 hK (not_le.1 h1)
    have hb' : -(Lexp p n 200 : ℝ) ≤ p * (Rx ((K n : ℚ) / p) : ℝ) + 1000 * 201 ^ 2 := by
      exact_mod_cast hb
    nlinarith [mul_le_mul_of_nonneg_right hb' hlog]

/-! ### (5.21) -/

/-- (5.21) for `M = 200`, in the form: for every `ε > 0`, eventually
`log m_{K,200} ≤ (A_200 + ε) K²`. -/
theorem normFactor_growth {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (normFactor n 200) ≤ ((AM 200 : ℝ) + ε) * (K n : ℝ) ^ 2 := by
  obtain ⟨ps, hrun, hps⟩ := Ex.run_of_chunksOK eR _ _ rChunks_ok
  set V : ℚ := (ps.map fun q => Ex.pieceInt q.1 q.2.1 q.2.2).sum
  have hV : (V : ℝ) + 6 * (37 / 40) / 200 ≤ AM 200 := by
    have := rBounds_sum
    have h : V + 6 * lambda / 200 ≤ AM 200 := by linarith
    have h' : ((V + 6 * lambda / 200 : ℚ) : ℝ) ≤ (AM 200 : ℚ) := by exact_mod_cast h
    simpa [lambda] using h'
  -- the pieces
  have hR := tendsto_psum_run eR le_rfl hrun
  rw [show (rChunks.map Prod.fst).flatten.getLastD (20 / 37) = 200 from rPoints_last] at hR
  have hdim : ∀ n, (dim n : ℝ) = 37 / 40 * K n := fun n => by simp only [K, dim]; push_cast; ring
  have hKinv : Tendsto (fun n => (K n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_K
  have T1 := (((tendsto_theta_K (c := 1 / 200) (by norm_num)).add
    ((tendsto_psi_K (c := 5) (by norm_num)).sub (tendsto_theta_K (c := 5) (by norm_num)))).const_mul
      (6 * (37 / 40 : ℝ)))
  have T3 := hKinv.const_mul (37 / 40 * (25 * Real.log 24))
  have T5 := ((tendsto_theta_K (c := 37 / 20) (by norm_num)).mul hKinv).const_mul
    (1000 * 201 ^ 2 : ℝ)
  have hsum := ((T1.add T3).add hR).add T5
  simp only [mul_zero, add_zero, sub_self] at hsum
  have hlim : 6 * (37 / 40) * (1 / 200 : ℝ) + (V : ℝ) < AM 200 + ε := by linarith
  filter_upwards [hsum.eventually (gt_mem_nhds hlim), eventually_ge_atTop 200000] with n hn hn0
  have hK : 200 * 200 ^ 2 ≤ K n := by simp only [K]; omega
  have hK0 : (0 : ℝ) < K n := by simp only [K]; push_cast; positivity
  -- split the sum
  rw [log_normFactor]
  have hsplit : ∑ p ∈ Ps n, -(Lexp p n 200 : ℝ) * Real.log p =
      ∑ p ∈ Ps n, (if p * 200 ≤ K n then -(Lexp p n 200 : ℝ) * Real.log p else 0) +
        ∑ p ∈ Ps n, (if p * 200 ≤ K n then 0 else -(Lexp p n 200 : ℝ) * Real.log p) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ => by split_ifs <;> ring
  rw [hsplit]
  have hs := small_primes_le n
  have hl := large_primes_le n hK
  have e1 : θ ((K n : ℝ) / 200) = θ (1 / 200 * K n) := by ring_nf
  rw [e1, hdim n] at hs
  have key : ∑ p ∈ Ps n, (if p * 200 ≤ K n then -(Lexp p n 200 : ℝ) * Real.log p else 0) +
      ∑ p ∈ Ps n, (if p * 200 ≤ K n then 0 else -(Lexp p n 200 : ℝ) * Real.log p) ≤
      (6 * (37 / 40) * (θ (1 / 200 * K n) / K n + (ψ (5 * K n) / K n - θ (5 * K n) / K n)) +
        37 / 40 * (25 * Real.log 24) * (K n : ℝ)⁻¹ +
        psum n (20 / 37) 200 (fun p => p * (eR.eval ((K n : ℚ) / p) : ℝ) * Real.log p) /
          (K n : ℝ) ^ 2 +
        1000 * 201 ^ 2 * (θ (37 / 20 * K n) / K n * (K n : ℝ)⁻¹)) * (K n : ℝ) ^ 2 := by
    have e2 : (6 * (37 / 40) * (θ (1 / 200 * K n) / K n + (ψ (5 * K n) / K n - θ (5 * K n) / K n)) +
        37 / 40 * (25 * Real.log 24) * (K n : ℝ)⁻¹ +
        psum n (20 / 37) 200 (fun p => p * (eR.eval ((K n : ℚ) / p) : ℝ) * Real.log p) /
          (K n : ℝ) ^ 2 +
        1000 * 201 ^ 2 * (θ (37 / 20 * K n) / K n * (K n : ℝ)⁻¹)) * (K n : ℝ) ^ 2 =
        6 * (37 / 40 * K n) * (θ (1 / 200 * K n) + ψ (5 * K n) - θ (5 * K n)) +
          37 / 40 * K n * (25 * Real.log 24) +
          psum n (20 / 37) 200 (fun p => p * (eR.eval ((K n : ℚ) / p) : ℝ) * Real.log p) +
          1000 * 201 ^ 2 * θ (37 / 20 * K n) := by
      field_simp
      ring
    rw [e2]
    simp only [Rx] at hl
    linarith
  refine key.trans (mul_le_mul_of_nonneg_right hn.le (by positivity))

end Zeta5
