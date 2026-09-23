/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Data.Nat.Prime.Factorial
import Zeta5.LocalBounds

/-!
# Integrality (Proposition 5.1)

`Q_{K,M} = m_{K,M} S_K Δ_K` has integer coefficients: at every prime `p` the exponent
`-L_p(K, M)` of `p` in `m_{K,M}` compensates the local bound of §3–§4 for `v_p^G(F_K)`.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

theorem VGe_prime_zpow_of_ne {q : ℕ} (hq : q.Prime) (hpq : q ≠ p) (k : ℤ) :
    VGe p 0 ((q : ℚ) ^ k) := by
  refine VGe_of_padicValRat fun _ => ?_
  have : Fact q.Prime := ⟨hq⟩
  rw [padicValRat.zpow, padicValRat.of_nat, padicValNat_primes hpq.symm]
  simp

/-- `v_p(m_{K,M}) = -L_p(K, M)` for `p ≤ 2h`. -/
theorem VGe_normFactor (n M : ℕ) :
    VGe p (if p ≤ 2 * dim n then -Lexp p n M else 0) (normFactor n M) := by
  set s := (Finset.range (2 * dim n + 1)).filter Nat.Prime
  have h := VGe_prod (p := p) s (w := fun q => if q = p then -Lexp p n M else 0)
    (f := fun q => (q : ℚ) ^ (-Lexp q n M)) fun q hq => by
      split_ifs with hqp
      · subst hqp; exact VGe_p_pow _
      · exact VGe_prime_zpow_of_ne (mem_filter.1 hq).2 hqp _
  rw [sum_ite_eq' s p] at h
  have hmem : p ∈ s ↔ p ≤ 2 * dim n := by
    simp only [s, mem_filter, mem_range, hp.out, and_true]; omega
  simp only [hmem] at h
  exact h

theorem VGe_div_nat {a b : ℕ} (hb : ¬p ∣ b) : VGe p 0 ((a : ℚ) / b) := by
  rw [VGe, padicNorm.div, (padicNorm.nat_eq_one_iff b).2 hb, div_one, neg_zero, zpow_zero]
  exact padicNorm.of_nat a

/-- For `p > 2h`, every factorial in `S_K` is a `p`-adic unit. -/
theorem VGe_S_of_lt {n : ℕ} (hp2 : 2 * dim n < p) : VGe p 0 (S n) := by
  have hfac : ∀ m : ℕ, m < p → ¬p ∣ m.factorial := fun m hm h =>
    absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (not_le.2 hm)
  have hden : ¬p ∣ (N n).factorial ^ (12 * dim n) *
      ∏ i ∈ Finset.Icc 1 (dim n - 1), (2 * i).factorial ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · exact hfac _ (by simp only [N, dim] at hp2 ⊢; omega) (Nat.Prime.dvd_of_dvd_pow hp.out h)
    · obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finsetProd_iff hp.out.prime _).1 h
      have := (Finset.mem_Icc.1 hi).2
      exact hfac _ (by omega) (Nat.Prime.dvd_of_dvd_pow hp.out hdvd)
  have hS : S n = (((K n).factorial ^ (2 * dim n) * 4 ^ (dim n - 1) : ℕ) : ℚ) /
      (((N n).factorial ^ (12 * dim n) * ∏ i ∈ Finset.Icc 1 (dim n - 1),
        (2 * i).factorial ^ 2 : ℕ) : ℚ) := by
    rw [S]; push_cast; rfl
  rw [hS]
  exact VGe_div_nat hden

theorem VGe_S (n : ℕ) : VGe p (padicValRat p (S n)) (S n) :=
  (VGe_iff (S_pos n).ne').2 le_rfl

/-- **Proposition 5.1**: `Q_{K,M} = m_{K,M} F_K` has integer coefficients. -/
theorem QKM_integral {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) :
    ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = Q n M := by
  refine exists_intPoly_of_forall_prime fun p hp' => ?_
  have : Fact p.Prime := ⟨hp'⟩
  have hm := VGe_normFactor (p := p) n M
  -- the local bound for `F_K`
  have hF : PolyVGe p (if p ≤ 2 * dim n then Lexp p n M else 0) (F n) := by
    split_ifs with hp2
    · unfold Lexp
      split_ifs with h1 h2
      · exact smallPrime_bound p n
      · rw [F]; exact (PolyVGe_C (VGe_S n)).mul (inner_bound hM hK (by omega) h2)
      · rw [F]
        refine (PolyVGe_C (VGe_S n)).mul ?_
        by_cases hpK : p ≤ K n
        · exact outer_bound hM hK (by omega) hpK
        · have : Outer.gammaOut p n = 0 := by simp [Outer.gammaOut, not_le.1 hpK]
          rw [this]; exact big_bound (not_le.1 hpK)
    · rw [F]
      have := (PolyVGe_C (VGe_S_of_lt (p := p) (not_le.1 hp2))).mul
        (big_bound (p := p) (n := n) (by simp only [K, dim] at hp2 ⊢; omega))
      simpa using this
  have := (PolyVGe_C hm).mul hF
  rw [Q]
  convert this using 1
  split_ifs <;> simp

end Zeta5
