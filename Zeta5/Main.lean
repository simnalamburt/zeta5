/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Zeta5.Theorem21

/-!
# Irrationality of ζ(5)

This file follows the structure of A. Fauzan, *ζ(5) is irrational* (17 September 2026,
`ZETA5_IS_IRRATIONAL.pdf` in this repository).

The paper constructs integer polynomials `Qₙ := Q_{40n,200} ∈ ℤ[X]` of degree `37n` with
`0 < Qₙ(ζ(5)) < exp(-139n²/5)` for all sufficiently large `n` (Theorem 2.1 of the paper), and
deduces irrationality by a short integrality argument (§1.1).

* `Zeta5.irrational_of_smallIntPolys` formalises the deduction in §1.1 for an arbitrary real
  number: if such a sequence of integer polynomials exists at `x`, then `x` is irrational.
* `Zeta5.exists_smallIntPolys_zeta5` is the existence statement provided by Theorem 2.1 of the
  paper (Sections 2–7 and Appendices A–B), with `Qₙ := Q_{40n,200}` of `Zeta5.Defs`. It is derived
  from the four parts of Theorem 2.1 stated in `Zeta5.Theorem21`, which are not yet proved.
* `irrational_zeta_five` combines the two.
-/

open Polynomial Filter

namespace Zeta5

/-- The integrality argument of §1.1 of the paper.

If, for all sufficiently large `n`, there is an integer polynomial `Q` of degree at most `37n`
with `0 < Q(x) < exp(-139 n² / 5)`, then `x` is irrational.

Proof: if `x = a / b` with `b ≥ 1`, then `b ^ (37 n) * Q(x)` is a positive integer, hence `≥ 1`,
but it is at most `exp(37 n (b - 1) - 139 n² / 5) < 1` once `n ≥ 2 b`. -/
theorem irrational_of_smallIntPolys (x : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ 37 * n ∧
      0 < aeval x Q ∧ aeval x Q < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2)) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hdpos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  set n : ℕ := N + 2 * q.den with hn
  have hnR : (n : ℝ) = N + 2 * q.den := by rw [hn]; push_cast; ring
  obtain ⟨Q, hQdeg, hQpos, hQlt⟩ := hN n (by omega)
  -- `m = den ^ (deg Q) * Q(q)` is an integer.
  set m : ℤ := (Q.scaleRoots (q.den : ℤ)).eval q.num with hm
  have key : (m : ℝ) = (q.den : ℝ) ^ Q.natDegree * aeval (q : ℝ) Q := by
    have h1 : (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := by
      rw [Rat.cast_def]; field_simp
    have h2 := scaleRoots_eval₂_mul (p := Q) (Int.castRingHom ℝ) (q : ℝ) (q.den : ℤ)
    have h3 := eval₂_at_apply (p := Q.scaleRoots (q.den : ℤ)) (Int.castRingHom ℝ) q.num
    simp only [eq_intCast, Int.cast_natCast] at h2 h3
    rw [hm, aeval_def, algebraMap_int_eq, ← h3, h1, h2]
  have hm_one : (1 : ℝ) ≤ m := by
    have h0 : (0 : ℝ) < m := by rw [key]; exact mul_pos (pow_pos hdpos _) hQpos
    have h0' : (0 : ℤ) < m := by exact_mod_cast h0
    have h1' : (1 : ℤ) ≤ m := by omega
    exact_mod_cast h1'
  -- `den ^ (deg Q) ≤ den ^ (37 n) ≤ exp (37 n (den - 1))`.
  have hpow : (q.den : ℝ) ^ Q.natDegree ≤ Real.exp (37 * n * ((q.den : ℝ) - 1)) := by
    calc (q.den : ℝ) ^ Q.natDegree ≤ (q.den : ℝ) ^ (37 * n) := pow_le_pow_right₀ hd1 hQdeg
      _ ≤ (Real.exp ((q.den : ℝ) - 1)) ^ (37 * n) := by
          apply pow_le_pow_left₀ hdpos.le
          linarith [Real.add_one_le_exp ((q.den : ℝ) - 1)]
      _ = Real.exp (37 * n * ((q.den : ℝ) - 1)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- The quadratic decay beats the exponential growth of `den ^ (37 n)` once `n ≥ 2 den`.
  have hlt : Real.exp (37 * n * ((q.den : ℝ) - 1)) *
      Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) < 1 := by
    rw [← Real.exp_add, Real.exp_lt_one_iff]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h2d : 2 * (q.den : ℝ) ≤ n := by rw [hnR]; linarith
    have hn0 : (0 : ℝ) < n := by rw [hnR]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h2d hn0.le]
  have : (1 : ℝ) < 1 := by
    calc (1 : ℝ) ≤ m := hm_one
      _ = (q.den : ℝ) ^ Q.natDegree * aeval (q : ℝ) Q := key
      _ ≤ Real.exp (37 * n * ((q.den : ℝ) - 1)) * aeval (q : ℝ) Q :=
          mul_le_mul_of_nonneg_right hpow hQpos.le
      _ < Real.exp (37 * n * ((q.den : ℝ) - 1)) * Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left hQlt (Real.exp_pos _)
      _ < 1 := hlt
  exact lt_irrefl _ this

/-- The consequence of Theorem 2.1 of the paper used in §1.1: for all sufficiently large `n`
there is an integer polynomial `Qₙ` (namely `Q_{40n,200}`) of degree at most `37n` with
`0 < Qₙ(ζ(5)) < exp(-139 n² / 5)`.

The admissibility condition `K ≥ 200M²` of Theorem 2.1 holds for `M = 200` once `n ≥ 200000`. -/
theorem exists_smallIntPolys_zeta5 :
    ∀ᶠ n : ℕ in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ 37 * n ∧
      0 < aeval (riemannZeta 5).re Q ∧
        aeval (riemannZeta 5).re Q < Real.exp (-(139 / 5 : ℝ) * (n : ℝ) ^ 2) := by
  filter_upwards [QKM_decay, eventually_ge_atTop 200000] with n hdecay hn
  obtain ⟨q, hq⟩ := QKM_mem_int (n := n) (M := 200) (by norm_num) (by simp only [K]; omega)
  have hval : aeval (riemannZeta 5).re q = aeval (riemannZeta 5).re (Q n 200) := by
    rw [← hq, ← algebraMap_int_eq, aeval_map_algebraMap]
  refine ⟨q, ?_, hval ▸ QKM_pos n 200, hval ▸ hdecay⟩
  have hdeg := QKM_natDegree n 200
  rw [← hq, natDegree_map_eq_of_injective (RingHom.injective_int _)] at hdeg
  simp [hdeg, dim]

end Zeta5

/-- ζ(5) is irrational (Theorem 1.1 of the paper). -/
theorem irrational_zeta_five : Irrational (riemannZeta 5).re :=
  Zeta5.irrational_of_smallIntPolys _ Zeta5.exists_smallIntPolys_zeta5
