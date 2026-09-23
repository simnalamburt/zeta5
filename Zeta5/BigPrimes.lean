/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.GramBasis
import Zeta5.SmallPrimes

/-!
# Primes `p > K` (Proposition 4.3, second part)

For `p > K` every pole `x = ±j` of the pulled back entries of `G_K` has `|x| < p`. The only
congruent poles are `j` and `j - p`, and the divided difference makes their contribution integral
because `H⁽⁵⁾_j ≡ H⁽⁵⁾_{p-1-j} (mod p)`. The polynomial parts have degree `≤ 104n + 1 < 4p - 2`, so
their `τ`-values are integral too. Hence `G_K` itself is `p`-integral, and so is `Δ_K`. (The paper
passes to a unimodular basis first; this is not needed.)
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [Fact p.Prime]

theorem PolyVGe.pow {w : ℤ} {P : ℚ[X]} (hP : PolyVGe p w P) (k : ℕ) :
    PolyVGe p (k * w) (P ^ k) := by
  induction k with
  | zero =>
    simpa using PolyVGe_C (p := p) (VGe_one (p := p))
  | succ k ih => rw [pow_succ]; exact (ih.mul hP).mono (by push_cast; ring_nf; rfl)

theorem PolyVGe_comp {A B : ℚ[X]} (hA : PolyVGe p 0 A) (hB : PolyVGe p 0 B) :
    PolyVGe p 0 (A.comp B) := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine PolyVGe_sum _ fun e _ => ?_
  simpa using PolyVGe.C_mul (hA e) (hB.pow e)

theorem PolyVGe_D (m : ℕ) : PolyVGe p 0 (D m) := by
  have := PolyVGe_prod (p := p) (Icc 1 m) (w := fun _ => 0)
    (f := fun j : ℕ => X + C ((j : ℚ) ^ 2)) fun j _ =>
      PolyVGe_X.add (PolyVGe_C (by
        have := VGe_natCast (p := p) (j ^ 2); push_cast at this; exact this))
  simpa [D, poleDen] using this

theorem PolyVGe_pull (S : Finset ℕ) {A : ℚ[X]} (hA : PolyVGe p 0 A) : PolyVGe p 0 (pull S A) := by
  rw [pull]
  have h1 : PolyVGe p 0 (C ((-1 : ℚ) ^ S.card)) := PolyVGe_C (by
    simpa using VGe_intCast (p := p) ((-1) ^ S.card))
  have h2 := (PolyVGe_X (p := p)).pow 5
  have h3 := PolyVGe_comp hA ((PolyVGe_X (p := p)).pow 2).neg
  simpa using (h1.mul h2).mul h3

/-- **Proposition 4.3**, second part: `Δ_K` is `p`-integral for `p > K`. -/
theorem big_bound' {n : ℕ} (hp : K n < p) : PolyVGe p 0 (Δ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : dim 0 = 0 := rfl
    rw [Δ]
    have h0 : (G 0).det = 1 := by
      rw [Matrix.det_eq_one_of_card_eq_zero]; simp [this]
    rw [h0]
    simpa using PolyVGe_C (p := p) VGe_one
  have hp5 : 5 ≤ p := by simp only [K] at hp; omega
  have hG : ∀ i j : Fin (dim n), PolyVGe p 0 (G n i j) := by
    intro i j
    simp only [G, Matrix.of_apply]
    rw [muX_eq_tauR _ _ (by simp), poleSet_Icc]
    have hN : PolyVGe p 0 (D (N n) ^ 6 * X ^ ((i : ℕ) + j)) := by
      simpa using ((PolyVGe_D (p := p) (N n)).pow 6).mul ((PolyVGe_X (p := p)).pow _)
    refine PolyVGe_tauR_small hp5 (fun r hr => ?_) (PolyVGe_pull _ hN) ?_
    · simp only [RK, mem_erase, mem_Icc] at hr; omega
    · rw [natDegree_divByMonic _ (poleProd_monic _), natDegree_poleProd, card_RK]
      have hA : (D (N n) ^ 6 * X ^ ((i : ℕ) + j)).natDegree ≤ 6 * N n + (i + j) := by
        refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_pow_le _))
        refine natDegree_pow_le.trans ?_
        rw [natDegree_D]
      have hpull : (pull (Icc 1 (K n)) (D (N n) ^ 6 * X ^ ((i : ℕ) + j))).natDegree ≤
          5 + 2 * (6 * N n + (i + j)) := by
        rw [pull]
        refine natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans ?_) ?_)
        · simp
        · refine natDegree_comp_le.trans ?_
          have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by simp
          rw [this]; nlinarith
      have hi := i.2; have hj := j.2
      simp only [dim, N, K] at hpull hi hj hp ⊢
      omega
  have := PolyVGe_det (G n) (fun _ => 0) (fun _ _ => 0) (fun _ _ => by simp) hG
  simpa [Δ] using this

end Zeta5
