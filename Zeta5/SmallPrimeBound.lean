/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.GramBasis
import Zeta5.SmallPrimes

/-!
# The small prime bound (3.11), (3.12)

In the basis `q_0 = 1`, `q_i(t) = (-1)^i 2t D_{i-1}(t) / (2i)!` the matrix
`[(K!)² μ_X(f_i f_j / D_K)]`, `f_i = (D_N/(N!)²)³ q_i`, has determinant `F_K` (3.11). Under
`t = -x²` both `D_N(t)/(N!)²` and `q_i(t)` become integer-valued, since
`q_i(-x²) = C(x + i, 2i) + C(x + i - 1, 2i)`. Lemma 3.3 bounds every entry, which gives (3.12).
-/

open Polynomial Finset

namespace Zeta5

/-! ### Products of consecutive integers -/

theorem prod_range_eq_prod_Ioc (a : ℤ) (n : ℕ) :
    ∏ j ∈ range n, (((a + n : ℤ) : ℚ) - j) = ∏ k ∈ Ioc a (a + n), (k : ℚ) := by
  refine prod_nbij' (fun j => a + n - j) (fun k => (a + n - k).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range, mem_Ioc] at hj ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ioc] at hk ⊢; omega
  · intro j hj; simp only [mem_range] at hj; omega
  · intro k hk; simp only [mem_Ioc] at hk; omega
  · intro j _; push_cast; ring

/-- A product of `n` consecutive integers is `n!` times an integer. -/
theorem prod_Ioc_eq_factorial_mul (a : ℤ) (n : ℕ) :
    ∏ k ∈ Ioc a (a + n), (k : ℚ) = n.factorial * (Ring.choose (a + n) n : ℤ) := by
  rw [← binomP_eval_int, binomP, eval_mul, eval_C, descPochhammer_eval_eq_prod_range,
    prod_range_eq_prod_Ioc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

variable {p : ℕ} [Fact p.Prime]

theorem VGe_prod_Ioc_div (a : ℤ) (n : ℕ) :
    VGe p 0 ((∏ k ∈ Ioc a (a + n), (k : ℚ)) / n.factorial) := by
  rw [prod_Ioc_eq_factorial_mul, mul_div_cancel_left₀ _ (by positivity)]
  exact VGe_intCast _

/-! ### Integer values of `D_N(-x²)/(N!)²` -/

theorem VGe_D_div (N : ℕ) (y : ℤ) :
    VGe p 0 ((D N).eval (-(y : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2) := by
  have h1 : ∏ j ∈ Icc 1 N, ((j : ℚ) + y) = ∏ k ∈ Ioc y (y + N), (k : ℚ) := by
    refine prod_nbij' (fun j => y + j) (fun k => (k - y).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc, mem_Ioc] at hj ⊢; omega
    · intro k hk; simp only [mem_Icc, mem_Ioc] at hk ⊢; omega
    · intro j _; simp
    · intro k hk; simp only [mem_Ioc] at hk; omega
    · intro j _; push_cast; ring
  have h2 : ∏ j ∈ Icc 1 N, ((j : ℚ) - y) = ∏ k ∈ Ioc (-y) (-y + N), (k : ℚ) := by
    refine prod_nbij' (fun j => j - y) (fun k => (k + y).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc, mem_Ioc] at hj ⊢; omega
    · intro k hk; simp only [mem_Icc, mem_Ioc] at hk ⊢; omega
    · intro j _; simp
    · intro k hk; simp only [mem_Ioc] at hk; omega
    · intro j _; push_cast; ring
  have : (D N).eval (-(y : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2 =
      ((∏ k ∈ Ioc (-y) (-y + N), (k : ℚ)) / N.factorial) *
        ((∏ k ∈ Ioc y (y + N), (k : ℚ)) / N.factorial) := by
    rw [← h1, ← h2, D, poleDen, eval_prod, div_mul_div_comm, ← sq, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    simp only [eval_add, eval_X, eval_C]
    ring
  rw [this]
  simpa using (VGe_prod_Ioc_div (p := p) (-y) N).mul (VGe_prod_Ioc_div (p := p) y N)

/-! ### The basis `q_i` -/

/-- `q_0 = 1`, `q_i(t) = (-1)^i 2t D_{i-1}(t) / (2i)!`. -/
noncomputable def qb (i : ℕ) : ℚ[X] :=
  if i = 0 then 1 else C ((-1) ^ i * 2 / ((2 * i).factorial : ℚ)) * X * D (i - 1)

theorem natDegree_qb (i : ℕ) : (qb i).natDegree ≤ i := by
  unfold qb
  split_ifs with hi
  · simp
  · refine (natDegree_mul_le).trans ?_
    rw [natDegree_D]
    have : (C ((-1 : ℚ) ^ i * 2 / ((2 * i).factorial : ℚ)) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    omega

theorem coeff_qb (i : ℕ) :
    (qb i).coeff i = if i = 0 then 1 else (-1) ^ i * 2 / ((2 * i).factorial : ℚ) := by
  unfold qb
  split_ifs with hi
  · subst hi; simp
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [mul_assoc, coeff_C_mul, coeff_X_mul, Nat.add_sub_cancel]
    have h := (D_monic j).coeff_natDegree
    rw [natDegree_D] at h
    rw [h, mul_one]

/-- `y ∏_{1 ≤ j ≤ i} (y² - j²)` is the product of the `2i + 1` integers around `y`. -/
theorem prod_centered (y : ℤ) (i : ℕ) :
    ∏ k ∈ Ioc (y - i - 1) (y + i), (k : ℚ) = y * ∏ j ∈ Icc 1 i, ((y : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  induction i with
  | zero =>
    have : Ioc (y - (0 : ℕ) - 1) (y + (0 : ℕ)) = {y} := by
      ext k; simp only [mem_Ioc, mem_singleton]; push_cast; omega
    rw [this]; simp
  | succ i ih =>
    have hs : Ioc (y - (i + 1 : ℕ) - 1) (y + (i + 1 : ℕ)) =
        insert (y - i - 1) (insert (y + i + 1) (Ioc (y - i - 1) (y + i))) := by
      ext k; simp only [mem_Ioc, mem_insert]; push_cast; omega
    rw [hs, prod_insert (by simp only [mem_insert, mem_Ioc]; omega),
      prod_insert (by simp only [mem_Ioc]; omega), ih, prod_Icc_succ_top (by omega)]
    push_cast
    ring

/-- `q_i(-y²)` is an integer: `q_{i+1}(-y²) = C(y + i + 1, 2i + 2) + C(y + i, 2i + 2)`. -/
theorem VGe_qb (i : ℕ) (y : ℤ) : VGe p 0 ((qb i).eval (-(y : ℚ) ^ 2)) := by
  rcases i with _ | i
  · simpa [qb] using VGe_one (p := p)
  have hD : (D i).eval (-(y : ℚ) ^ 2) = (-1) ^ i * ∏ j ∈ Icc 1 i, ((y : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
    rw [D, poleDen, eval_prod, show ((-1 : ℚ) ^ i) = (-1) ^ #(Icc 1 i) by simp, ← prod_neg]
    refine prod_congr rfl fun j _ => ?_
    simp only [eval_add, eval_X, eval_C]
    ring
  have e1 : ∏ k ∈ Ioc (y - i - 1) (y - i - 1 + (2 * (i + 1) : ℕ)), (k : ℚ) =
      ((y : ℚ) + i + 1) * ∏ k ∈ Ioc (y - i - 1) (y + i), (k : ℚ) := by
    rw [show y - i - 1 + ((2 * (i + 1) : ℕ) : ℤ) = y + i + 1 by push_cast; ring,
      show Ioc (y - i - 1) (y + i + 1) = insert (y + i + 1) (Ioc (y - i - 1) (y + i)) by
        ext k; simp only [mem_Ioc, mem_insert]; omega,
      prod_insert (by simp only [mem_Ioc]; omega)]
    push_cast; ring
  have e2 : ∏ k ∈ Ioc (y - i - 2) (y - i - 2 + (2 * (i + 1) : ℕ)), (k : ℚ) =
      ((y : ℚ) - i - 1) * ∏ k ∈ Ioc (y - i - 1) (y + i), (k : ℚ) := by
    rw [show y - i - 2 + ((2 * (i + 1) : ℕ) : ℤ) = y + i by push_cast; ring,
      show Ioc (y - i - 2) (y + i) = insert (y - i - 1) (Ioc (y - i - 1) (y + i)) by
        ext k; simp only [mem_Ioc, mem_insert]; omega,
      prod_insert (by simp only [mem_Ioc]; omega)]
    push_cast; ring
  have hc := prod_centered y i
  have : (qb (i + 1)).eval (-(y : ℚ) ^ 2) =
      (∏ k ∈ Ioc (y - i - 1) (y - i - 1 + (2 * (i + 1) : ℕ)), (k : ℚ)) /
          ((2 * (i + 1)).factorial : ℚ) +
        (∏ k ∈ Ioc (y - i - 2) (y - i - 2 + (2 * (i + 1) : ℕ)), (k : ℚ)) /
          ((2 * (i + 1)).factorial : ℚ) := by
    have hq : qb (i + 1) = C ((-1) ^ (i + 1) * 2 / ((2 * (i + 1)).factorial : ℚ)) * X * D i := by
      simp [qb]
    rw [e1, e2, ← add_div, ← add_mul, hq, eval_mul, eval_mul, eval_C, eval_X, hD]
    rw [hc]
    have hsq : ((-1 : ℚ) ^ (i + 1)) * (-1) * (-1) ^ i = 1 := by
      rw [← pow_succ, ← pow_add, show i + 1 + 1 + i = 2 * (i + 1) by ring, pow_mul]; norm_num
    field_simp
    linear_combination (2 * (y : ℚ) ^ 2 * ∏ j ∈ Icc 1 i, ((y : ℚ) ^ 2 - (j : ℚ) ^ 2)) * hsq
  rw [this]
  exact (VGe_prod_Ioc_div _ _).add (VGe_prod_Ioc_div _ _)

/-! ### The change of basis (3.11) -/

/-- The basis `q_0, …, q_{h-1}`. -/
noncomputable def qbasis (n : ℕ) : Fin (dim n) → ℚ[X] := fun i => qb i

/-- `(K!)² / (N!)^{12}`. -/
noncomputable def cK (n : ℕ) : ℚ := ((K n).factorial : ℚ) ^ 2 / ((N n).factorial : ℚ) ^ 12

theorem prod_range_eq_prod_Icc (f : ℕ → ℚ) (hf : f 0 = 1) (h : ℕ) :
    ∏ i ∈ range h, f i = ∏ i ∈ Icc 1 (h - 1), f i := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [prod_range_succ, ih]
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp [hf]
    · rw [show h + 1 - 1 = (h - 1) + 1 by omega, prod_Icc_succ_top (by omega),
        Nat.sub_add_cancel hh]

theorem det_qbasis (n : ℕ) : (coeffMat (qbasis n)).det ^ 2 * cK n ^ dim n = S n := by
  rw [det_coeffMat_of_triangular (qbasis n) fun i => natDegree_qb i, ← prod_pow]
  simp only [qbasis, coeff_qb]
  rw [Fin.prod_univ_eq_prod_range (fun i => (if i = 0 then (1 : ℚ) else
      (-1) ^ i * 2 / ((2 * i).factorial : ℚ)) ^ 2) (dim n),
    prod_range_eq_prod_Icc _ (by simp)]
  have : ∀ i ∈ Icc 1 (dim n - 1), (if i = 0 then (1 : ℚ) else
      (-1) ^ i * 2 / ((2 * i).factorial : ℚ)) ^ 2 = 4 / ((2 * i).factorial : ℚ) ^ 2 := by
    intro i hi
    have hi0 : i ≠ 0 := by have := (mem_Icc.1 hi).1; omega
    simp only [hi0, ↓reduceIte]
    rw [div_pow, mul_pow, ← pow_mul,
      mul_comm i 2, pow_mul]
    norm_num
  rw [prod_congr rfl this, prod_div_distrib, prod_const, Nat.card_Icc, S, cK, div_pow, ← pow_mul,
    ← pow_mul]
  push_cast
  field_simp

theorem natDegree_qbasis_lt (n : ℕ) (i : Fin (dim n)) : (qbasis n i).natDegree < dim n :=
  (natDegree_qb i).trans_lt i.2

/-- (3.11): `F_K = det [(K!)² μ_X(f_i f_j / D_K)]`. -/
theorem F_eq_det (n : ℕ) :
    F n = (gram (C (cK n) * D (N n) ^ 6) (Icc 1 (K n)) (qbasis n)).det := by
  have h1 : gram (C (cK n) * D (N n) ^ 6) (Icc 1 (K n)) (qbasis n) =
      C (cK n) • gram (D (N n) ^ 6) (Icc 1 (K n)) (qbasis n) := by
    ext i j : 1
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, muX_C_mul]
  rw [h1, Matrix.det_smul, det_gram_change _ _ _ (natDegree_qbasis_lt n), ← G_eq_gram, ← Δ, F,
    Fintype.card_fin, ← det_qbasis]
  simp only [map_mul, map_pow]
  ring

/-! ### The entries -/

variable {p : ℕ} [Fact p.Prime]

theorem pull_C_mul (S : Finset ℕ) (c : ℚ) (A : ℚ[X]) : pull S (C c * A) = C c * pull S A := by
  rw [← smul_eq_C_mul, pull_smul, smul_eq_C_mul]

/-- Every entry of (3.11) satisfies Lemma 3.3. -/
theorem entry_bound {n : ℕ} (i j : Fin (dim n)) :
    PolyVGe p (-6 * Nat.log p (5 * K n))
      (gram (C (cK n) * D (N n) ^ 6) (Icc 1 (K n)) (qbasis n) i j) := by
  have hn : 1 ≤ n := by have := i.2; simp only [dim] at this; omega
  have hK : 1 ≤ K n := by simp only [K]; omega
  set B := C (((N n).factorial : ℚ) ^ 12)⁻¹ * D (N n) ^ 6 * qb i * qb j
  have hA : C (cK n) * D (N n) ^ 6 * qbasis n i * qbasis n j =
      C (((K n).factorial : ℚ) ^ 2) * B := by
    simp only [B, qbasis, cK, div_eq_mul_inv, C_mul]; ring
  simp only [gram, Matrix.of_apply]
  rw [hA, muX_eq_tauR _ _ (by simp), pull_C_mul, poleSet_Icc]
  refine lemma33 hK _ ?_ fun y => ?_
  · -- `deg ≤ 5 + 2 (6N + i + j) ≤ 12N + 4h + 1 < 5K`
    have h1 : (C (((N n).factorial : ℚ) ^ 12)⁻¹ * D (N n) ^ 6).natDegree ≤ 6 * N n :=
      (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by rw [natDegree_D]))
    have h2 := (natDegree_mul_le (p := C (((N n).factorial : ℚ) ^ 12)⁻¹ * D (N n) ^ 6)
      (q := qb i)).trans (add_le_add h1 (natDegree_qb i))
    have hB : B.natDegree ≤ 6 * N n + i + j :=
      (natDegree_mul_le (q := qb j)).trans (add_le_add h2 (natDegree_qb j))
    have hcomp : (B.comp (-X ^ 2)).natDegree ≤ 2 * (6 * N n + i + j) := by
      refine natDegree_comp_le.trans ?_
      have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by simp
      rw [this]; nlinarith
    have hpull : (pull (Icc 1 (K n)) B).natDegree ≤ 5 + 2 * (6 * N n + i + j) := by
      rw [pull]
      refine (natDegree_mul_le).trans (add_le_add ((natDegree_mul_le).trans ?_) hcomp)
      simp
    have hi := i.2
    have hj := j.2
    simp only [dim, N, K] at hpull hi hj ⊢
    omega
  · have hv : (pull (Icc 1 (K n)) B).eval (y : ℚ) =
        (((-1 : ℤ) ^ #(Icc 1 (K n)) * y ^ 5 : ℤ) : ℚ) *
          (((D (N n)).eval (-(y : ℚ) ^ 2) / ((N n).factorial : ℚ) ^ 2) ^ 6 *
            ((qb i).eval (-(y : ℚ) ^ 2) * (qb j).eval (-(y : ℚ) ^ 2))) := by
      simp only [pull, B, eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_neg]
      push_cast
      field_simp
    rw [hv]
    have := (VGe_intCast (p := p) ((-1 : ℤ) ^ #(Icc 1 (K n)) * y ^ 5)).mul
      (((VGe_D_div (p := p) (N n) y).pow 6).mul ((VGe_qb (p := p) i y).mul (VGe_qb (p := p) j y)))
    simpa using this

/-- **(3.12)**: `v_p^G(F_K) ≥ -6h ⌊log_p(5K)⌋ - h v_p(24)` for every prime `p`. -/
theorem smallPrime_bound' (n : ℕ) :
    PolyVGe p (-6 * dim n * Nat.log p (5 * K n) - dim n * padicValNat p 24) (F n) := by
  rw [F_eq_det]
  have h := PolyVGe_det (p := p) (gram (C (cK n) * D (N n) ^ 6) (Icc 1 (K n)) (qbasis n))
    (fun _ => -6 * Nat.log p (5 * K n)) (fun _ _ => -6 * Nat.log p (5 * K n))
    (fun _ _ => by ring_nf; rfl)
    fun i j => entry_bound i j
  refine h.mono ?_
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (0 : ℤ) ≤ dim n * padicValNat p 24 := by positivity
  linarith

end Zeta5
