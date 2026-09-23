/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.InnerCount
import Zeta5.InnerEntry
import Zeta5.Unimodular

/-!
# The inner range (Proposition 4.1)

Under (4.1) we use the basis (4.5) `E_{a,i} = ∏_{c ≠ a} (t + c²)^{L_c} (t + a²)^i` with the weights
(4.6), (4.7). It is `ℤ_p`-unimodular by the Chinese remainder theorem. Each entry has valuation at
least `min_c E_c - 4` (`PolyVGe_entry`), and splitting `2(E_c - 4)` into the half-weights of the two
rows shows that this is at least the sum of the two row weights, as in the paper.
-/

open Polynomial Finset

namespace Zeta5

variable {p : ℕ} [hp : Fact p.Prime]

namespace Inner

set_option linter.unusedSectionVars false

/-! ### Consequences of (4.1) -/

section Hyp

variable {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n)
include hM hK hp1 hp2

theorem hyp_n : 1 ≤ n := by
  simp only [K] at hK; nlinarith

theorem hyp_pM : 200 * M < p := by
  by_contra h
  have : p * M ≤ 200 * M * M := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem hyp_Mn : M ≤ n := by
  simp only [K] at hK; nlinarith

theorem hyp_p5 : 5 ≤ p := by
  have := hyp_pM hM hK hp1 hp2; omega

theorem hyp_p2 : p ≠ 2 := by
  have := hyp_pM hM hK hp1 hp2; omega

theorem hyp_odd : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · exact absurd h (hyp_p2 hM hK hp1 hp2)
  · exact h

theorem hyp_m : 1 ≤ (p - 1) / 2 := by
  have := hyp_p5 hM hK hp1 hp2; omega

theorem hyp_two_m : 2 * ((p - 1) / 2) = p - 1 := by
  have := hyp_odd hM hK hp1 hp2; omega

/-- `p² > 200 K`. -/
theorem hyp_sq : 200 * K n < p ^ 2 := by
  have h1 := hyp_pM hM hK hp1 hp2
  have : 200 * (p * M) ≤ p * p := by nlinarith
  nlinarith

theorem hyp_mN : N n / p ≤ n := by
  have := hyp_p5 hM hK hp1 hp2
  exact (Nat.div_le_div_left (by omega : 5 ≤ p) (by omega)).trans (by simp only [N]; omega)

theorem hyp_mK : K n / p < M := by
  rw [Nat.div_lt_iff_lt_mul (by have := hyp_p5 hM hK hp1 hp2; omega)]; linarith

end Hyp

/-! ### The allocation -/

section Alloc

/-- `m`. -/
abbrev mm (p : ℕ) : ℕ := (p - 1) / 2

theorem rhs_eq (n M : ℕ) : rhs p n M = mm p * T p n M + E p n M := by
  rw [T, E]; exact (Int.mul_ediv_add_emod _ _).symm

variable {n M : ℕ}
variable (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n)
include hM hK hp1 hp2

theorem mm_pos : (0 : ℤ) < mm p := by
  have := hyp_m hM hK hp1 hp2
  simp only [mm]
  omega

theorem E_nonneg : 0 ≤ E p n M := Int.emod_nonneg _ (mm_pos hM hK hp1 hp2).ne'

theorem E_lt : E p n M < mm p := Int.emod_lt_of_pos _ (mm_pos hM hK hp1 hp2)

theorem rhs_bound : 2 * rhs p n M = 92 * n - 8 * M - 20 - 6 * (N n / p : ℕ) := by
  simp only [rhs, dim, L0, N]; push_cast; ring

/-- `T ≥ b_a`: the dimensions `L_a` are nonnegative. -/
theorem b_le_T {a : ℕ} (ha : a ∈ classes p) : b p n a ≤ T p n M := by
  have ha' := mem_Icc.1 ha
  have hell := ell_mul_le (p := p) (A := N n) (a := a) (by omega)
  have htwo := hyp_two_m hM hK hp1 hp2
  have hmN := hyp_mN hM hK hp1 hp2
  have hMn := hyp_Mn hM hK hp1 hp2
  have hn := hyp_n hM hK hp1 hp2
  have hp5 := hyp_p5 hM hK hp1 hp2
  have hr := rhs_eq (p := p) n M
  have hE := E_lt hM hK hp1 hp2
  have h2r := rhs_bound hM hK hp1 hp2
  have e1 : 2 * ((mm p : ℕ) : ℤ) + 1 = p := by
    have : 2 * mm p + 1 = p := by simp only [mm]; omega
    exact_mod_cast this
  have hell' : ((ell p (N n) a : ℕ) : ℤ) * p ≤ 2 * (3 * n : ℤ) + p := by
    have : ((ell p (N n) a * p : ℕ) : ℤ) ≤ ((2 * N n + p : ℕ) : ℤ) := by exact_mod_cast hell
    have hN : ((N n : ℕ) : ℤ) = 3 * n := by simp [N]
    push_cast at this; linarith
  have hlZ0 : (0 : ℤ) ≤ ((ell p (N n) a : ℕ) : ℤ) := by positivity
  have hmN' : ((N n / p : ℕ) : ℤ) ≤ n := by exact_mod_cast hmN
  have hp2' : (3 * p : ℤ) ≤ 40 * n := by have := hp2; simp only [K] at this; exact_mod_cast this
  simp only [b]
  generalize ((mm p : ℕ) : ℤ) = mZ at *
  generalize ((ell p (N n) a : ℕ) : ℤ) = lZ at *
  generalize T p n M = T0 at *
  generalize ((N n / p : ℕ) : ℤ) = mN at *
  by_contra hlt
  simp only [not_le] at hlt
  have hmZ0 : 0 ≤ mZ := by omega
  have s1 : mZ * T0 ≤ mZ * (3 * lZ - 1) := mul_le_mul_of_nonneg_left (by omega) hmZ0
  have s3 : (2 * mZ) * lZ ≤ lZ * p := by rw [← e1]; nlinarith
  nlinarith

theorem L_nonneg {a : ℕ} (ha : a ∈ classes p) : 0 ≤ L p n M a := by
  have := b_le_T hM hK hp1 hp2 ha
  simp only [L, eps]; split_ifs <;> omega

/-- `T ≤ 7M + 22`. -/
theorem T_le : T p n M ≤ 7 * M + 22 := by
  have htwo := hyp_two_m hM hK hp1 hp2
  have hMn := hyp_Mn hM hK hp1 hp2
  have hr := rhs_eq (p := p) n M
  have hE := E_nonneg hM hK hp1 hp2
  have h2r := rhs_bound hM hK hp1 hp2
  have hmN : (0 : ℤ) ≤ (N n / p : ℕ) := by positivity
  by_contra hlt
  simp only [not_le] at hlt
  have h1 : (mm p : ℤ) * (7 * M + 23) ≤ rhs p n M := by
    rw [hr]; nlinarith [mm_pos hM hK hp1 hp2]
  have h2 : ((p : ℤ) - 1) * (7 * M + 23) ≤ 2 * rhs p n M := by
    have : ((p : ℤ) - 1) = 2 * (mm p : ℤ) := by
      have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
        have := hyp_p5 hM hK hp1 hp2; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
      rw [← this, ← htwo]; push_cast; ring
    rw [this]; nlinarith
  have hpK : (K n : ℤ) < p * M := by exact_mod_cast hp1
  simp only [K] at hpK
  push_cast at hpK
  nlinarith

theorem mK_le : 2 * T p n M + 2 * (K n / p : ℕ) ≤ 16 * M + 45 := by
  have h1 := T_le hM hK hp1 hp2
  have h2 := hyp_mK hM hK hp1 hp2
  have : ((K n / p : ℕ) : ℤ) ≤ M - 1 := by omega
  omega

/-- `∑_a ϵ_a = E`. -/
theorem sum_eps : ∑ a ∈ classes p, eps p n M a = E p n M := by
  have hE0 := E_nonneg hM hK hp1 hp2
  have hEm := E_lt hM hK hp1 hp2
  simp only [eps, sum_boole]
  have hcard : #(classes p) = mm p := by simp [classes]
  have : {a ∈ classes p | (rank p n a : ℤ) < E p n M} =
      {a ∈ classes p | rk (classes p) (ell p (K n)) a < (E p n M).toNat} := by
    refine filter_congr fun a _ => ?_
    rw [rank_eq_rk]; omega
  rw [this, card_rk_lt (by omega)]
  omega

/-- `L_0 + ∑_a L_a = h`. -/
theorem sum_L : L0 M + ∑ a ∈ classes p, L p n M a = dim n := by
  have hsum := sum_ell_classes (p := p) (hyp_p2 hM hK hp1 hp2) (N n)
  have hcard : #(classes p) = mm p := by simp [classes]
  simp only [L, b, sum_add_distrib, sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]
  rw [sum_eps hM hK hp1 hp2, ← mul_sum]
  have : ∑ a ∈ classes p, (ell p (N n) a : ℤ) = (N n : ℤ) - (N n / p : ℕ) := by
    rw [← Nat.cast_sum, hsum, Nat.cast_sub (Nat.div_le_self _ _)]
  rw [this]
  have hr := rhs_eq (p := p) n M
  simp only [rhs] at hr
  linarith

/-- A class with an extra row has `ℓ_K` at least that of a class without one. -/
theorem ell_le_of_eps {a c : ℕ} (_ha : a ∈ classes p) (hc : c ∈ classes p)
    (hea : eps p n M a = 1) (hec : eps p n M c = 0) : ell p (K n) c ≤ ell p (K n) a := by
  by_contra h
  simp only [not_le] at h
  have hlt : rank p n c < rank p n a := rk_lt_rk (s := classes p) (ℓ := ell p (K n)) hc (Or.inl h)
  simp only [eps] at hea hec
  split_ifs at hea hec with h1 h2
  all_goals omega

/-- `ℓ_K` varies by at most two over the ordinary classes. -/
theorem ell_le_add_two {a c : ℕ} (ha : a ∈ classes p) (hc : c ∈ classes p) :
    ell p (K n) c ≤ ell p (K n) a + 2 := by
  have ha' := mem_Icc.1 ha
  have hc' := mem_Icc.1 hc
  have hp5 := hyp_p5 hM hK hp1 hp2
  have h1 := ell_mul_le (p := p) (A := K n) (a := c) (by omega)
  have h2 := two_mul_div_le_ell (p := p) (A := K n) ha'.1 ha'.2
  have h3 : K n < (K n / p + 1) * p := by
    have := Nat.lt_div_mul_add (a := K n) (show 0 < p by omega)
    linarith
  have : ell p (K n) c < 2 * (K n / p) + 3 := by
    by_contra h
    simp only [not_lt] at h
    have := Nat.mul_le_mul_right p h
    nlinarith
  omega

end Alloc

/-! ### The basis (4.5) and the weights -/

section Basis

/-- The number `L_c` of rows of the class `c` (`L_0 = 4M + 10`). -/
def Lr (p n M c : ℕ) : ℕ := if c = 0 then (L0 M).toNat else (L p n M c).toNat

/-- The exponent vector of the row `(c, i)`:
`E_{c,i} = ∏_{c' ≠ c} (t + c'²)^{L_{c'}} (t + c²)^i`. -/
def ex (p n M c i : ℕ) : ℕ → ℕ := fun c' => if c' = c then i else Lr p n M c'

/-- Twice the weight (4.6), (4.7) of the row `(c, i)`. -/
def wt (p n M c i : ℕ) : ℤ := if c = 0 then w02 p n M i else w2 p n c i

/-- The half-weight of a row with exponent vector `e` at the source `c`: twice the source bound
`E_c - 4` is the sum of the half-weights of the two rows. -/
def halfE (p Nn Kn : ℕ) (e : ℕ → ℕ) (c : ℕ) : ℤ :=
  (if c = 0 then 1 else -4) + 2 * kap c * e c + 6 * kap c * (ell p Nn c : ℤ) -
    kap c * (ell p Kn c : ℤ)

omit hp in
theorem sum_range_shift (f : ℕ → ℤ) (m : ℕ) :
    ∑ c ∈ range m, f (c + 1) = ∑ a ∈ Icc 1 m, f a := by
  refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro c hc; simp only [mem_range, mem_Icc] at hc ⊢; omega
  · intro a ha; simp only [mem_range, mem_Icc] at ha ⊢; omega
  · intro c _; simp
  · intro a ha; simp only [mem_Icc] at ha; omega
  · intro c _; rfl

omit hp in
theorem two_Ecl (Nn Kn : ℕ) (e e' : ℕ → ℕ) (c : ℕ) :
    2 * (Ecl p Nn Kn e e' c - 4) = halfE p Nn Kn e c + halfE p Nn Kn e' c := by
  simp only [Ecl, halfE]
  split_ifs <;> push_cast <;> ring

variable {n M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n)
include hM hK hp1 hp2

theorem Lr_eq {a : ℕ} (ha : a ∈ classes p) : (Lr p n M a : ℤ) = L p n M a := by
  have ha' := mem_Icc.1 ha
  simp only [Lr, show a ≠ 0 by omega, ↓reduceIte]
  exact Int.toNat_of_nonneg (L_nonneg hM hK hp1 hp2 ha)

theorem Lr_zero : (Lr p n M 0 : ℤ) = 4 * M + 10 := by
  simp only [Lr, ↓reduceIte, L0]; omega

/-- `∑_c L_c = h`. -/
theorem sum_Lr : ∑ c ∈ range (mm p + 1), Lr p n M c = dim n := by
  have h := sum_L hM hK hp1 hp2
  have e1 : ∑ c ∈ range (mm p + 1), (Lr p n M c : ℤ) = L0 M + ∑ a ∈ classes p, L p n M a := by
    rw [sum_range_succ', add_comm, sum_range_shift (fun c => (Lr p n M c : ℤ)) (mm p)]
    rw [Lr_zero hM hK hp1 hp2, L0]
    congr 1
    exact sum_congr rfl fun a ha => Lr_eq hM hK hp1 hp2 ha
  have : ((∑ c ∈ range (mm p + 1), Lr p n M c : ℕ) : ℤ) = dim n := by
    push_cast; rw [e1, h]
  exact_mod_cast this

theorem sum_ex {a i : ℕ} (ha : a ≤ mm p) :
    ∑ c ∈ range (mm p + 1), ex p n M a i c + Lr p n M a = dim n + i := by
  have hmem : a ∈ range (mm p + 1) := mem_range.2 (by omega)
  rw [← add_sum_erase _ _ hmem, ← sum_Lr hM hK hp1 hp2, ← add_sum_erase _ _ hmem]
  have : ∑ c ∈ (range (mm p + 1)).erase a, ex p n M a i c =
      ∑ c ∈ (range (mm p + 1)).erase a, Lr p n M c :=
    sum_congr rfl fun c hc => by simp [ex, ne_of_mem_erase hc]
  rw [this]
  simp [ex]
  ring

/-- **The weight check**: every row's half-weight at every source is at least its weight. -/
theorem wt_le_halfE {a i c : ℕ} (ham : a ≤ mm p) (hi : i < Lr p n M a) (hcm : c ≤ mm p) :
    wt p n M a i ≤ halfE p (N n) (K n) (ex p n M a i) c := by
  have hTK := mK_le hM hK hp1 hp2
  have hN0 := ell_eq_zero_class (p := p) (N n)
  have hK0 := ell_eq_zero_class (p := p) (K n)
  have hcl : ∀ c, 1 ≤ c → c ≤ mm p → c ∈ classes p := fun c h1 h2 => mem_Icc.2 ⟨h1, h2⟩
  have hLZ : ∀ c, 1 ≤ c → c ≤ mm p →
      2 * (Lr p n M c : ℤ) + 6 * (ell p (N n) c : ℤ) = 2 * Z p n M c := by
    intro c h1 h2
    rw [Lr_eq hM hK hp1 hp2 (hcl c h1 h2)]
    simp only [L, Z, b]; ring
  have heps : ∀ c, eps p n M c = 0 ∨ eps p n M c = 1 := fun c => by
    simp only [eps]; split_ifs <;> simp
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · -- a zero-class row
    simp only [wt, ↓reduceIte]
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simp only [halfE, ex, kap, ↓reduceIte, hN0, hK0, w02]
      push_cast
      exact (min_le_left _ _).trans (le_of_eq (by ring))
    · have hc := hcl c hc0 hcm
      have hcap : zeroCap2 p n M ≤ 2 * Z p n M c - ell p (K n) c - 4 := by
        simp only [zeroCap2, show (classes p).Nonempty from ⟨c, hc⟩, ↓reduceDIte]
        exact inf'_le _ hc
      have := hLZ c hc0 hcm
      simp only [halfE, ex, kap, show c ≠ 0 by omega, ↓reduceIte, w02]
      push_cast
      refine (min_le_right _ _).trans (hcap.trans (le_of_eq ?_))
      linarith
  · have ha := hcl a ha0 ham
    have hia : (i : ℤ) + 1 ≤ L p n M a := by
      have := Lr_eq hM hK hp1 hp2 ha; omega
    simp only [wt, show a ≠ 0 by omega, ↓reduceIte, w2, b]
    have hLa : L p n M a = T p n M - 3 * ell p (N n) a + eps p n M a := by
      simp only [L, b]
    by_cases hca : c = a
    · subst hca
      simp only [halfE, ex, kap, show c ≠ 0 by omega, ↓reduceIte]
      push_cast; linarith
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simp only [halfE, ex, kap, ↓reduceIte, hN0, hK0, show (0 : ℕ) ≠ a by omega]
      have := Lr_zero hM hK hp1 hp2 (n := n)
      have hea := heps a
      have hl : (0 : ℤ) ≤ ell p (K n) a := by positivity
      have hmN : (0 : ℤ) ≤ ((N n / p : ℕ) : ℤ) := by positivity
      generalize N n / p = mN at *
      generalize K n / p = mK at *
      push_cast
      rcases hea with h | h <;> rw [h] at hLa <;> nlinarith
    · have hc := hcl c hc0 hcm
      have hZ := hLZ c hc0 hcm
      simp only [halfE, ex, kap, show c ≠ 0 by omega, hca, ↓reduceIte]
      push_cast
      have hZc : Z p n M c = T p n M + eps p n M c := rfl
      rcases heps a with h1 | h1 <;> rcases heps c with h2 | h2
      · have := ell_le_add_two hM hK hp1 hp2 ha hc; rw [h1] at hLa; rw [h2] at hZc; push_cast at *
        linarith
      · have := ell_le_add_two hM hK hp1 hp2 ha hc; rw [h1] at hLa; rw [h2] at hZc; push_cast at *
        linarith
      · have := ell_le_of_eps hM hK hp1 hp2 ha hc h1 h2; rw [h1] at hLa; rw [h2] at hZc
        push_cast at *
        linarith
      · have := ell_le_add_two hM hK hp1 hp2 ha hc; rw [h1] at hLa; rw [h2] at hZc; push_cast at *
        linarith

end Basis

/-! ### Proposition 4.1 -/

section Final

omit hp in
theorem natDegree_pull_le (S : Finset ℕ) (A : ℚ[X]) :
    (pull S A).natDegree ≤ 5 + 2 * A.natDegree := by
  rw [pull]
  refine natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans ?_) ?_)
  · simp
  · refine natDegree_comp_le.trans ?_
    have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by simp
    rw [this, mul_comm]

/-- The rows `(c, i)`, `c ≤ m`, `i < L_c`. -/
abbrev Row (p n M : ℕ) := Σ c : Fin (mm p + 1), Fin (Lr p n M c)

variable {n M : ℕ}

/-- The rows in the order of `finSigmaFinEquiv`. -/
def rowEquiv (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) : Row p n M ≃ Fin (dim n) :=
  finSigmaFinEquiv.trans (finCongr h)

/-- The basis (4.5) over `ℤ`. -/
noncomputable def basZ (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) (k : Fin (dim n)) : ℤ[X] :=
  EpolyZ p (ex p n M ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2)

/-- The basis (4.5). -/
noncomputable def bas (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) (k : Fin (dim n)) : ℚ[X] :=
  (basZ h k).map (Int.castRingHom ℚ)

variable (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n) (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n)
include hM hK hp1 hp2

theorem sum_Lr_fin : ∑ c : Fin (mm p + 1), Lr p n M c = dim n := by
  rw [Fin.sum_univ_eq_sum_range (fun c => Lr p n M c)]
  exact sum_Lr hM hK hp1 hp2

theorem natDegree_Epoly_ex {c i : ℕ} (hc : c ≤ mm p) (hi : i < Lr p n M c) :
    (Epoly p (ex p n M c i)).natDegree < dim n := by
  have h1 := natDegree_Epoly_le (p := p) (ex p n M c i)
  have h2 : ∑ c' ∈ range ((p - 1) / 2 + 1), ex p n M c i c' + Lr p n M c = dim n + i :=
    sum_ex hM hK hp1 hp2 (a := c) (i := i) hc
  omega

theorem basZ_natDegree (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) (k : Fin (dim n)) :
    (basZ (p := p) (M := M) h k).natDegree < dim n := by
  have hk := natDegree_Epoly_ex hM hK hp1 hp2 (Nat.lt_succ_iff.1 ((rowEquiv h).symm k).1.2)
    ((rowEquiv h).symm k).2.2
  rw [Epoly, natDegree_map_eq_of_injective (RingHom.injective_int _)] at hk
  exact hk

/-- The classes `c²` are distinct modulo `p`. -/
theorem rho_injective :
    Function.Injective fun c : Fin (mm p + 1) => -(((c : ℕ) : ZMod p) ^ 2) := by
  intro c c' h
  simp only [neg_inj] at h
  have h' : (((c : ℕ) : ℤ) ^ 2 - ((c' : ℕ) : ℤ) ^ 2 : ℤ) = (0 : ZMod p) := by
    push_cast; rw [h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  exact Fin.ext (sq_class_unique (Nat.lt_succ_iff.1 c.2) (Nat.lt_succ_iff.1 c'.2) h')

theorem EpolyZ_ex_map (c : Fin (mm p + 1)) (i : ℕ) :
    (EpolyZ p (ex p n M c i)).map (Int.castRingHom (ZMod p)) =
      crtRow (fun c : Fin (mm p + 1) => -(((c : ℕ) : ZMod p) ^ 2)) (fun c => Lr p n M c) c i := by
  rw [EpolyZ, Polynomial.map_prod, crtRow, Finset.prod_range, ← mul_prod_erase _ _ (mem_univ c),
    mul_comm]
  congr 1
  · refine prod_congr rfl fun c' hc' => ?_
    have hne : (c' : ℕ) ≠ c := fun h' => ne_of_mem_erase hc' (Fin.ext h')
    simp [ex, hne, sub_eq_add_neg]
  · simp [ex, sub_eq_add_neg]

theorem basZ_map (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) (k : Fin (dim n)) :
    (basZ (p := p) (M := M) h k).map (Int.castRingHom (ZMod p)) =
      crtRow (fun c : Fin (mm p + 1) => -(((c : ℕ) : ZMod p) ^ 2)) (fun c => Lr p n M c)
        ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 :=
  EpolyZ_ex_map hM hK hp1 hp2 _ _

theorem basZ_independent (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) :
    LinearIndependent (ZMod p) fun k =>
      (basZ (p := p) (M := M) h k).map (Int.castRingHom (ZMod p)) := by
  simp_rw [basZ_map hM hK hp1 hp2 h]
  exact (crtRow_linearIndependent _ (rho_injective hM hK hp1 hp2) _).comp _
    (rowEquiv h).symm.injective

/-- The weights sum to `γ_p^in`. -/
theorem sum_wt (h : ∑ c : Fin (mm p + 1), Lr p n M c = dim n) :
    ∑ k : Fin (dim n), wt p n M ((rowEquiv h).symm k).1 ((rowEquiv h).symm k).2 =
      gammaIn p n M := by
  rw [Equiv.sum_comp (rowEquiv h).symm (fun x : Row p n M => wt p n M x.1 x.2),
    Fintype.sum_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun c => ∑ i : Fin (Lr p n M c), wt p n M c i) (mm p + 1)]
  rw [sum_congr rfl fun c _ => Fin.sum_univ_eq_sum_range (fun i => wt p n M c i) (Lr p n M c)]
  rw [sum_range_succ', sum_range_shift (fun c => ∑ i ∈ range (Lr p n M c), wt p n M c i),
    gammaIn]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  have : a ≠ 0 := by have := (mem_Icc.1 ha).1; omega
  simp [Lr, wt, this]

/-- The entry of the rows `(c₁, i₁)`, `(c₂, i₂)` has valuation at least the mean of their
weights. -/
theorem entry_bound_inner {c1 i1 c2 i2 : ℕ} (hc1 : c1 ≤ mm p) (hi1 : i1 < Lr p n M c1)
    (hc2 : c2 ≤ mm p) (hi2 : i2 < Lr p n M c2) :
    PolyVGe p ((wt p n M c1 i1 + wt p n M c2 i2 + 1) / 2)
      (muX (D (N n) ^ 6 * Epoly p (ex p n M c1 i1) * Epoly p (ex p n M c2 i2)) (Icc 1 (K n))) := by
  have hp2' := hyp_p2 hM hK hp1 hp2
  have hn := hyp_n hM hK hp1 hp2
  have hsq := hyp_sq hM hK hp1 hp2
  refine PolyVGe_entry hp2' _ _ (Dw := 104 * n + 2) ?_ (by omega) ?_ fun c hc => ?_
  · have h1 := natDegree_Epoly_ex hM hK hp1 hp2 hc1 hi1
    have h2 := natDegree_Epoly_ex hM hK hp1 hp2 hc2 hi2
    have h3a := natDegree_mul_le (p := D (N n) ^ 6 * Epoly p (ex p n M c1 i1))
      (q := Epoly p (ex p n M c2 i2))
    have h3b := natDegree_mul_le (p := D (N n) ^ 6) (q := Epoly p (ex p n M c1 i1))
    have h3c : (D (N n) ^ 6).natDegree ≤ 6 * N n := natDegree_pow_le.trans (by rw [natDegree_D])
    have h4 := natDegree_pull_le (Icc 1 (K n))
      (D (N n) ^ 6 * Epoly p (ex p n M c1 i1) * Epoly p (ex p n M c2 i2))
    generalize (Epoly p (ex p n M c1 i1)).natDegree = d1 at *
    generalize (Epoly p (ex p n M c2 i2)).natDegree = d2 at *
    generalize (D (N n) ^ 6 * Epoly p (ex p n M c1 i1) * Epoly p (ex p n M c2 i2)).natDegree =
      d3 at *
    generalize (D (N n) ^ 6 * Epoly p (ex p n M c1 i1)).natDegree = d4 at *
    generalize (D (N n) ^ 6).natDegree = d5 at *
    simp only [dim, N, K] at h1 h2 h3c h4 ⊢
    omega
  · unfold Close
    simp only [K] at hsq ⊢
    omega
  · have h1 := wt_le_halfE hM hK hp1 hp2 hc1 hi1 hc
    have h2 := wt_le_halfE hM hK hp1 hp2 hc2 hi2 hc
    have h3 := two_Ecl (p := p) (N n) (K n) (ex p n M c1 i1) (ex p n M c2 i2) c
    omega

/-- **Proposition 4.1**: `v_p^G(Δ_K) ≥ γ_p^in`. -/
theorem inner_bound' : PolyVGe p (gammaIn p n M) (Δ n) := by
  have hsum := sum_Lr_fin hM hK hp1 hp2
  obtain ⟨h0, hB⟩ := unimodular_of_independent (p := p) (basZ hsum)
    (basZ_natDegree hM hK hp1 hp2 hsum) (basZ_independent hM hK hp1 hp2 hsum)
  refine PolyVGe_Δ_of_gram (bas hsum) (fun k => ?_) h0 hB ?_
  · rw [bas, natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact basZ_natDegree hM hK hp1 hp2 hsum k
  have hdet := PolyVGe_det (p := p) (gram (D (N n) ^ 6) (Icc 1 (K n)) (bas hsum))
    (fun k => wt p n M ((rowEquiv hsum).symm k).1 ((rowEquiv hsum).symm k).2)
    (fun k l => (wt p n M ((rowEquiv hsum).symm k).1 ((rowEquiv hsum).symm k).2 +
      wt p n M ((rowEquiv hsum).symm l).1 ((rowEquiv hsum).symm l).2 + 1) / 2)
    (fun k l => by omega) fun k l =>
      entry_bound_inner hM hK hp1 hp2 (Nat.lt_succ_iff.1 ((rowEquiv hsum).symm k).1.2)
        ((rowEquiv hsum).symm k).2.2 (Nat.lt_succ_iff.1 ((rowEquiv hsum).symm l).1.2)
        ((rowEquiv hsum).symm l).2.2
  rwa [sum_wt hM hK hp1 hp2 hsum] at hdet

end Final

end Inner

end Zeta5
