/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.AffineEx
import Zeta5.PrimeAsymp

/-!
# Prime sums of piecewise affine functions

If an expression `e` is affine on the consecutive intervals of `l, bs` (`Zeta5.Ex.run`), then
`K⁻² ∑_{l ≤ K/p < last} p e(K/p) log p` tends to the exact integral `∫ e(x) x⁻³ dx`: on each open
interval the summand is `(A K + B p) log p` (`Zeta5.tendsto_psum_affine`), and the primes with
`K/p` at an endpoint contribute `o(K²)` (`Zeta5.tendsto_point`).
-/

open Filter Finset Real
open scoped Topology

namespace Zeta5

namespace Ex

theorem run_nil (e : Ex) (l : ℚ) : e.run l [] = some [] := by
  simp only [run]

theorem run_cons_eq_some {e : Ex} {l r : ℚ} {bs : List ℚ} {ps : List (ℚ × ℚ × (ℚ × ℚ))} :
    e.run l (r :: bs) = some ps ↔ ∃ f ps', l < r ∧ e.aff l r = some f ∧ e.run r bs = some ps' ∧
      ps = (l, r, f) :: ps' := by
  simp only [run]
  split_ifs with h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    constructor
    · rintro ⟨f, hf, ps', hps', rfl⟩
      exact ⟨f, ps', h, hf, hps', rfl⟩
    · rintro ⟨f, ps', -, hf, hps', rfl⟩
      exact ⟨f, hf, ps', hps', rfl⟩
  · simp only [false_iff, not_exists, not_and]
    intro f ps' h'
    exact absurd h' h

theorem run_append (e : Ex) :
    ∀ (l : ℚ) (bs₁ bs₂ : List ℚ) (ps₁ ps₂ : List (ℚ × ℚ × (ℚ × ℚ))), e.run l bs₁ = some ps₁ →
      e.run (bs₁.getLastD l) bs₂ = some ps₂ → e.run l (bs₁ ++ bs₂) = some (ps₁ ++ ps₂) := by
  intro l bs₁
  induction bs₁ generalizing l with
  | nil =>
    intro bs₂ ps₁ ps₂ h1 h2
    rw [run_nil, Option.some.injEq] at h1
    subst h1
    simpa using h2
  | cons r bs ih =>
    intro bs₂ ps₁ ps₂ h1 h2
    obtain ⟨f, ps', hlr, hf, hps', rfl⟩ := run_cons_eq_some.1 h1
    rw [List.getLastD_cons] at h2
    rw [List.cons_append, List.cons_append]
    exact run_cons_eq_some.2 ⟨f, ps' ++ ps₂, hlr, hf, ih r bs₂ ps' ps₂ hps' h2, rfl⟩

theorem le_getLastD_of_run (e : Ex) :
    ∀ (l : ℚ) (bs : List ℚ) (ps : List (ℚ × ℚ × (ℚ × ℚ))), e.run l bs = some ps →
      l ≤ bs.getLastD l := by
  intro l bs
  induction bs generalizing l with
  | nil => intro _ _; exact le_refl l
  | cons r bs ih =>
    intro ps h
    obtain ⟨f, ps', hlr, -, hps', -⟩ := run_cons_eq_some.1 h
    rw [List.getLastD_cons]
    exact hlr.le.trans (ih r ps' hps')

theorem exists_of_intLe {e : Ex} {l : ℚ} {bs : List ℚ} {V : ℚ} (h : e.intLe l bs V = true) :
    ∃ ps, e.run l bs = some ps ∧ (ps.map fun q => pieceInt q.1 q.2.1 q.2.2).sum ≤ V := by
  unfold intLe runInt at h
  cases hr : e.run l bs with
  | none => simp [hr] at h
  | some ps =>
    simp only [hr, Option.map_some, decide_eq_true_eq] at h
    exact ⟨ps, rfl, h⟩

end Ex

/-- `K⁻² ∑_{l ≤ K/p < last} p e(K/p) log p → ∫_l^{last} e(x) x⁻³ dx`. -/
theorem tendsto_psum_run (e : Ex) {l : ℚ} (hl : 20 / 37 ≤ l) {bs : List ℚ}
    {ps : List (ℚ × ℚ × (ℚ × ℚ))} (h : e.run l bs = some ps) :
    Tendsto (fun n => psum n l (bs.getLastD l)
        (fun p => p * (e.eval ((K n : ℚ) / p) : ℝ) * log p) / (K n : ℝ) ^ 2) atTop
      (𝓝 (((ps.map fun q => Ex.pieceInt q.1 q.2.1 q.2.2).sum : ℚ) : ℝ)) := by
  induction bs generalizing l ps with
  | nil =>
    rw [Ex.run_nil, Option.some.injEq] at h
    subst h
    simp [psum_self]
  | cons r bs ih =>
    obtain ⟨f, ps', hlr, hf, hps', rfl⟩ := Ex.run_cons_eq_some.1 h
    have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
    have hr : 20 / 37 ≤ r := hl.trans hlr.le
    have hlast : r ≤ bs.getLastD r := Ex.le_getLastD_of_run e r bs ps' hps'
    rw [List.getLastD_cons]
    set c : ℝ := ((e.eval l - Ex.at' f l : ℚ) : ℝ)
    have hpiece : ∀ n, psum n l r (fun p => p * (e.eval ((K n : ℚ) / p) : ℝ) * log p) =
        psum n l r (fun p => ((f.1 : ℝ) * K n + (f.2 : ℝ) * p) * log p) +
          ∑ p ∈ Ps n, if (K n : ℚ) / p = l then c * p * log p else 0 := by
      intro n
      rw [psum, psum, ← sum_add_distrib]
      refine sum_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_Ps.1 hp).2.pos
      by_cases h1 : l ≤ (K n : ℚ) / p ∧ (K n : ℚ) / p < r
      · rw [if_pos h1, if_pos h1]
        rcases eq_or_lt_of_le h1.1 with h2 | h2
        · rw [if_pos h2.symm, ← h2]
          have hK : (K n : ℝ) = (l : ℝ) * p := by
            have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (mem_Ps.1 hp).2.ne_zero
            have : (K n : ℚ) = l * p := by rw [h2]; field_simp
            exact_mod_cast this
          simp only [c, Ex.at']
          push_cast
          rw [hK]
          ring
        · rw [if_neg h2.ne', add_zero, Ex.aff_sound h2 h1.2 e f hf]
          simp only [Ex.at']
          push_cast
          field_simp
      · rw [if_neg h1, if_neg h1, zero_add, if_neg]
        intro h2
        exact h1 ⟨h2.symm.le, h2 ▸ hlr⟩
    have e1 : ∀ n, psum n l (bs.getLastD r)
        (fun p => p * (e.eval ((K n : ℚ) / p) : ℝ) * log p) / (K n : ℝ) ^ 2 =
        psum n l r (fun p => ((f.1 : ℝ) * K n + (f.2 : ℝ) * p) * log p) / (K n : ℝ) ^ 2 +
          (∑ p ∈ Ps n, if (K n : ℚ) / p = l then c * p * log p else 0) / (K n : ℝ) ^ 2 +
          psum n r (bs.getLastD r) (fun p => p * (e.eval ((K n : ℚ) / p) : ℝ) * log p) /
            (K n : ℝ) ^ 2 := by
      intro n
      rw [psum_add hlr.le hlast, hpiece]
      ring
    have key := ((tendsto_psum_affine hl hlr (f.1 : ℝ) (f.2 : ℝ)).add
      (tendsto_point hl0 c)).add (ih hr hps')
    refine Tendsto.congr (fun n => (e1 n).symm) ?_
    convert key using 2
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Ex.pieceInt]
    push_cast
    ring

end Zeta5
