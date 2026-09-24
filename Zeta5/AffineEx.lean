/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-!
# Piecewise affine functions, checked by evaluation

The functions `R(x)` of §5 are built from `x` by affine operations, products, floors, minima,
maxima and comparisons, and they are affine between consecutive points of an explicit finite set
(Appendix B). To integrate them exactly we represent them as expressions `Zeta5.Ex` and evaluate
an expression on an open interval `(l, r)` to an affine form `A x + B` (`Zeta5.Ex.aff`). The
evaluation fails unless every floor, minimum, maximum and comparison is constant on `(l, r)`;
this is decided from the values of the affine forms of the arguments at `l` and `r`.
`Zeta5.Ex.aff_sound` says that a successful evaluation is correct at every point of `(l, r)`.

`Zeta5.Ex.run` evaluates an expression on the consecutive intervals of a list of points.
-/

namespace Zeta5

/-- Expressions in one rational variable. `ite a b t e` is `if a < b then t else e`. -/
inductive Ex : Type
  | var : Ex
  | cst : ℚ → Ex
  | add : Ex → Ex → Ex
  | sub : Ex → Ex → Ex
  | mul : Ex → Ex → Ex
  | floor : Ex → Ex
  | min : Ex → Ex → Ex
  | max : Ex → Ex → Ex
  | ite : Ex → Ex → Ex → Ex → Ex

namespace Ex

instance : Add Ex := ⟨add⟩
instance : Sub Ex := ⟨sub⟩
instance : Mul Ex := ⟨mul⟩

/-- The value of an expression at `x`. -/
def eval (x : ℚ) : Ex → ℚ
  | var => x
  | cst c => c
  | add a b => a.eval x + b.eval x
  | sub a b => a.eval x - b.eval x
  | mul a b => a.eval x * b.eval x
  | floor a => ⌊a.eval x⌋
  | min a b => Min.min (a.eval x) (b.eval x)
  | max a b => Max.max (a.eval x) (b.eval x)
  | ite a b t e => if a.eval x < b.eval x then t.eval x else e.eval x

@[simp] theorem eval_var (x : ℚ) : var.eval x = x := rfl
@[simp] theorem eval_cst (x c : ℚ) : (cst c).eval x = c := rfl
@[simp] theorem eval_add (x : ℚ) (a b : Ex) : (a + b).eval x = a.eval x + b.eval x := rfl
@[simp] theorem eval_sub (x : ℚ) (a b : Ex) : (a - b).eval x = a.eval x - b.eval x := rfl
@[simp] theorem eval_mul (x : ℚ) (a b : Ex) : (a * b).eval x = a.eval x * b.eval x := rfl
@[simp] theorem eval_floor (x : ℚ) (a : Ex) : (floor a).eval x = ⌊a.eval x⌋ := rfl
@[simp] theorem eval_min (x : ℚ) (a b : Ex) : (min a b).eval x = Min.min (a.eval x) (b.eval x) :=
  rfl
@[simp] theorem eval_max (x : ℚ) (a b : Ex) : (max a b).eval x = Max.max (a.eval x) (b.eval x) :=
  rfl
@[simp] theorem eval_ite (x : ℚ) (a b t e : Ex) :
    (ite a b t e).eval x = if a.eval x < b.eval x then t.eval x else e.eval x := rfl

/-- The value `A y + B` of the affine form `f = (A, B)` at `y`. -/
def at' (f : ℚ × ℚ) (y : ℚ) : ℚ := f.1 * y + f.2

/-- The affine form of an expression on the open interval `(l, r)`, if every floor, minimum,
maximum and comparison in it is constant there. -/
def aff (l r : ℚ) : Ex → Option (ℚ × ℚ)
  | var => some (1, 0)
  | cst c => some (0, c)
  | add a b => do
    let f ← a.aff l r
    let g ← b.aff l r
    pure (f.1 + g.1, f.2 + g.2)
  | sub a b => do
    let f ← a.aff l r
    let g ← b.aff l r
    pure (f.1 - g.1, f.2 - g.2)
  | mul a b => do
    let f ← a.aff l r
    let g ← b.aff l r
    if f.1 = 0 then pure (f.2 * g.1, f.2 * g.2)
    else if g.1 = 0 then pure (f.1 * g.2, f.2 * g.2)
    else none
  | floor a => do
    let f ← a.aff l r
    let lo := Min.min (at' f l) (at' f r)
    if Max.max (at' f l) (at' f r) ≤ ⌊lo⌋ + 1 then pure (0, ⌊lo⌋) else none
  | min a b => do
    let f ← a.aff l r
    let g ← b.aff l r
    if at' f l ≤ at' g l ∧ at' f r ≤ at' g r then pure f
    else if at' g l ≤ at' f l ∧ at' g r ≤ at' f r then pure g
    else none
  | max a b => do
    let f ← a.aff l r
    let g ← b.aff l r
    if at' f l ≤ at' g l ∧ at' f r ≤ at' g r then pure g
    else if at' g l ≤ at' f l ∧ at' g r ≤ at' f r then pure f
    else none
  | ite a b t e => do
    let f ← a.aff l r
    let g ← b.aff l r
    if at' g l ≤ at' f l ∧ at' g r ≤ at' f r then e.aff l r
    else if at' f l ≤ at' g l ∧ at' f r ≤ at' g r then t.aff l r
    else none

theorem at'_sub (f g : ℚ × ℚ) (y : ℚ) : at' (f.1 - g.1, f.2 - g.2) y = at' f y - at' g y := by
  simp only [at']; ring

section Sound

variable {l r x : ℚ} (hl : l < x) (hr : x < r)
include hl hr

/-- An affine function that is `≤ 0` at both ends of `[l, r]` is `≤ 0` inside. -/
theorem at'_nonpos {f : ℚ × ℚ} (h1 : at' f l ≤ 0) (h2 : at' f r ≤ 0) : at' f x ≤ 0 := by
  have e : at' f x * (r - l) = at' f l * (r - x) + at' f r * (x - l) := by
    simp only [at']; ring
  have : at' f x * (r - l) ≤ 0 := by
    rw [e]; nlinarith
  by_contra h
  have h := lt_of_not_ge h
  nlinarith

/-- An affine function that is `≤ 0` at both ends of `[l, r]` and not `≥ 0` at both is `< 0`
inside. -/
theorem at'_neg {f : ℚ × ℚ} (h1 : at' f l ≤ 0) (h2 : at' f r ≤ 0)
    (h3 : ¬(0 ≤ at' f l ∧ 0 ≤ at' f r)) : at' f x < 0 := by
  have e : at' f x * (r - l) = at' f l * (r - x) + at' f r * (x - l) := by
    simp only [at']; ring
  have : at' f x * (r - l) < 0 := by
    rw [e]
    rcases not_and_or.1 h3 with h | h
    · have h := lt_of_not_ge h; nlinarith
    · have h := lt_of_not_ge h; nlinarith
  by_contra h
  have h := le_of_not_gt h
  nlinarith

theorem le_of_ends {f g : ℚ × ℚ} (h1 : at' f l ≤ at' g l) (h2 : at' f r ≤ at' g r) :
    at' f x ≤ at' g x := by
  have := at'_nonpos hl hr (f := (f.1 - g.1, f.2 - g.2)) (by rw [at'_sub]; linarith)
    (by rw [at'_sub]; linarith)
  rw [at'_sub] at this
  linarith

theorem lt_of_ends {f g : ℚ × ℚ} (h1 : at' f l ≤ at' g l) (h2 : at' f r ≤ at' g r)
    (h3 : ¬(at' g l ≤ at' f l ∧ at' g r ≤ at' f r)) : at' f x < at' g x := by
  have := at'_neg hl hr (f := (f.1 - g.1, f.2 - g.2)) (by rw [at'_sub]; linarith)
    (by rw [at'_sub]; linarith)
    (by rw [at'_sub, at'_sub]; intro h; exact h3 ⟨by linarith, by linarith⟩)
  rw [at'_sub] at this
  linarith

/-- The floor of an affine function is constant on `(l, r)` if no integer lies strictly between
its values at `l` and `r`. -/
theorem floor_at' {f : ℚ × ℚ}
    (h : Max.max (at' f l) (at' f r) ≤ ⌊Min.min (at' f l) (at' f r)⌋ + 1) :
    ⌊at' f x⌋ = ⌊Min.min (at' f l) (at' f r)⌋ := by
  set lo := Min.min (at' f l) (at' f r)
  have hlo : lo ≤ at' f x := by
    rcases min_choice (at' f l) (at' f r) with h' | h'
    · have := le_of_ends hl hr (f := (0, lo)) (g := f) (by simp [at', lo]) (by simp [at', lo])
      simpa [at'] using this
    · have := le_of_ends hl hr (f := (0, lo)) (g := f) (by simp [at', lo]) (by simp [at', lo])
      simpa [at'] using this
  rw [Int.floor_eq_iff]
  refine ⟨(Int.floor_le lo).trans hlo, ?_⟩
  by_cases hA : f.1 = 0
  · have : at' f x = lo := by
      simp only [lo, at', hA, zero_mul, zero_add, min_self]
    rw [this]
    exact Int.lt_floor_add_one lo
  · have hx : at' f x < Max.max (at' f l) (at' f r) := by
      rcases lt_or_gt_of_ne hA with hA | hA
      · have : at' f x < at' f l := by simp only [at']; nlinarith
        exact lt_of_lt_of_le this (le_max_left _ _)
      · have : at' f x < at' f r := by simp only [at']; nlinarith
        exact lt_of_lt_of_le this (le_max_right _ _)
    linarith

/-- A successful affine evaluation on `(l, r)` is correct at every `x ∈ (l, r)`. -/
theorem aff_sound : ∀ (e : Ex) (f : ℚ × ℚ), e.aff l r = some f → e.eval x = at' f x
  | var, f, h => by
    simp only [aff, Option.some.injEq] at h
    subst h; simp [at']
  | cst c, f, h => by
    simp only [aff, Option.some.injEq] at h
    subst h; simp [at', eval]
  | add a b, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨fa, ha, fb, hb, rfl⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb, at']
    ring
  | sub a b, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨fa, ha, fb, hb, rfl⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb, at']
    ring
  | mul a b, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨fa, ha, fb, hb, h⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb]
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h; subst h
      simp only [at', h1]; ring
    · simp only [Option.some.injEq] at h; subst h
      simp only [at', h2]; ring
  | floor a, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨fa, ha, h⟩ := h
    split_ifs at h with h1
    simp only [Option.some.injEq] at h; subst h
    rw [eval, aff_sound a fa ha, floor_at' hl hr h1]
    simp only [at', zero_mul, zero_add]
  | min a b, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨fa, ha, fb, hb, h⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb]
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h; subst h
      exact min_eq_left (le_of_ends hl hr h1.1 h1.2)
    · simp only [Option.some.injEq] at h; subst h
      exact min_eq_right (le_of_ends hl hr h2.1 h2.2)
  | max a b, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨fa, ha, fb, hb, h⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb]
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h; subst h
      exact max_eq_right (le_of_ends hl hr h1.1 h1.2)
    · simp only [Option.some.injEq] at h; subst h
      exact max_eq_left (le_of_ends hl hr h2.1 h2.2)
  | ite a b t e, f, h => by
    simp only [aff, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨fa, ha, fb, hb, h⟩ := h
    simp only [eval, aff_sound a fa ha, aff_sound b fb hb]
    split_ifs at h with h1 h2
    · rw [if_neg (not_lt.2 (le_of_ends hl hr h1.1 h1.2))]
      exact aff_sound e f h
    · rw [if_pos (lt_of_ends hl hr h2.1 h2.2 h1)]
      exact aff_sound t f h

end Sound

/-- The affine forms of `e` on the consecutive intervals of the points `l, bs`, which must be
increasing. -/
def run (e : Ex) : ℚ → List ℚ → Option (List (ℚ × ℚ × (ℚ × ℚ)))
  | _, [] => some []
  | l, r :: bs =>
    if l < r then do
      let f ← e.aff l r
      let ps ← run e r bs
      pure ((l, r, f) :: ps)
    else none

/-- `∫_l^r (A x + B) x⁻³ dx`. -/
def pieceInt (l r : ℚ) (f : ℚ × ℚ) : ℚ := f.1 * (1 / l - 1 / r) + f.2 / 2 * (1 / l ^ 2 - 1 / r ^ 2)

/-- `∫ e(x) x⁻³ dx` over the intervals of the points `l, bs`, if `e` is affine on each. -/
def runInt (e : Ex) (l : ℚ) (bs : List ℚ) : Option ℚ :=
  (run e l bs).map fun ps => (ps.map fun q => pieceInt q.1 q.2.1 q.2.2).sum

/-- The check run by the kernel: `e` is affine on each interval and `∫ e x⁻³ ≤ V`. -/
def intLe (e : Ex) (l : ℚ) (bs : List ℚ) (V : ℚ) : Bool :=
  match runInt e l bs with
  | some v => decide (v ≤ V)
  | none => false

end Ex

end Zeta5
