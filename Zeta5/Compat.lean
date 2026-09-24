/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Mathlib.Algebra.Polynomial.Div

/-!
# Lemmas missing from the pinned Mathlib

The project is pinned to the Mathlib release used by PrimeNumberTheoremAnd (`v4.32.2`). A few lemmas
used here were added to Mathlib later; they are proved here under the same names. Remove them when
the pin moves past their addition.
-/

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

theorem add_divByMonic (p₁ p₂ q : R[X]) : (p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q := by
  by_cases hq : q.Monic
  · nontriviality R
    exact (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) (p₁ %ₘ q + p₂ %ₘ q) hq
      ⟨by rw [mul_add, add_add_add_comm, modByMonic_add_div, modByMonic_add_div],
        (degree_add_le _ _).trans_lt
          (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).1
  · simp [divByMonic_eq_of_not_monic _ hq]

theorem smul_divByMonic (c : R) (p q : R[X]) : (c • p) /ₘ q = c • (p /ₘ q) := by
  by_cases hq : q.Monic
  · nontriviality R
    refine (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
      ⟨?_, (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).1
    rw [mul_smul_comm, ← smul_add, modByMonic_add_div]
  · simp [divByMonic_eq_of_not_monic _ hq]

end Polynomial
