/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.BigPrimes
import Zeta5.InnerRange
import Zeta5.OuterRange
import Zeta5.SmallPrimeBound

/-!
# The local bounds of §3 and §4 (statements)

* `Zeta5.smallPrime_bound`: (3.12), `v_p^G(F_K) ≥ -6h ⌊log_p(5K)⌋ - h v_p(24)` for every prime `p`.
* `Zeta5.inner_bound`: Proposition 4.1, `v_p^G(Δ_K) ≥ γ_p^in` in the inner range.
* `Zeta5.outer_bound`: Proposition 4.3, `v_p^G(Δ_K) ≥ γ_p^out` in the outer range.
* `Zeta5.big_bound`: Proposition 4.3, `v_p^G(Δ_K) ≥ 0` for `p > K`.
-/

namespace Zeta5

/-- (3.12). -/
theorem smallPrime_bound (p n : ℕ) [Fact p.Prime] :
    PolyVGe p (-6 * dim n * Nat.log p (5 * K n) - dim n * padicValNat p 24) (F n) :=
  smallPrime_bound' n

/-- Proposition 4.1. -/
theorem inner_bound {p n M : ℕ} [Fact p.Prime] (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (hp1 : K n < p * M) (hp2 : 3 * p ≤ K n) : PolyVGe p (Inner.gammaIn p n M) (Δ n) :=
  Inner.inner_bound' hM hK hp1 hp2

/-- Proposition 4.3, first part. -/
theorem outer_bound {p n M : ℕ} [Fact p.Prime] (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ K n)
    (hp1 : K n < 3 * p) (hp2 : p ≤ K n) : PolyVGe p (Outer.gammaOut p n) (Δ n) :=
  Outer.outer_bound' hM hK hp1 hp2

/-- Proposition 4.3, second part. -/
theorem big_bound {p n : ℕ} [Fact p.Prime] (hp : K n < p) : PolyVGe p 0 (Δ n) :=
  big_bound' hp

end Zeta5
