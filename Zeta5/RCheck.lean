/-
Copyright (c) 2026 Jihyeon Kim. All rights reserved.
Released under Apache 2.0 or MIT license, at your option, as described in the file COPYRIGHT.
Authors: Jihyeon Kim
-/
import Zeta5.Constants
import Zeta5.RData
import Zeta5.RFun
import Zeta5.RIntegral

/-!
# The exact integral of `R(x) x⁻³` (Appendix B)

The kernel checks, chunk by chunk, that the limiting exponent `Zeta5.eR` is affine on every
interval between consecutive points of `Zeta5/RData.lean`, and that `∫ R(x) x⁻³ dx` over each
chunk is at most the stated bound (`decide +kernel` on `Zeta5.Ex.intLe`). Together:

`∫_{20/37}^{200} R(x) x⁻³ dx ≤ A_200 - 6λ/200` (`Zeta5.rBounds_sum`). Here `∫_{20/37}^3 = I_out`
is (5.10), and `∫_3^{200}` is computed exactly instead of through the tail bounds (5.15)–(5.17);
the exact value is smaller than the paper's bound by about `0.004`.
-/

namespace Zeta5

namespace Ex

/-- A chunked check: `e` is affine on the intervals of each chunk, whose integral is at most the
given bound. -/
def chunksOK (e : Ex) : ℚ → List (List ℚ × ℚ) → Bool
  | _, [] => true
  | l, (c, V) :: cs => e.intLe l c V && chunksOK e (c.getLastD l) cs

theorem run_of_chunksOK (e : Ex) : ∀ (l : ℚ) (cs : List (List ℚ × ℚ)), e.chunksOK l cs = true →
    ∃ ps, e.run l (cs.map Prod.fst).flatten = some ps ∧
      (ps.map fun q => pieceInt q.1 q.2.1 q.2.2).sum ≤ (cs.map Prod.snd).sum := by
  intro l cs
  induction cs generalizing l with
  | nil => intro _; exact ⟨[], run_nil e l, by simp⟩
  | cons cV cs ih =>
    obtain ⟨c, V⟩ := cV
    intro h
    simp only [chunksOK, Bool.and_eq_true] at h
    obtain ⟨ps₁, h1, hs1⟩ := exists_of_intLe h.1
    obtain ⟨ps₂, h2, hs2⟩ := ih _ h.2
    refine ⟨ps₁ ++ ps₂, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons]
      exact run_append e l c _ ps₁ ps₂ h1 h2
    · simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      linarith

end Ex

theorem rChunk0_ok : eR.intLe rStart0 (toQ rChunk0) rBound0 = true := by decide +kernel

theorem rChunk1_ok : eR.intLe rStart1 (toQ rChunk1) rBound1 = true := by decide +kernel

theorem rChunk2_ok : eR.intLe rStart2 (toQ rChunk2) rBound2 = true := by decide +kernel

theorem rChunk3_ok : eR.intLe rStart3 (toQ rChunk3) rBound3 = true := by decide +kernel

theorem rChunk4_ok : eR.intLe rStart4 (toQ rChunk4) rBound4 = true := by decide +kernel

theorem rChunk5_ok : eR.intLe rStart5 (toQ rChunk5) rBound5 = true := by decide +kernel

theorem rChunk6_ok : eR.intLe rStart6 (toQ rChunk6) rBound6 = true := by decide +kernel

theorem rChunk7_ok : eR.intLe rStart7 (toQ rChunk7) rBound7 = true := by decide +kernel

theorem rChunk8_ok : eR.intLe rStart8 (toQ rChunk8) rBound8 = true := by decide +kernel

theorem rChunk9_ok : eR.intLe rStart9 (toQ rChunk9) rBound9 = true := by decide +kernel

theorem rChunk0_last : (toQ rChunk0).getLastD rStart0 = rStart1 := by decide +kernel

theorem rChunk1_last : (toQ rChunk1).getLastD rStart1 = rStart2 := by decide +kernel

theorem rChunk2_last : (toQ rChunk2).getLastD rStart2 = rStart3 := by decide +kernel

theorem rChunk3_last : (toQ rChunk3).getLastD rStart3 = rStart4 := by decide +kernel

theorem rChunk4_last : (toQ rChunk4).getLastD rStart4 = rStart5 := by decide +kernel

theorem rChunk5_last : (toQ rChunk5).getLastD rStart5 = rStart6 := by decide +kernel

theorem rChunk6_last : (toQ rChunk6).getLastD rStart6 = rStart7 := by decide +kernel

theorem rChunk7_last : (toQ rChunk7).getLastD rStart7 = rStart8 := by decide +kernel

theorem rChunk8_last : (toQ rChunk8).getLastD rStart8 = rStart9 := by decide +kernel

/-- The chunks with their bounds. -/
def rChunks : List (List ℚ × ℚ) :=
  [(toQ rChunk0, rBound0), (toQ rChunk1, rBound1), (toQ rChunk2, rBound2), (toQ rChunk3, rBound3),
    (toQ rChunk4, rBound4), (toQ rChunk5, rBound5), (toQ rChunk6, rBound6), (toQ rChunk7, rBound7),
    (toQ rChunk8, rBound8), (toQ rChunk9, rBound9)]

theorem rStart0_eq : rStart0 = 20 / 37 := rfl

theorem rChunks_ok : eR.chunksOK (20 / 37) rChunks = true := by
  rw [← rStart0_eq]
  simp only [rChunks, Ex.chunksOK, rChunk0_ok, rChunk1_ok, rChunk2_ok, rChunk3_ok, rChunk4_ok,
    rChunk5_ok, rChunk6_ok, rChunk7_ok, rChunk8_ok, rChunk9_ok, rChunk0_last, rChunk1_last,
    rChunk2_last, rChunk3_last, rChunk4_last, rChunk5_last, rChunk6_last, rChunk7_last,
    rChunk8_last, Bool.and_true]

/-- All the points after `20/37`. -/
def rPoints : List ℚ := (rChunks.map Prod.fst).flatten

theorem rPoints_last : rPoints.getLastD (20 / 37) = 200 := by decide +kernel

theorem rBounds_sum : (rChunks.map Prod.snd).sum + 6 * lambda / 200 ≤ AM 200 := by
  norm_num [rChunks, rBound0, rBound1, rBound2, rBound3, rBound4, rBound5, rBound6, rBound7,
    rBound8, rBound9, AM_200, lambda]

end Zeta5
