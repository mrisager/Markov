import Markov.CanonicalTrace

/-! A local strict triangle inequality for the candidate trace lengths on
Farey triangles. This is only the adjacent-direction inequality; it is not
an assertion of the global triangle inequality or existence of a norm. -/

noncomputable section

namespace Markov

/-- The trace associated with a sum of half-lengths has Fricke polynomial 4. -/
theorem cosh_sum_fricke_polynomial (x y : ℝ) :
    (2 * Real.cosh x) ^ 2 + (2 * Real.cosh y) ^ 2 +
      (2 * Real.cosh (x + y)) ^ 2 -
      (2 * Real.cosh x) * (2 * Real.cosh y) * (2 * Real.cosh (x + y)) = 4 := by
  rw [Real.cosh_add]
  linear_combination
    4 * (1 - Real.cosh y ^ 2) * Real.cosh_sq_sub_sinh_sq x -
      4 * Real.sinh x ^ 2 * Real.cosh_sq_sub_sinh_sq y

/-- The Fricke root is strictly below the trace of the sum of lengths. -/
theorem fricke_trace_lt_cosh_sum (t b c : ℝ)
    (ht : 2 ≤ t) (hb : 2 ≤ b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    c < 2 * Real.cosh (Real.arcosh (t / 2) + Real.arcosh (b / 2)) := by
  let x := Real.arcosh (t / 2)
  let y := Real.arcosh (b / 2)
  let C := 2 * Real.cosh (x + y)
  have hx : 0 ≤ x := Real.arcosh_nonneg (by linarith)
  have hy : 0 ≤ y := Real.arcosh_nonneg (by linarith)
  have htx : 2 * Real.cosh x = t := by
    dsimp [x]
    rw [Real.cosh_arcosh (by linarith)]
    ring
  have hby : 2 * Real.cosh y = b := by
    dsimp [y]
    rw [Real.cosh_arcosh (by linarith)]
    ring
  have hpoly : t ^ 2 + b ^ 2 + C ^ 2 - t * b * C = 4 := by
    simpa only [htx, hby] using cosh_sum_fricke_polynomial x y
  have hlow : t * b ≤ 2 * C := by
    have hs := mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.sinh_nonneg_iff.mpr hy)
    dsimp [C]
    rw [Real.cosh_add]
    nlinarith [htx, hby]
  change c < C
  by_contra h
  have hc : C ≤ c := le_of_not_gt h
  have hdiff : 0 ≤ (c - C) * (c + C - t * b) :=
    mul_nonneg (sub_nonneg.mpr hc) (by linarith)
  nlinarith

/-- Local strict triangle for three real traces satisfying Fricke. -/
theorem fricke_trace_length_strict_triangle (t b c : ℝ)
    (ht : 2 ≤ t) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    2 * Real.arcosh (c / 2) < 2 * Real.arcosh (t / 2) + 2 * Real.arcosh (b / 2) := by
  have hbound := fricke_trace_lt_cosh_sum t b c ht hb hf
  have hx : 0 ≤ Real.arcosh (t / 2) := Real.arcosh_nonneg (by linarith)
  have hy : 0 ≤ Real.arcosh (b / 2) := Real.arcosh_nonneg (by linarith)
  have hi := (Real.arcosh_lt_arcosh (show 0 < c / 2 by linarith)
    (Real.cosh_pos (Real.arcosh (t / 2) + Real.arcosh (b / 2)))).mpr
      (show c / 2 < Real.cosh (Real.arcosh (t / 2) + Real.arcosh (b / 2)) by linarith)
  rw [Real.arcosh_cosh (add_nonneg hx hy)] at hi
  linarith

/-- The numerical primitive trace lengths satisfy a strict triangle
inequality at each positive Farey edge. -/
theorem FareyHolonomy.canonicalLength_strict_triangle
    {u v : ℤ × ℤ} {M N : IntMatrixTwo} (h : FareyHolonomy u v M N)
    (hu : NonnegativePrimitiveDirection u) (hv : NonnegativePrimitiveDirection v)
    (hs : NonnegativePrimitiveDirection (u + v)) :
    primitiveFareyLength (u + v) hs < primitiveFareyLength u hu + primitiveFareyLength v hv := by
  have htu : (3 : ℝ) ≤ primitiveFareyTrace u hu := by
    exact_mod_cast primitiveFareyTrace_ge_three u hu
  have htv : (3 : ℝ) ≤ primitiveFareyTrace v hv := by
    exact_mod_cast primitiveFareyTrace_ge_three v hv
  have hts : (3 : ℝ) ≤ primitiveFareyTrace (u + v) hs := by
    exact_mod_cast primitiveFareyTrace_ge_three (u + v) hs
  have hf : (primitiveFareyTrace u hu : ℝ) ^ 2 + (primitiveFareyTrace v hv : ℝ) ^ 2 +
      (primitiveFareyTrace (u + v) hs : ℝ) ^ 2 =
      (primitiveFareyTrace u hu : ℝ) * primitiveFareyTrace v hv * primitiveFareyTrace (u + v) hs := by
    exact_mod_cast h.canonicalTrace_fricke hu hv hs
  exact fricke_trace_length_strict_triangle _ _ _ (by linarith) (by linarith) (by linarith) hf

end Markov
