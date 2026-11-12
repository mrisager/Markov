import Markov.SeparationBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The logarithmic and square-root estimates concluding the size argument
in Lemma 6. Geometric determinant and arc estimates remain explicit inputs;
this module proves their real-analytic consequences. -/

namespace Markov

/-- Compare the arithmetic lower bound with the geometric upper bound.
The two nonnegative constants only need positivity when this is divided by c. -/
theorem unresolved_log_height_bound (M D A L c H z : ℝ)
    (hD : 1 ≤ D) (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hlower : Real.exp (-M * D * A ^ 2) ≤ z)
    (hupper : z ≤ L * D * Real.exp (-c * H)) :
    c * H ≤ (M + Real.log L + 1) * D * A ^ 2 := by
  have hDp : 0 < D := by linarith
  have hLp : 0 < L := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (-M * D * A ^ 2)) (hlower.trans hupper)
  rw [Real.log_exp, Real.log_mul (mul_ne_zero hLp.ne' hDp.ne') (Real.exp_ne_zero _),
    Real.log_mul hLp.ne' hDp.ne', Real.log_exp] at hlog
  have hlogD : Real.log D ≤ D := by
    linarith [Real.log_le_sub_one_of_pos hDp]
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hE : 1 ≤ D * A ^ 2 := by nlinarith
  have hDE : D ≤ D * A ^ 2 := by nlinarith
  have hLbound : Real.log L ≤ Real.log L * (D * A ^ 2) := by nlinarith
  nlinarith

/-- The explicit positive height constant obtained by taking logarithms. -/
theorem unresolved_height_bound (M D A L c H z : ℝ)
    (hD : 1 ≤ D) (hA : 1 ≤ A) (hL : 1 ≤ L) (hM : 0 ≤ M) (hc : 0 < c)
    (hlower : Real.exp (-M * D * A ^ 2) ≤ z)
    (hupper : z ≤ L * D * Real.exp (-c * H)) :
    0 < (M + Real.log L + 1) / c ∧
      H ≤ ((M + Real.log L + 1) / c) * D * A ^ 2 := by
  have hnum : 0 < M + Real.log L + 1 := by
    linarith [Real.log_nonneg hL]
  refine ⟨div_pos hnum hc, ?_⟩
  have hb := unresolved_log_height_bound M D A L c H z hD hA hL hlower hupper
  calc
    H = (c * H) / c := by field_simp
    _ ≤ ((M + Real.log L + 1) * D * A ^ 2) / c :=
      div_le_div_of_nonneg_right hb hc.le
    _ = ((M + Real.log L + 1) / c) * D * A ^ 2 := by ring

/-- An endpoint-height lower bound combines with the Farey arc estimate
without any square-root algebra: `s² H³ ≤ C² K D`. -/
theorem cap_arc_squared_bound (s C H A K D : ℝ)
    (hs0 : 0 ≤ s) (hC : 0 ≤ C) (hH : 0 < H) (hA : 0 < A)
    (hs : s ≤ C / (H * A)) (hheight : H ≤ K * D * A ^ 2) :
    s ^ 2 * H ^ 3 ≤ C ^ 2 * K * D := by
  have hprod : s * (H * A) ≤ C := (le_div_iff₀ (mul_pos hH hA)).mp hs
  have hprod0 : 0 ≤ s * (H * A) := by positivity
  have hsq : (s * (H * A)) ^ 2 ≤ C ^ 2 := (sq_le_sq₀ hprod0 hC).2 hprod
  have h1 := mul_le_mul_of_nonneg_right hsq hH.le
  have h2 := mul_le_mul_of_nonneg_left hheight (sq_nonneg C)
  have hmul : (s ^ 2 * H ^ 3) * A ^ 2 ≤ (C ^ 2 * K * D) * A ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hA)

/-- The square-root form of the unresolved arc-size estimate. -/
theorem cap_arc_sqrt_bound (s C H A K D : ℝ)
    (hs0 : 0 ≤ s) (hC : 0 ≤ C) (hH : 0 < H) (hA : 0 < A)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hs : s ≤ C / (H * A)) (hheight : H ≤ K * D * A ^ 2) :
    s ≤ C * Real.sqrt K * Real.sqrt D / (H * Real.sqrt H) := by
  have hsq := cap_arc_squared_bound s C H A K D hs0 hC hH hA hs hheight
  have hleft : (s * H * Real.sqrt H) ^ 2 = s ^ 2 * H ^ 3 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hH.le]
    ring
  have hright : (C * Real.sqrt K * Real.sqrt D) ^ 2 = C ^ 2 * K * D := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hD]
  rw [← hleft, ← hright] at hsq
  have hb := (sq_le_sq₀ (by positivity : 0 ≤ s * H * Real.sqrt H)
    (by positivity : 0 ≤ C * Real.sqrt K * Real.sqrt D)).mp hsq
  apply (le_div_iff₀ (mul_pos hH (Real.sqrt_pos.2 hH))).mpr
  nlinarith

/-- Lemma 6's concluding analysis, with both geometric inputs visible:
the determinant upper bound and the Farey endpoint arc estimate. -/
theorem unresolved_cap_arc_bound (M D A L c H z C s : ℝ)
    (hD : 1 ≤ D) (hA : 1 ≤ A) (hL : 1 ≤ L) (hM : 0 ≤ M) (hc : 0 < c)
    (hH : 0 < H) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hlower : Real.exp (-M * D * A ^ 2) ≤ z)
    (hupper : z ≤ L * D * Real.exp (-c * H)) (hs : s ≤ C / (H * A)) :
    s ≤ C * Real.sqrt ((M + Real.log L + 1) / c) * Real.sqrt D /
      (H * Real.sqrt H) := by
  have hh := unresolved_height_bound M D A L c H z hD hA hL hM hc hlower hupper
  exact cap_arc_sqrt_bound s C H A ((M + Real.log L + 1) / c) D hs0 hC hH
    (by linarith) hh.1.le (by linarith) hs hh.2

end Markov
