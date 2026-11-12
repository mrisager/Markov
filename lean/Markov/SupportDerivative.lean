import Markov.NormedPlane
import Mathlib.Analysis.Convex.Deriv

/-! The right directional derivative of a norm equals the value of the
selected supporting functional, as used in §3.1 (quoted Lemma 2.6).
The proof uses one-dimensional convex derivatives and constructs a norming
functional with the extremal derivative as its second basis value. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_norm_line (a b : E) : ConvexOn ℝ univ (fun t : ℝ => ‖a + t • b‖) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy α β hα hβ hab
  have he : a + (α * x + β * y) • b = α • (a + x • b) + β • (a + y • b) := by
    calc
      _ = (α + β) • a + (α * x + β * y) • b := by rw [hab, one_smul]
      _ = _ := by module
  change ‖a + (α * x + β * y) • b‖ ≤ α * ‖a + x • b‖ + β * ‖a + y • b‖
  rw [he]
  calc
    _ ≤ ‖α • (a + x • b)‖ + ‖β • (a + y • b)‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hβ]

/-- The right derivative of the norm restricted to a line gives a supporting
line of that convex real function, on both sides of zero. -/
theorem norm_line_rightDeriv_support (a b : E) (z : ℝ) :
    ‖a‖ + derivWithin (fun t : ℝ => ‖a + t • b‖) (Ioi 0) 0 * z ≤ ‖a + z • b‖ := by
  let g : ℝ → ℝ := fun t => ‖a + t • b‖
  have hc : ConvexOn ℝ univ g := convexOn_norm_line a b
  have hi : (0 : ℝ) ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hleft := hc.slope_le_leftDeriv_of_mem_interior (mem_univ z) hi hz
    have hright := hc.leftDeriv_le_rightDeriv_of_mem_interior hi
    rw [slope_comm] at hleft
    have h := hleft.trans hright
    simp only [slope_def_field, sub_zero] at h
    have hm := (div_le_iff_of_neg hz).mp h
    simpa [g] using (show g 0 + derivWithin g (Ioi 0) 0 * z ≤ g z by linarith)
  · simp
  · have h := hc.rightDeriv_le_slope_of_mem_interior hi (mem_univ z) hz
    simp only [slope_def_field, sub_zero] at h
    have hm := (le_div_iff₀ hz).mp h
    simpa [g] using (show g 0 + derivWithin g (Ioi 0) 0 * z ≤ g z by linarith)

/-- Extend a supporting line of the norm section to its homogeneous plane. -/
theorem norm_plane_support_from_line (a b : E) (q : ℝ)
    (hline : ∀ z : ℝ, ‖a‖ + q * z ≤ ‖a + z • b‖) (s t : ℝ) :
    s * ‖a‖ + t * q ≤ ‖s • a + t • b‖ := by
  let K : ℝ := |s| + 1
  let p : ℝ := K + s
  have hK : 0 < K := by dsimp [K]; positivity
  have hp : 0 < p := by dsimp [p, K]; linarith [neg_abs_le s]
  have hpt : p * (t / p) = t := by field_simp
  have he : K • a + (s • a + t • b) = p • (a + (t / p) • b) := by
    rw [smul_add, smul_smul, hpt]
    dsimp [p]
    module
  have heNorm : ‖K • a + (s • a + t • b)‖ = p * ‖a + (t / p) • b‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
  have hl : p * ‖a‖ + q * t ≤ ‖K • a + (s • a + t • b)‖ := by
    calc
      _ = p * (‖a‖ + q * (t / p)) := by field_simp
      _ ≤ p * ‖a + (t / p) • b‖ := mul_le_mul_of_nonneg_left (hline _) hp.le
      _ = _ := heNorm.symm
  have hu := norm_add_le (K • a) (s • a + t • b)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hK] at hu
  dsimp [p] at hl
  nlinarith

def slopeFunctional (B : Module.Basis (Fin 2) ℝ E) (q : ℝ) : StrongDual ℝ E := by
  letI : FiniteDimensional ℝ E := Module.Finite.of_basis B
  exact (B.constr ℝ ![‖B 0‖, q]).toContinuousLinearMap

theorem slopeFunctional_zero (B : Module.Basis (Fin 2) ℝ E) (q : ℝ) :
    slopeFunctional B q (B 0) = ‖B 0‖ := by simp [slopeFunctional]

theorem slopeFunctional_one (B : Module.Basis (Fin 2) ℝ E) (q : ℝ) :
    slopeFunctional B q (B 1) = q := by simp [slopeFunctional]

theorem slopeFunctional_isNorming (B : Module.Basis (Fin 2) ℝ E) (q : ℝ)
    (hline : ∀ z : ℝ, ‖B 0‖ + q * z ≤ ‖B 0 + z • B 1‖) :
    slopeFunctional B q ∈ normingFunctionals (B 0) := by
  have hupper : ∀ x : E, slopeFunctional B q x ≤ ‖x‖ := by
    intro x
    have hx : (B.repr x) 0 • B 0 + (B.repr x) 1 • B 1 = x := by
      simpa only [Fin.sum_univ_two] using B.sum_repr x
    have h := norm_plane_support_from_line (B 0) (B 1) q hline ((B.repr x) 0) ((B.repr x) 1)
    rw [hx] at h
    simpa [slopeFunctional, Module.Basis.constr_apply_fintype, Fin.sum_univ_two] using h
  refine ⟨?_, slopeFunctional_zero B q⟩
  apply (slopeFunctional B q).opNorm_le_bound (by norm_num)
  intro x
  rw [Real.norm_eq_abs, one_mul, abs_le]
  refine ⟨?_, hupper x⟩
  have h := hupper (-x)
  simp only [map_neg, norm_neg] at h
  linarith

theorem normingFunctional_le_norm (a x : E) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals a) : f x ≤ ‖x‖ := by
  have hn : |f x| ≤ ‖f‖ * ‖x‖ := by simpa using f.le_opNorm x
  have hm := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg x)
  exact (le_abs_self _).trans (hn.trans (by simpa using hm))

theorem normingFunctional_le_rightDeriv (B : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals (B 0)) :
    f (B 1) ≤ derivWithin (fun t : ℝ => ‖B 0 + t • B 1‖) (Ioi 0) 0 := by
  let g : ℝ → ℝ := fun t => ‖B 0 + t • B 1‖
  have hc : ConvexOn ℝ univ g := convexOn_norm_line _ _
  have hder := hc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp : (0 : ℝ) ∈ interior (univ : Set ℝ))
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hder
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have h := normingFunctional_le_norm (B 0) (B 0 + t • B 1) f hf
  rw [map_add, map_smul, hf.2] at h
  simp only [smul_eq_mul] at h
  simp only [slope_def_field, sub_zero]
  apply (le_div_iff₀ ht).mpr
  simpa [g] using (show f (B 1) * t ≤ g t - g 0 by simpa [g] using (by linarith : f (B 1) * t ≤ ‖B 0 + t • B 1‖ - ‖B 0‖))

theorem selectedSupport_value_eq_rightDeriv (B : Module.Basis (Fin 2) ℝ E) :
    selectedSupport B (B 1) =
      derivWithin (fun t : ℝ => ‖B 0 + t • B 1‖) (Ioi 0) 0 := by
  let q := derivWithin (fun t : ℝ => ‖B 0 + t • B 1‖) (Ioi 0) 0
  have hq := slopeFunctional_isNorming B q (norm_line_rightDeriv_support (B 0) (B 1))
  have hmax := (selectedSupport_spec B).2 (slopeFunctional B q) hq
  rw [slopeFunctional_one] at hmax
  exact le_antisymm
    (normingFunctional_le_rightDeriv B (selectedSupport B) (selectedSupport_spec B).1) hmax

/-- The directional-derivative limit quoted in §3.1, proved for any normed plane. -/
theorem selectedSupport_directional_limit (B : Module.Basis (Fin 2) ℝ E) :
    Tendsto (fun t : ℝ => (‖B 0 + t • B 1‖ - ‖B 0‖) / t)
      (𝓝[>] 0) (𝓝 (selectedSupport B (B 1))) := by
  have hc := convexOn_norm_line (B 0) (B 1)
  have hder := hc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp : (0 : ℝ) ∈ interior (univ : Set ℝ))
  rw [← selectedSupport_value_eq_rightDeriv B] at hder
  have h := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hder
  have hs : slope (fun t : ℝ => ‖B 0 + t • B 1‖) 0 =
      (fun t : ℝ => (‖B 0 + t • B 1‖ - ‖B 0‖) / t) := by
    ext t
    simp [slope_def_field]
  rw [hs] at h
  exact h

/-- The same limit for the two nonparallel integer directions used in the paper. -/
theorem selectedSupportAt_directional_limit (B : Module.Basis (Fin 2) ℝ E)
    (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0) :
    Tendsto (fun t : ℝ =>
      (‖intVector B u + t • intVector B v‖ - ‖intVector B u‖) / t)
      (𝓝[>] 0) (𝓝 (selectedSupportAt B u v (intVector B v))) := by
  rw [selectedSupportAt, dif_pos hdet]
  simpa only [intPairBasis_zero, intPairBasis_one]
    using selectedSupport_directional_limit (intPairBasis B u v hdet)

theorem norm_affine_difference_identity (a b : E) (r : ℝ) (hr : 0 < r) :
    ‖r • a + b‖ - r * ‖a‖ = (‖a + r⁻¹ • b‖ - ‖a‖) / r⁻¹ := by
  have he : r • (a + r⁻¹ • b) = r • a + b := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, div_inv_eq_mul]
  ring

/-- The large integral-ray form of the directional derivative. It is ready
to combine with the Fricke recurrence and trace–length asymptotics. -/
theorem selectedSupport_integral_ray_limit (B : Module.Basis (Fin 2) ℝ E) :
    Tendsto (fun n : ℕ => ‖((n : ℝ) + 1) • B 0 + B 1‖ - ((n : ℝ) + 1) * ‖B 0‖)
      atTop (𝓝 (selectedSupport B (B 1))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := tendsto_inv_atTop_nhdsGT_zero.comp hn
  have h := (selectedSupport_directional_limit B).comp ht
  convert h using 1
  ext n
  exact norm_affine_difference_identity (B 0) (B 1) ((n : ℝ) + 1) (by positivity)

end Markov
