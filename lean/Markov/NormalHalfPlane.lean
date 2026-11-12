import Markov.BoundaryNormals

/-! A common open half-plane for the actual supporting normals of the
canonical trace quarter arc. The half-plane is derived from the strict
mixed-seed length triangle, rather than assumed as angular containment. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equal-length rays whose difference has strictly smaller than twice their
length have positive support evaluation on their sum throughout this cone. -/
theorem normingFunctional_sum_pos_of_equal_norm
    (a b : E) (L t : ℝ) (ha : ‖a‖ = L) (hb : ‖b‖ = L)
    (hdiff : ‖a - b‖ < 2 * L) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals (a + t • b)) :
    0 < f (a + b) := by
  have hfa : f a ≤ L := by
    calc
      f a ≤ |f a| := le_abs_self _
      _ ≤ ‖f‖ * ‖a‖ := f.le_opNorm a
      _ ≤ ‖a‖ := by nlinarith [hf.1, norm_nonneg a]
      _ = L := ha
  have hfb : -L ≤ f b := by
    have hh : |f b| ≤ L := by
      calc
        |f b| ≤ ‖f‖ * ‖b‖ := f.le_opNorm b
        _ ≤ ‖b‖ := by nlinarith [hf.1, norm_nonneg b]
        _ = L := hb
    exact (abs_le.mp hh).1
  have hbound : L - t * L ≤ f a + t * f b := by
    have hh := norm_sub_le (a + t • b) (t • b)
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0,
      ha, hb, ← hf.2, map_add, map_smul, smul_eq_mul] at hh
    linarith
  by_contra hpos
  have hsum : f a + f b ≤ 0 := by simpa only [map_add] using le_of_not_gt hpos
  have hweighted : t * (f a + f b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hsum
  have heqa : f a = L := by
    apply le_antisymm hfa
    by_contra h
    have hstrict : 0 < (1 - t) * (L - f a) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have heqb : f b = -L := by linarith
  have hdiffbound : f (a - b) ≤ ‖a - b‖ := by
    calc
      f (a - b) ≤ |f (a - b)| := le_abs_self _
      _ ≤ ‖f‖ * ‖a - b‖ := f.le_opNorm _
      _ ≤ ‖a - b‖ := by nlinarith [hf.1, norm_nonneg (a - b)]
  rw [map_sub, heqa, heqb] at hdiffbound
  linarith

/-- The same positivity includes both endpoints of the parameter interval. -/
theorem normingFunctional_sum_pos_of_equal_norm_Icc
    (a b : E) (L t : ℝ) (ha : ‖a‖ = L) (hb : ‖b‖ = L)
    (hdiff : ‖a - b‖ < 2 * L) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals (a + t • b)) :
    0 < f (a + b) := by
  by_cases ht1 : t < 1
  · exact normingFunctional_sum_pos_of_equal_norm a b L t ha hb hdiff ht.1 ht1 f hf
  have ht_eq : t = 1 := by linarith [ht.2]
  have hsum_ne : a + b ≠ 0 := by
    intro hz
    have hbneg : b = -a := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_comm] using hz
    have hdiff_eq : a - b = (2 : ℝ) • a := by rw [hbneg]; module
    have hdiff_norm : ‖a - b‖ = 2 * L := by
      rw [hdiff_eq, norm_smul, Real.norm_eq_abs, ha]
      norm_num
    linarith
  have heval : f (a + b) = ‖a + b‖ := by
    simpa only [ht_eq, one_smul] using hf.2
  rw [heval]
  exact norm_pos_iff.mpr hsum_ne

/-- Strict positivity survives Euclidean normalization of the covector. -/
theorem normalizedEuclideanCovector_sum_pos
    (C : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E)
    (hf : 0 < f (C 0 + C 1)) :
    0 < normalizedEuclideanCovector C f 0 + normalizedEuclideanCovector C f 1 := by
  have hfnz : f ≠ 0 := by
    intro hz
    simp [hz] at hf
  have hnorm : 0 < ‖euclideanDualCoordinates C f‖ :=
    norm_pos_iff.mpr (euclideanDualCoordinates_ne_zero C f hfnz)
  change 0 < ‖euclideanDualCoordinates C f‖⁻¹ * f (C 0) +
    ‖euclideanDualCoordinates C f‖⁻¹ * f (C 1)
  rw [← mul_add, ← map_add]
  exact mul_pos (inv_pos.mpr hnorm) hf

/-- The strict difference bound comes from the actual mixed-sign seed.
No reflection invariance of the trace norm is used. -/
theorem norm_traceBasis_sub_lt_twice_axis :
    ‖traceBasis 0 - traceBasis 1‖ < 2 * traceAxisLength := by
  have hseed : SeededFarey (1, 0) (0, 1)
      modularGeneratorB modularGeneratorA.adjugate (1, 0) (0, 1)
      modularGeneratorB modularGeneratorA.adjugate := .seed
  let h0 : NonnegativePrimitiveDirection (1, 0) := hseed.coordinate_left_nonnegativePrimitive
  let h1 : NonnegativePrimitiveDirection (0, 1) := hseed.coordinate_right_nonnegativePrimitive
  have hs : NonnegativePrimitiveDirection ((1, 0) + (0, 1)) :=
    hseed.left.coordinate_right_nonnegativePrimitive
  have hstrict := hseed.canonicalSeedLength_strict_triangle
    (quadrantSeed_positiveFrickePair 1) h0 h1 hs
  have hn0 := norm_intVector_next (1, 0) h0
  have hn1 := norm_intVector_next (0, 1) h1
  have hns := norm_intVector_next ((1, 0) + (0, 1)) hs
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_one, Int.cast_zero,
    zero_add, one_smul, zero_smul, add_zero, norm_neg,
    norm_traceBasis_zero, norm_traceBasis_one] at hn0 hn1 hns
  rw [← hn0, ← hn1, ← hns] at hstrict
  rw [norm_sub_rev]
  change ‖traceBasis 1 + -traceBasis 0‖ < 2 * traceAxisLength
  linarith

/-- Every actual support over the canonical trace cone lies in the same
strict dual half-plane. This is a conclusion about all supports. -/
theorem trace_normingFunctional_sum_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1)) :
    0 < f (traceBasis 0 + traceBasis 1) :=
  normingFunctional_sum_pos_of_equal_norm _ _ traceAxisLength t
    norm_traceBasis_zero norm_traceBasis_one norm_traceBasis_sub_lt_twice_axis ht0 ht1 f hf

/-- The common strict half-plane also contains every support at both ends
of the canonical closed trace radial section. -/
theorem trace_normingFunctional_sum_pos_Icc (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1)) :
    0 < f (traceBasis 0 + traceBasis 1) :=
  normingFunctional_sum_pos_of_equal_norm_Icc _ _ traceAxisLength t
    norm_traceBasis_zero norm_traceBasis_one norm_traceBasis_sub_lt_twice_axis ht f hf

/-- All actual Euclidean normals above the trace unit boundary quarter arc
belong to the open half-plane with positive coordinate sum. -/
theorem trace_quarterArc_normals_subset_openHalfPlane :
    normalsOn traceBasis (slopeBoundaryArc traceBasis 0 1) ⊆
      {n | 0 < n 0 + n 1} := by
  rw [normalsOn_slopeBoundaryArc]
  rintro n ⟨f, ⟨t, ht, hf⟩, rfl⟩
  have hcone : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1) := by
    rwa [radialBasisSection,
      normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero traceBasis t)] at hf
  exact normalizedEuclideanCovector_sum_pos traceBasis f
    (trace_normingFunctional_sum_pos t ht.1.le ht.2 f hcone)

/-- A closed radial-section formulation, with the two endpoint normal
sets included. -/
theorem trace_closedQuarterArc_normals_subset_openHalfPlane :
    normalsOn traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) ⊆
      {n | 0 < n 0 + n 1} := by
  rintro n ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
  have hcone : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1) := by
    rwa [radialBasisSection,
      normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero traceBasis t)] at hf
  exact normalizedEuclideanCovector_sum_pos traceBasis f
    (trace_normingFunctional_sum_pos_Icc t ht f hcone)

end Markov
