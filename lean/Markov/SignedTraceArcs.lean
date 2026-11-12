import Markov.SignedSectors
import Markov.CutoffArcs

/-! Uniform Euclidean radial variation on the eight signed coordinate
sectors. The signed bases live in the same trace normed plane, and all
lengths are measured by the original `traceEuclideanCoordinates` map.
Consecutive slopes refer to the actual finite primitive cutoff set.
No geometric identification with a hyperbolic surface is asserted. -/

noncomputable section
open scoped NNReal ENNReal
namespace Markov

/-- A positive trace-norm denominator bound for each signed basis. -/
def signedTraceRadialLowerBound (k : Fin 8) : ℝ :=
  Classical.choose (radialBasisSection_exists_norm_lower_bound (signedSectorBasis traceBasis k))

theorem signedTraceRadialLowerBound_pos (k : Fin 8) : 0 < signedTraceRadialLowerBound k :=
  (Classical.choose_spec
    (radialBasisSection_exists_norm_lower_bound (signedSectorBasis traceBasis k))).1

theorem signedTraceRadialLowerBound_le (k : Fin 8) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    signedTraceRadialLowerBound k ≤
      ‖signedSectorBasis traceBasis k 0 + t • signedSectorBasis traceBasis k 1‖ :=
  (Classical.choose_spec
    (radialBasisSection_exists_norm_lower_bound (signedSectorBasis traceBasis k))).2 t ht

/-- The signed section remains in the original trace normed space. -/
def signedTraceEuclideanRadialSection (k : Fin 8) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  traceEuclideanCoordinates ∘ radialBasisSection (signedSectorBasis traceBasis k)

/-- The source section uses the unchanged trace norm. -/
theorem norm_signedTraceRadialSection (k : Fin 8) (t : ℝ) :
    ‖radialBasisSection (signedSectorBasis traceBasis k) t‖ = 1 :=
  norm_radialBasisSection _ _

def signedTraceEuclideanSectorConstant (k : Fin 8) : ℝ≥0 :=
  ‖traceEuclideanCoordinates‖₊ *
    radialSectionLipschitzConstant (signedSectorBasis traceBasis k)
      (signedTraceRadialLowerBound k) (signedTraceRadialLowerBound_pos k)

/-- The maximum of the eight constants is finite and independent of the sector. -/
def signedTraceEuclideanArcConstant : ℝ≥0 :=
  Finset.univ.sup signedTraceEuclideanSectorConstant

theorem signedTraceEuclideanSectorConstant_le (k : Fin 8) :
    signedTraceEuclideanSectorConstant k ≤ signedTraceEuclideanArcConstant :=
  Finset.le_sup (Finset.mem_univ k)

theorem signedTraceEuclideanRadialSection_sector_lipschitzOnWith (k : Fin 8) :
    LipschitzOnWith (signedTraceEuclideanSectorConstant k)
      (signedTraceEuclideanRadialSection k) (Set.Icc (0 : ℝ) 1) :=
  radialBasisSection_target_lipschitzOnWith (signedSectorBasis traceBasis k)
    traceEuclideanCoordinates _ (signedTraceRadialLowerBound k)
    (signedTraceRadialLowerBound_pos k) (signedTraceRadialLowerBound_le k)

/-- One Lipschitz constant works in the actual Euclidean target for all eight sectors. -/
theorem signedTraceEuclideanRadialSection_lipschitzOnWith (k : Fin 8) :
    LipschitzOnWith signedTraceEuclideanArcConstant
      (signedTraceEuclideanRadialSection k) (Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  apply ((signedTraceEuclideanRadialSection_sector_lipschitzOnWith k).dist_le_mul s hs t ht).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast signedTraceEuclideanSectorConstant_le k) (dist_nonneg)

/-- The same finite constant bounds Euclidean metric variation in every sector. -/
theorem signedTraceEuclideanRadialSection_eVariationOn_le (k : Fin 8) (a b : ℝ)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ 1) :
    eVariationOn (signedTraceEuclideanRadialSection k) (Set.Icc a b) ≤
      ENNReal.ofReal ((signedTraceEuclideanArcConstant : ℝ) * (b - a)) := by
  rw [ENNReal.ofReal_mul (p := (signedTraceEuclideanArcConstant : ℝ)) (q := b - a)
    signedTraceEuclideanArcConstant.property, ENNReal.ofReal_coe_nnreal]
  apply lipschitzOnWith_eVariationOn_Icc_le
  exact (signedTraceEuclideanRadialSection_lipschitzOnWith k).mono
    (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)

theorem signedTraceEuclideanRadialSection_variation_le (k : Fin 8) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (eVariationOn (signedTraceEuclideanRadialSection k) (Set.Icc a b)).toReal ≤
      (signedTraceEuclideanArcConstant : ℝ) * (b - a) := by
  have h := signedTraceEuclideanRadialSection_eVariationOn_le k a b ha hab hb
  exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
    (ENNReal.toReal_ofReal
      (mul_nonneg signedTraceEuclideanArcConstant.property (sub_nonneg.mpr hab)))

/-- A single finite constant supplies both uniform regularity and variation. -/
theorem signedTraceEuclideanRadialSection_exists_uniform_constant :
    ∃ K : ℝ≥0, (∀ k : Fin 8, LipschitzOnWith K
      (signedTraceEuclideanRadialSection k) (Set.Icc (0 : ℝ) 1)) ∧
      ∀ (k : Fin 8) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
        eVariationOn (signedTraceEuclideanRadialSection k) (Set.Icc a b) ≤
          ENNReal.ofReal ((K : ℝ) * (b - a)) :=
  ⟨signedTraceEuclideanArcConstant, signedTraceEuclideanRadialSection_lipschitzOnWith,
    signedTraceEuclideanRadialSection_eVariationOn_le⟩

/-- Actual consecutive cutoff slopes discharge the arithmetic spacing
hypotheses; the same Euclidean constant works for every signed basis. -/
theorem signedTraceEuclideanRadialSection_cutoff_eVariationOn_le
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    eVariationOn (signedTraceEuclideanRadialSection k)
      (Set.Icc (cutoffSlope u) (cutoffSlope v)) ≤
      ENNReal.ofReal (2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ))) := by
  have huI := cutoffSlope_mem_Icc H u h.1
  have hvI := cutoffSlope_mem_Icc H v h.2.1
  have hord := ((consecutiveCutoffSlopes_iff_slope H u v).mp h).2.2.1
  have hgap := consecutiveCutoffSlopes_gap_le_scale H u v h
  calc
    eVariationOn (signedTraceEuclideanRadialSection k)
        (Set.Icc (cutoffSlope u) (cutoffSlope v)) ≤
        ENNReal.ofReal ((signedTraceEuclideanArcConstant : ℝ) *
          (cutoffSlope v - cutoffSlope u)) :=
      signedTraceEuclideanRadialSection_eVariationOn_le k _ _ huI.1 hord.le hvI.2
    _ ≤ ENNReal.ofReal (2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      have hwidth : cutoffSlope v - cutoffSlope u = |cutoffSlope u - cutoffSlope v| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hord.le)]
      rw [hwidth]
      calc
        (signedTraceEuclideanArcConstant : ℝ) * |cutoffSlope u - cutoffSlope v| ≤
            (signedTraceEuclideanArcConstant : ℝ) *
              (2 / ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hgap signedTraceEuclideanArcConstant.property
        _ = _ := by ring

/-- A transformed primitive vector gives its original normalized trace
vector. No symmetry of the trace norm under coordinate reflection is used. -/
theorem signedTraceEuclideanRadialSection_cutoff_endpoint (k : Fin 8)
    (u : ℤ × ℤ) (hu : 0 < (signedSectorCoordinates k u).1) :
    signedTraceEuclideanRadialSection k (cutoffSlope (signedSectorCoordinates k u)) =
      traceEuclideanCoordinates (NormedSpace.normalize (intVector traceBasis u)) := by
  rw [signedTraceEuclideanRadialSection, Function.comp_apply,
    ← normalize_intVector_eq_radialBasisSection _ _ hu, signedSectorBasis_intVector]

/-- The cutoff estimate in the original infinity heights. The only
arithmetic hypothesis is actual consecutiveness after the chosen signed
coordinate change, rather than assumed determinant or sum conditions. -/
theorem signedTraceEuclideanRadialSection_transformed_cutoff_eVariationOn_le
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H (signedSectorCoordinates k u)
      (signedSectorCoordinates k v)) :
    eVariationOn (signedTraceEuclideanRadialSection k)
      (Set.Icc (cutoffSlope (signedSectorCoordinates k u))
        (cutoffSlope (signedSectorCoordinates k v))) ≤
      ENNReal.ofReal (2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (intHeight u) (intHeight v))) := by
  have hu := (mem_cutoffSlopesUpTo H (signedSectorCoordinates k u)).mp h.1
  have hv := (mem_cutoffSlopesUpTo H (signedSectorCoordinates k v)).mp h.2.1
  have hus : InSignedSector k u := ⟨hu.2.1, hu.2.2.1⟩
  have hvs : InSignedSector k v := ⟨hv.2.1, hv.2.2.1⟩
  rw [hus.height_eq_first k u, hvs.height_eq_first k v]
  exact signedTraceEuclideanRadialSection_cutoff_eVariationOn_le k H _ _ h

theorem signedTraceEuclideanRadialSection_transformed_cutoff_variation_le
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H (signedSectorCoordinates k u)
      (signedSectorCoordinates k v)) :
    (eVariationOn (signedTraceEuclideanRadialSection k)
      (Set.Icc (cutoffSlope (signedSectorCoordinates k u))
        (cutoffSlope (signedSectorCoordinates k v)))).toReal ≤
      2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (intHeight u) (intHeight v)) := by
  have hb := signedTraceEuclideanRadialSection_transformed_cutoff_eVariationOn_le k H u v h
  apply (ENNReal.toReal_mono (by finiteness) hb).trans_eq
  have hu : 0 ≤ intHeight u := (abs_nonneg (u.1 : ℝ)).trans (le_max_left _ _)
  have hv : 0 ≤ intHeight v := (abs_nonneg (v.1 : ℝ)).trans (le_max_left _ _)
  exact ENNReal.toReal_ofReal (by positivity)

/-- Signed coordinate changes preserve the entire primitive height cutoff. -/
theorem signedSectorCoordinates_mem_primitiveDirectionsUpTo (k : Fin 8) (H : ℕ)
    (u : ℤ × ℤ) :
    signedSectorCoordinates k u ∈ primitiveDirectionsUpTo H ↔
      u ∈ primitiveDirectionsUpTo H := by
  rw [mem_primitiveDirectionsUpTo, mem_primitiveDirectionsUpTo,
    signedSectorCoordinates_coprime_iff, signedSectorCoordinates_height]

/-- The signed basis represents exactly the same actual cutoff corners. -/
theorem cutoffCorners_signedSectorBasis {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) (H : ℕ) :
    cutoffCorners (signedSectorBasis B k) H = cutoffCorners B H := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hqp : signedSectorCoordinates k
        (signedSectorCoordinates (signedSectorInverse k) q) = q := by
      simpa only [signedSectorInverse_involutive] using
        signedSectorCoordinates_inverse (signedSectorInverse k) q
    have hv := signedSectorBasis_intVector B k
      (signedSectorCoordinates (signedSectorInverse k) q)
    rw [hqp] at hv
    apply Finset.mem_image.mpr
    refine ⟨signedSectorCoordinates (signedSectorInverse k) q, ?_, ?_⟩
    · exact (signedSectorCoordinates_mem_primitiveDirectionsUpTo _ H q).mpr hq
    · exact congrArg NormedSpace.normalize hv.symm
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨signedSectorCoordinates k q, ?_, ?_⟩
    · exact (signedSectorCoordinates_mem_primitiveDirectionsUpTo k H q).mpr hq
    · exact congrArg NormedSpace.normalize (signedSectorBasis_intVector B k q)

/-- Consecutive transformed slopes avoid the original actual cutoff corners. -/
theorem transformedCutoffSlopes_arc_disjoint_corners {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (B : Module.Basis (Fin 2) ℝ E)
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H (signedSectorCoordinates k u)
      (signedSectorCoordinates k v)) :
    Disjoint (slopeBoundaryArc (signedSectorBasis B k)
      (cutoffSlope (signedSectorCoordinates k u))
      (cutoffSlope (signedSectorCoordinates k v))) (↑(cutoffCorners B H) : Set E) := by
  rw [← cutoffCorners_signedSectorBasis B k H]
  exact consecutiveCutoffSlopes_arc_disjoint_corners _ H _ _ h

/-- The signed-sector gap lies on the same unit boundary with the same
actual primitive cutoff corners removed. -/
theorem transformedCutoffSlopes_arc_subset_boundary_difference {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (B : Module.Basis (Fin 2) ℝ E)
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H (signedSectorCoordinates k u)
      (signedSectorCoordinates k v)) :
    slopeBoundaryArc (signedSectorBasis B k)
      (cutoffSlope (signedSectorCoordinates k u))
      (cutoffSlope (signedSectorCoordinates k v)) ⊆
      frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E) := by
  rw [← cutoffCorners_signedSectorBasis B k H]
  exact consecutiveCutoffSlopes_arc_subset_boundary_difference _ H _ _ h

end Markov
