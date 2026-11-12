import Markov.CutoffNeighbors
import Markov.BoundaryArc
import Markov.TraceArcs

/-! The primitive height cutoff on the trace unit boundary and its
canonical-sector gaps. Consecutive endpoints bound arcs free of cutoff
points. The Euclidean variation bound follows from the arithmetic
estimates for the constructed trace norm. -/

noncomputable section
open scoped NNReal ENNReal
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit boundary points selected by the actual primitive height cutoff. -/
def cutoffCorners (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) : Finset E := by
  classical
  exact (primitiveDirectionsUpTo H).image (fun u => NormedSpace.normalize (intVector B u))

theorem cutoffCorners_card_le (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) :
    (cutoffCorners B H).card ≤ (2 * H + 1) ^ 2 := by
  classical
  exact (Finset.card_image_le).trans (primitiveDirectionsUpTo_card_le H)

/-- Canonical denominator-cutoff directions belong to the full primitive
 height cutoff used to remove points from the unit boundary. -/
theorem cutoffSlope_mem_primitiveDirectionsUpTo (H : ℕ) (u : ℤ × ℤ)
    (hu : u ∈ cutoffSlopesUpTo H) : u ∈ primitiveDirectionsUpTo H := by
  obtain ⟨hup, huq, huqp, huH, hcop⟩ := (mem_cutoffSlopesUpTo H u).mp hu
  have hp : (0 : ℝ) ≤ u.1 := by exact_mod_cast hup.le
  have hq : (0 : ℝ) ≤ u.2 := by exact_mod_cast huq
  have hqp : (u.2 : ℝ) ≤ u.1 := by exact_mod_cast huqp
  apply (mem_primitiveDirectionsUpTo H u).mpr
  refine ⟨hcop, ?_⟩
  simp only [intHeight, abs_of_nonneg hp, abs_of_nonneg hq, max_eq_left hqp]
  exact_mod_cast huH

theorem normalize_mem_cutoffCorners (B : Module.Basis (Fin 2) ℝ E) (H : ℕ)
    (u : ℤ × ℤ) (hu : u ∈ cutoffSlopesUpTo H) :
    NormedSpace.normalize (intVector B u) ∈ cutoffCorners B H := by
  classical
  exact Finset.mem_image.mpr ⟨u, cutoffSlope_mem_primitiveDirectionsUpTo H u hu, rfl⟩

private theorem coord_zero_normalize_intVector (B : Module.Basis (Fin 2) ℝ E)
    (u : ℤ × ℤ) :
    B.coord 0 (NormedSpace.normalize (intVector B u)) =
      ‖intVector B u‖⁻¹ * (u.1 : ℝ) := by
  simp [NormedSpace.normalize, intVector, Module.Basis.coord_apply, Module.Basis.repr_self]

/-- Positive denominator normalization is exactly the radial slope section. -/
theorem normalize_intVector_eq_radialBasisSection (B : Module.Basis (Fin 2) ℝ E)
    (u : ℤ × ℤ) (hu : 0 < u.1) :
    NormedSpace.normalize (intVector B u) = radialBasisSection B (cutoffSlope u) := by
  have hp : (0 : ℝ) < u.1 := by exact_mod_cast hu
  have he : intVector B u = (u.1 : ℝ) • (B 0 + cutoffSlope u • B 1) := by
    rw [intVector, smul_add, smul_smul]
    congr 1
    congr 1
    dsimp [cutoffSlope]
    field_simp
  rw [he, NormedSpace.normalize_smul_of_pos hp]
  rfl

/-- The primitive cutoff points lie on the unit norm boundary. -/
theorem mem_cutoffCorners_norm (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (x : E)
    (hx : x ∈ cutoffCorners B H) : ‖x‖ = 1 := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  have hcop := ((mem_primitiveDirectionsUpTo H u).mp hu).1
  have hne : intVector B u ≠ 0 := by
    intro hz
    have h0 := congrArg (B.coord 0) hz
    have h1 := congrArg (B.coord 1) hz
    have hu0 : u.1 = 0 := by
      have : (u.1 : ℝ) = 0 := by
        simpa [intVector, Module.Basis.coord_apply, Module.Basis.repr_self] using h0
      exact_mod_cast this
    have hu1 : u.2 = 0 := by
      have : (u.2 : ℝ) = 0 := by
        simpa [intVector, Module.Basis.coord_apply, Module.Basis.repr_self] using h1
      exact_mod_cast this
    obtain ⟨s, t, hbez⟩ := hcop
    simp [hu0, hu1] at hbez
  exact NormedSpace.norm_normalize hne

theorem cutoffSlope_mem_Icc (H : ℕ) (u : ℤ × ℤ) (hu : u ∈ cutoffSlopesUpTo H) :
    cutoffSlope u ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hup, huq, huqp, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp hu
  have hp : (0 : ℝ) < u.1 := by exact_mod_cast hup
  have hq : (0 : ℝ) ≤ u.2 := by exact_mod_cast huq
  have hqp : (u.2 : ℝ) ≤ u.1 := by exact_mod_cast huqp
  exact ⟨div_nonneg hq hp.le, (div_le_one hp).mpr hqp⟩

/-- A cutoff point in the canonical positive slope wedge is represented
 by a member of the actual denominator cutoff set. -/
theorem cutoffCorner_in_canonical_wedge (B : Module.Basis (Fin 2) ℝ E) (H : ℕ)
    (x : E) (hx : x ∈ cutoffCorners B H) (hp : 0 < B.coord 0 x)
    (hs : basisSlope B x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u ∈ cutoffSlopesUpTo H, x = radialBasisSection B (cutoffSlope u) := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hcop, hheight⟩ := (mem_primitiveDirectionsUpTo H u).mp hu
  have hupreal : (0 : ℝ) < u.1 := by
    rw [coord_zero_normalize_intVector] at hp
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (intVector B u)))
      (show (u.1 : ℝ) ≤ 0 by linarith)
    linarith
  have hup : 0 < u.1 := by exact_mod_cast hupreal
  have he := normalize_intVector_eq_radialBasisSection B u hup
  rw [he, basisSlope_radialBasisSection] at hs
  have huqreal : (0 : ℝ) ≤ u.2 := by
    have hh := (le_div_iff₀ hupreal).mp hs.1
    simpa only [zero_mul] using hh
  have huqpreal : (u.2 : ℝ) ≤ u.1 := by
    have hh := (div_le_iff₀ hupreal).mp hs.2
    simpa only [one_mul] using hh
  have huHreal : (u.1 : ℝ) ≤ H :=
    (le_abs_self _).trans ((le_max_left _ _).trans hheight)
  have huq : 0 ≤ u.2 := by exact_mod_cast huqreal
  have huqp : u.2 ≤ u.1 := by exact_mod_cast huqpreal
  have huH : u.1 ≤ H := by exact_mod_cast huHreal
  exact ⟨u, (mem_cutoffSlopesUpTo H u).mpr ⟨hup, huq, huqp, huH, hcop⟩, he⟩

/-- No actual primitive height-cutoff point occurs in the open unit-boundary
 arc between consecutive canonical-sector cutoff slopes. -/
theorem consecutiveCutoffSlopes_arc_disjoint_corners
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    Disjoint (slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v))
      (↑(cutoffCorners B H) : Set E) := by
  apply Set.disjoint_left.mpr
  intro x hx hcorner
  have huI := cutoffSlope_mem_Icc H u h.1
  have hvI := cutoffSlope_mem_Icc H v h.2.1
  obtain ⟨w, hw, hxw⟩ := cutoffCorner_in_canonical_wedge B H x hcorner hx.2.1
    ⟨huI.1.trans hx.2.2.1.le, hx.2.2.2.le.trans hvI.2⟩
  have hxs : basisSlope B x = cutoffSlope w := by rw [hxw, basisSlope_radialBasisSection]
  have hn := (consecutiveCutoffSlopes_iff_slope H u v).mp h
  exact hn.2.2.2 w hw ⟨by simpa only [hxs] using hx.2.2.1,
    by simpa only [hxs] using hx.2.2.2⟩

/-- The open gap is contained in the actual unit boundary after removing
 all primitive height-cutoff points. -/
theorem consecutiveCutoffSlopes_arc_subset_boundary_difference
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) ⊆
      frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa using hx.1
  · exact Set.disjoint_left.mp (consecutiveCutoffSlopes_arc_disjoint_corners B H u v h) hx

/-- The actual boundary arc in the constructed trace norm plane. -/
def traceCutoffArc (u v : ℤ × ℤ) : Set TracePlane :=
  slopeBoundaryArc traceBasis (cutoffSlope u) (cutoffSlope v)

/-- Consecutive cutoff arcs have the required Euclidean variation scale. -/
theorem traceEuclideanRadialSection_cutoff_eVariationOn_le (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    eVariationOn traceEuclideanRadialSection (Set.Icc (cutoffSlope u) (cutoffSlope v)) ≤
      ENNReal.ofReal (2 * (traceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ))) := by
  obtain ⟨hup, _, _, huH, _⟩ := (mem_cutoffSlopesUpTo H u).mp h.1
  have hvp := ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  have hH : (0 : ℝ) < H := by
    have : (0 : ℤ) < H := hup.trans_le huH
    exact_mod_cast this
  have hsum : (H : ℝ) < (u.1 : ℝ) + v.1 := by
    exact_mod_cast (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).2
  have hdet : |(u.1 : ℝ) * v.2 - (u.2 : ℝ) * v.1| = 1 := by
    exact_mod_cast consecutiveCutoffSlopes_abs_det H u v h
  have hbound := traceEuclideanRadialSection_farey_eVariationOn_le
    (u.1 : ℝ) u.2 v.1 v.2 H (by exact_mod_cast hup) (by exact_mod_cast hvp)
    hH hsum hdet (cutoffSlope_mem_Icc H u h.1) (cutoffSlope_mem_Icc H v h.2.1)
  have hord := ((consecutiveCutoffSlopes_iff_slope H u v).mp h).2.2.1
  change eVariationOn traceEuclideanRadialSection
    (Set.Icc (min (cutoffSlope u) (cutoffSlope v))
      (max (cutoffSlope u) (cutoffSlope v))) ≤ _ at hbound
  simpa only [min_eq_left hord.le, max_eq_right hord.le] using hbound

/-- Real-valued Euclidean variation for consecutive actual cutoff endpoints. -/
theorem traceEuclideanRadialSection_cutoff_variation_le (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    (eVariationOn traceEuclideanRadialSection
      (Set.Icc (cutoffSlope u) (cutoffSlope v))).toReal ≤
      2 * (traceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ)) := by
  have hup : (0 : ℝ) < u.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H u).mp h.1).1
  have hvp : (0 : ℝ) < v.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  have hb := traceEuclideanRadialSection_cutoff_eVariationOn_le H u v h
  exact (ENNReal.toReal_mono (by finiteness) hb).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end Markov
