import Markov.TraceCutoffPathComponents
import Markov.GlobalArcLength

/-! Closed actual boundary arcs and their Euclidean diameter bounds.
The bounds use the finite variation of the existing signed radial curve.
-/

noncomputable section
open Set
namespace Markov

private theorem continuous_if_lt_seam {F : Type*} [TopologicalSpace F]
    (f g : ℝ → F) (c : ℝ) (hf : Continuous f) (hg : Continuous g)
    (hseam : f c = g c) :
    Continuous (fun t => if t < c then f t else g t) := by
  apply Continuous.if _ hf hg
  intro t ht
  have he : t = c := frontier_lt_subset_eq continuous_id continuous_const ht
  simpa only [he] using hseam

/-- The four actual normalized chords glue continuously at every seam. -/
theorem continuous_traceBoundaryPath : Continuous traceBoundaryPath := by
  have h0 : Continuous (fun t : ℝ => chordBoundarySection (traceRotationBasis 0) t) :=
    chordBoundarySection_continuous _
  have h1 : Continuous (fun t : ℝ =>
      chordBoundarySection (traceRotationBasis 1) (t - 1)) :=
    (chordBoundarySection_continuous _).comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun t : ℝ =>
      chordBoundarySection (traceRotationBasis 2) (t - 2)) :=
    (chordBoundarySection_continuous _).comp (continuous_id.sub continuous_const)
  have h3 : Continuous (fun t : ℝ =>
      chordBoundarySection (traceRotationBasis 3) (t - 3)) :=
    (chordBoundarySection_continuous _).comp (continuous_id.sub continuous_const)
  have h23 := continuous_if_lt_seam _ _ 3 h2 h3 (by
    norm_num only [sub_self, show (3 : ℝ) - 2 = 1 by norm_num]
    exact chordBoundarySection_seam (traceRotationBasis 2))
  have h123 := continuous_if_lt_seam _ _ 2 h1 h23 (by
    norm_num only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num,
      show (2 : ℝ) < 3 by norm_num, if_true]
    exact chordBoundarySection_seam (traceRotationBasis 1))
  have h0123 := continuous_if_lt_seam _ _ 1 h0 h123 (by
    norm_num only [sub_self, show (1 : ℝ) < 2 by norm_num, if_true]
    exact chordBoundarySection_seam (traceRotationBasis 0))
  exact h0123

/-- Adding the two actual endpoints gives the closure of any nonempty
open path interval. -/
theorem closure_traceBoundaryOpenArc (a b : ℝ) (hab : a < b) :
    closure (traceBoundaryOpenArc a b) = traceBoundaryPath '' Icc a b := by
  have hc : IsCompact (traceBoundaryPath '' Icc a b) :=
    isCompact_Icc.image continuous_traceBoundaryPath
  apply le_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) hc.isClosed
  · rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image continuous_traceBoundaryPath

/-- The closure of a signed actual cutoff component is its closed radial
parametrization, including both genuine endpoint vectors. -/
theorem closure_signed_cutoff_arc
    (n : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) :
    closure (slopeBoundaryArc (signedSectorBasis traceBasis k)
      (cutoffSlope u) (cutoffSlope v)) =
      radialBasisSection (signedSectorBasis traceBasis k) ''
        Icc (cutoffSlope u) (cutoffSlope v) :=
  closure_slopeBoundaryArc _ _ _
    ((consecutiveCutoffSlopes_iff_slope n u v).mp h).2.2.1

/-- The actual signed cutoff curve has finite Euclidean variation. -/
theorem signedTraceCutoffArcLength_ne_top
    (n : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) :
    signedTraceCutoffArcLength k u v ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness)
    (signedTraceCutoffArcLength_le_original_heights k n u v h)

/-- Any two points in the closure of the actual signed component are no
farther apart in the fixed Euclidean coordinates than its actual variation. -/
theorem dist_traceEuclideanCoordinates_le_signedTraceCutoffArcLength
    (n : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (x y : TracePlane)
    (hx : x ∈ closure (slopeBoundaryArc (signedSectorBasis traceBasis k)
      (cutoffSlope u) (cutoffSlope v)))
    (hy : y ∈ closure (slopeBoundaryArc (signedSectorBasis traceBasis k)
      (cutoffSlope u) (cutoffSlope v))) :
    dist (traceEuclideanCoordinates x) (traceEuclideanCoordinates y) ≤
      (signedTraceCutoffArcLength k u v).toReal := by
  rw [closure_signed_cutoff_arc n k u v h] at hx hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hv : BoundedVariationOn (signedTraceEuclideanRadialSection k)
      (Icc (cutoffSlope u) (cutoffSlope v)) :=
    signedTraceCutoffArcLength_ne_top n k u v h
  exact hv.dist_le hs ht

/-- Every actual uncut component has the closed path arc obtained by
adding its two marked endpoints in the same traversal. -/
theorem traceUncutBoundary_exists_closed_path_component
    (H : ℝ) (hH : 1 ≤ H) (x : TracePlane) (hx : x ∈ traceUncutBoundary H) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 4 ∧
      traceBoundaryPath a ∈ realCutoffCorners traceBasis H ∧
      traceBoundaryPath b ∈ realCutoffCorners traceBasis H ∧
      connectedComponentIn (traceUncutBoundary H) x = traceBoundaryOpenArc a b ∧
      closure (connectedComponentIn (traceUncutBoundary H) x) =
        traceBoundaryPath '' Icc a b := by
  obtain ⟨a, b, ha, hab, hb, hma, hmb, he⟩ :=
    traceUncutBoundary_exists_path_component H hH x hx
  exact ⟨a, b, ha, hab, hb, hma, hmb, he,
    by rw [he, closure_traceBoundaryOpenArc a b hab]⟩

end Markov
