import Markov.TraceUnresolvedAssociation

/-! Passing to a coarser real primitive cutoff enlarges each actual
uncut component and its actual normal set. The closed angular
neighborhood retains the exact same radius through compact closure
witnesses. Thus original unresolved membership is monotone toward
coarser cutoffs without any uniqueness assumption. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Increasing the real primitive height cutoff enlarges the actual
cutoff corner set. -/
theorem realCutoffCorners_mono (B : Module.Basis (Fin 2) ℝ E)
    {h H : ℝ} (hhH : h ≤ H) : realCutoffCorners B h ⊆ realCutoffCorners B H := by
  rintro x ⟨p, hp, hph, heq⟩
  exact ⟨p, hp, hph.trans hhH, heq⟩

/-- A coarser cutoff removes fewer boundary points. -/
theorem traceUncutBoundary_antitone : Antitone traceUncutBoundary := by
  intro h H hhH x hx
  exact ⟨hx.1, fun hcut => hx.2 (realCutoffCorners_mono traceBasis hhH hcut)⟩

/-- The actual component at the finer cutoff is contained in the
actual component through the same point at the coarser cutoff. -/
theorem traceUncutBoundary_component_mono (x : TracePlane)
    {h H : ℝ} (hhH : h ≤ H) :
    connectedComponentIn (traceUncutBoundary H) x ⊆
      connectedComponentIn (traceUncutBoundary h) x :=
  connectedComponentIn_mono x (traceUncutBoundary_antitone hhH)

/-- Every point of the actual uncut boundary has norm one. -/
theorem norm_eq_one_of_mem_traceUncutBoundary (H : ℝ) (x : TracePlane)
    (hx : x ∈ traceUncutBoundary H) : ‖x‖ = 1 := by
  have hf := hx.1
  rw [frontier_closedBall (0 : TracePlane) (by norm_num : (1 : ℝ) ≠ 0)] at hf
  simpa using hf

/-- Every genuine uncut component has a nonempty actual normal set. -/
theorem traceUncutBoundary_component_normals_nonempty (H : ℝ) (x : TracePlane)
    (hx : x ∈ traceUncutBoundary H) :
    (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)).Nonempty := by
  obtain ⟨f, hf⟩ := normingFunctionals_nonempty x
  exact ⟨normalizedEuclideanCovector traceBasis f,
    x, mem_connectedComponentIn hx, f, hf, rfl⟩

/-- The actual normals of every uncut component have unit Euclidean norm. -/
theorem traceUncutBoundary_component_normals_unit (H : ℝ) (x : TracePlane)
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) :
    ‖y‖ = 1 := by
  apply norm_eq_one_of_mem_normalsOn traceBasis
    (connectedComponentIn (traceUncutBoundary H) x) _ y hy
  intro z hz
  exact norm_eq_one_of_mem_traceUncutBoundary H z
    (connectedComponentIn_subset (traceUncutBoundary H) x hz)

/-- Inclusion of nonempty unit-normal sets preserves exact closed
angular-neighborhood membership. The witness lies in the closure, so no
attainment among actual interior normals is required. -/
theorem closedAngularNeighborhood_mono
    (J J' : Set (EuclideanSpace ℝ (Fin 2)))
    (hJ : J.Nonempty) (hunit' : ∀ y ∈ J', ‖y‖ = 1) (hJJ' : J ⊆ J') (η : ℝ) :
    closedAngularNeighborhood J η ⊆ closedAngularNeighborhood J' η := by
  intro z hz
  have hunit : ∀ y ∈ J, ‖y‖ = 1 := fun y hy => hunit' y (hJJ' hy)
  obtain ⟨hzunit, y, hy, hyangle⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J hJ hunit z η).mp hz
  apply (mem_closedAngularNeighborhood_iff_exists_mem_closure
    J' (hJ.mono hJJ') hunit' z η).mpr
  exact ⟨hzunit, y, closure_mono hJJ' hy, hyangle⟩

/-- The closed normal neighborhood of the finer-cutoff component is
contained in that of the actual coarser-cutoff component. -/
theorem traceUncutBoundary_component_angular_neighborhood_mono
    (h H η : ℝ) (hhH : h ≤ H) (x : TracePlane) (hx : x ∈ traceUncutBoundary H) :
    closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η ⊆
    closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η := by
  apply closedAngularNeighborhood_mono _ _
    (traceUncutBoundary_component_normals_nonempty H x hx)
    (traceUncutBoundary_component_normals_unit h x)
    (normalsOn_mono traceBasis (traceUncutBoundary_component_mono x hhH)) η

/-- Original unresolved membership at a finer real cutoff passes to any
coarser real cutoff, preserving the covector, size bound and angular radius. -/
theorem IsTraceUnresolved.mono_cutoff
    {d : ℤ × ℤ} {K h H η : ℝ} (hunresolved : IsTraceUnresolved d K H η)
    (hhH : h ≤ H) : IsTraceUnresolved d K h η := by
  obtain ⟨hd, hK, x, hx, hmem⟩ := hunresolved
  refine ⟨hd, hK, x, traceUncutBoundary_antitone hhH hx, ?_⟩
  exact traceUncutBoundary_component_angular_neighborhood_mono h H η hhH x hx hmem

end Markov
