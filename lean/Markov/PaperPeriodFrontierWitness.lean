import Markov.PaperStrictCellReturns
import Mathlib.Topology.Order.IntermediateValue

/-! Actual frontier witnesses strictly inside a positive period. The topology
argument uses the connected image of the actual parameter interval. No
sign-changing, adjacent-cell, or ordered-partition field is assumed. -/

noncomputable section
open Set Topology
universe u
namespace Markov

/-- A continuous curve from the interior of a closed set to its complement
has an actual frontier point at a parameter strictly between its endpoints. -/
theorem continuous_interval_frontier_witness {X : Type u} [TopologicalSpace X]
    (f : ℝ → X) (hf : Continuous f) (S : Set X) (hS : IsClosed S)
    (a b : ℝ) (hab : a<b) (ha : f a∈interior S) (hb : f b∉S) :
    ∃ t∈Ioo a b, f t∈frontier S := by
  classical
  by_contra hn
  push_neg at hn
  have hav : ∀ t∈Icc a b, f t∉frontier S := by
    intro t ht
    by_cases hta : t=a
    · subst t
      intro hfront
      exact hfront.2 ha
    by_cases htb : t=b
    · subst t
      intro hfront
      exact hb (by simpa only [hS.closure_eq] using hfront.1)
    exact hn t ⟨lt_of_le_of_ne ht.1 (fun h => hta h.symm),lt_of_le_of_ne ht.2 htb⟩
  have hcover : f '' Icc a b ⊆ interior S ∪ Sᶜ := by
    rintro z ⟨t,ht,rfl⟩
    by_cases hi : f t∈interior S
    · exact Or.inl hi
    · exact Or.inr (fun hs => hav t ht ⟨subset_closure hs,hi⟩)
  have hdisj : Disjoint (interior S) Sᶜ :=
    disjoint_left.mpr (fun z hz hzc => hzc (interior_subset hz))
  have hconn : IsPreconnected (f '' Icc a b) := isPreconnected_Icc.image f hf.continuousOn
  rcases hconn.subset_or_subset isOpen_interior hS.isOpen_compl hdisj hcover with hin | hout
  · exact hb (interior_subset (hin ⟨b,⟨hab.le,le_rfl⟩,rfl⟩))
  · exact (hout ⟨a,⟨le_rfl,hab.le⟩,rfl⟩) (interior_subset ha)

/-- The actual starting strict-cell point and actual outside endpoint give an
actual translated ORIGINAL-Q frontier point at a strictly intermediate time. -/
theorem paperQuadrilateral_frontier_cut_of_strict_start_exit
    (F : ℝ → UpperHalfPlane) (hF : Continuous F) (a b : ℝ) (hab : a<b)
    (δ : modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z∈paperIdealQuadrilateralStrictRegion) (hstart : δ • z=F a)
    (hend : F b∉(fun w : UpperHalfPlane => δ • w) '' paperIdealQuadrilateral) :
    ∃ t∈Ioo a b, ∃ w∈frontier paperIdealQuadrilateral, δ • w=F t := by
  let e : UpperHalfPlane ≃ₜ UpperHalfPlane := Homeomorph.smul δ
  have hclosed : IsClosed (e '' paperIdealQuadrilateral) :=
    e.isClosedMap _ paperIdealQuadrilateral_isClosed
  have hstartint : F a∈interior (e '' paperIdealQuadrilateral) := by
    rw [← e.image_interior]
    exact ⟨z,paperIdealQuadrilateralStrictRegion_subset_interior hz,hstart⟩
  obtain ⟨t,ht,hfront⟩ := continuous_interval_frontier_witness F hF
    (e '' paperIdealQuadrilateral) hclosed a b hab hstartint hend
  rw [← e.image_frontier] at hfront
  obtain ⟨w,hw,heq⟩ := hfront
  exact ⟨t,ht,w,hw,heq⟩

/-- The checked strict-return theorem discharges the outside endpoint for an
actual positive-period projected isometric line; an actual interior cut follows. -/
theorem periodicIsometricLine_period_frontier_cut
    (F : ℝ → UpperHalfPlane) (hF : Isometry F) (L : ℝ) (hL : 0<L)
    (hperiod : Function.Periodic (fun t => modularTraceQuotientMk (F t)) L)
    (a : ℝ) (δ : modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z∈paperIdealQuadrilateralStrictRegion) (hstart : δ • z=F a) :
    ∃ t∈Ioo a (a+L), ∃ w∈frontier paperIdealQuadrilateral, δ • w=F t :=
  paperQuadrilateral_frontier_cut_of_strict_start_exit F hF.continuous a (a+L)
    (by linarith) δ z hz hstart
    (periodicIsometricLine_period_endpoint_outside_start_cell F hF L hL hperiod a δ z hz hstart)

/-- Every actual hyperbolic deck axis has an actual strict phase, starting cell,
outside full-period endpoint, and true frontier cut strictly inside that period. -/
theorem modularHyperbolicAxis_exists_strict_phase_with_frontier_cut
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    ∃ a∈Ioo 0 (modularClosedGeodesicPeriod g),
      ∃ δ : modularTraceSubgroup, ∃ z∈paperIdealQuadrilateralStrictRegion,
        δ • z=modularHyperbolicAxis g hg a ∧
        modularHyperbolicAxis g hg (a+modularClosedGeodesicPeriod g)∉
          (fun w : UpperHalfPlane => δ • w) '' paperIdealQuadrilateral ∧
        ∃ t∈Ioo a (a+modularClosedGeodesicPeriod g),
          ∃ w∈frontier paperIdealQuadrilateral, δ • w=modularHyperbolicAxis g hg t := by
  obtain ⟨a,ha,δ,z,hz,hstart,hend⟩ :=
    modularHyperbolicAxis_exists_strict_phase_with_period_exit g hg
  refine ⟨a,ha,δ,z,hz,hstart,hend,?_⟩
  exact paperQuadrilateral_frontier_cut_of_strict_start_exit _
    (modularHyperbolicAxis_isometry g hg).continuous a _
    (by linarith [modularClosedGeodesicPeriod_pos g hg]) δ z hz hstart hend

end Markov
