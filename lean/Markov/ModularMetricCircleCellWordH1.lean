import Markov.PaperAxisCellWordH1
import Markov.ModularMetricCircleAxisNormalization
import Markov.UnimodularTorusHomeomorphisms

/-! The supplied metric circle's actual positive loop has the signed counts
of its actual normalized-axis side word. Only a literal period and phase
identity are used; no free-class or homology classification premise appears. -/
noncomputable section
open Set Topology
namespace Markov

/-- A literal actual selected-axis phase identifies the genuine fixed-I H1
coordinates of the supplied positive metric-circle loop with its forward deck
coordinates. The full-real lift is constructed from the actual selected axis. -/
theorem modularMetricCircle_positiveLoop_fixedCoordinates_of_axis_phase
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c : ℝ)
    (hlen : modularClosedGeodesicPeriod D = L)
    (hphase : ∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t+c)) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) =
      (paperTraceAbelianizationCoordinates D).toAdd := by
  let z := modularHyperbolicAxis D hg c
  let F : C(ℝ, UpperHalfPlane) :=
    ⟨fun t => modularHyperbolicAxis D hg (t+c),
      (modularHyperbolicAxis_isometry D hg).continuous.comp (continuous_id.add continuous_const)⟩
  have hz : modularTraceQuotientMk z = q 0 := by
    simpa only [z, zero_add, AddCircle.coe_zero] using (hphase 0).symm
  have hF0 : F 0 = z := by simp only [F, ContinuousMap.coe_mk, zero_add, z]
  have hproj (t : ℝ) : modularTraceQuotientMk (F t) = q (t : AddCircle L) :=
    (hphase t).symm
  have hD : F L = D • z := by
    change modularHyperbolicAxis D hg (L+c) = D • modularHyperbolicAxis D hg c
    rw [add_comm L c, ← hlen]
    exact (modularHyperbolicAxis_action D hg c).symm
  have hm := modularMetricCircle_positiveLoop_marked_of_lift L q z hz F hF0 hproj D hD
  have hcast := singularLoopClass_pointwise_eq
    ((modularMetricCirclePositiveLoop L q).cast hz hz)
    (modularMetricCirclePositiveLoop L q) (fun _ => rfl)
  rw [← hcast, modularTraceFixedSingularH1Equiv_loop]
  change (paperTraceAbelianizationCoordinates
      (modularTraceMarkedFundamentalGroupEquiv z (FundamentalGroup.fromPath
        (.mk ((modularMetricCirclePositiveLoop L q).cast hz hz))))).toAdd = _
  rw [hm, paperTraceAbelianizationCoordinates_seedConjugation,
    map_inv paperTraceAbelianizationCoordinates, inv_inv]

/-- The actual supplied circle's positive singular-H1 loop equals the signed
counts of the actual ordered side word of that SAME normalized deck axis. -/
theorem modularMetricCircle_positiveLoop_cellWord_coordinates_of_axis_phase
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c : ℝ)
    (hlen : modularClosedGeodesicPeriod D = L)
    (hphase : ∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t+c))
    (a : ℝ) (ha : a ∉ paperAxisSideCuts D hg) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) =
      ((paperAxisPeriodCellWord D hg a).map paperAxisCellLetterCoordinates).sum := by
  rw [modularMetricCircle_positiveLoop_fixedCoordinates_of_axis_phase L q D hg c hlen hphase,
    paperAxisPeriodCellWord_signedSum D hg a ha]

end Markov
