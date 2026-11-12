import Markov.ProperEmbeddedCircleLift
import Markov.CanonicalEmbeddedMonodromy

/-! Actual proper embedded full-real lifts of canonical circles, with their
literal canonical hyperbolic monodromy and cyclic deck separation discharged.
No separation theorem for planar ends or projected-axis simplicity is asserted. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual full-real lift based at the endpoint of the actual lifted connector. -/
def embeddedCircleConnectorRealLift
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) : C(ℝ, UpperHalfPlane) :=
  embeddedCircleRealLift q hq (embeddedCircleConnectorLiftPoint q d)
    (embeddedCircleConnectorLiftPoint_project q d)

/-- Its actual projection retains the literal circle parameter. -/
theorem embeddedCircleConnectorRealLift_project
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) (t : ℝ) :
    modularTraceQuotientMk (embeddedCircleConnectorRealLift q hq d t) = q (t : NormalizedCircle) :=
  embeddedCircleRealLift_project q hq _ _ t

/-- The actual forward unit monodromy law at the lifted connector endpoint. -/
theorem embeddedCircleConnectorRealLift_add_one
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) (t : ℝ) :
    embeddedCircleConnectorRealLift q hq d (t+1) =
      embeddedCircleConnectorDeck q hq d • embeddedCircleConnectorRealLift q hq d t :=
  embeddedCircleRealLift_add_one q hq _ _ t

/-- Every canonical primitive datum has an actual circle and actual connector
whose full-real lift is proper and closed embedded, whose monodromy is literally
paperPrimitiveHolonomy, and whose translated lift ranges have exactly the
corresponding cyclic stabilizer and disjoint distinct deck cosets. All class and
hyperbolicity hypotheses have been discharged by the actual canonical data. -/
theorem paperPrimitiveHolonomy_has_properEmbeddedLift
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      embeddedCircleConnectorDeck q hq d = paperPrimitiveHolonomy k p hp ∧
      IsProperMap (embeddedCircleConnectorRealLift q hq d) ∧
      IsClosedEmbedding (embeddedCircleConnectorRealLift q hq d) ∧
      (∀ t : ℝ, embeddedCircleConnectorRealLift q hq d (t+1) =
        paperPrimitiveHolonomy k p hp • embeddedCircleConnectorRealLift q hq d t) ∧
      (∀ (h : modularTraceSubgroup) (s t : ℝ),
        h • embeddedCircleConnectorRealLift q hq d s = embeddedCircleConnectorRealLift q hq d t ↔
          ∃ n : ℤ, t-s = (n : ℝ) ∧ h = (paperPrimitiveHolonomy k p hp)^n) ∧
      (∀ h : modularTraceSubgroup,
        range (fun t : ℝ => h • embeddedCircleConnectorRealLift q hq d t) =
          range (embeddedCircleConnectorRealLift q hq d) ↔
            h ∈ Subgroup.zpowers (paperPrimitiveHolonomy k p hp)) ∧
      (∀ a b : modularTraceSubgroup,
        b⁻¹*a ∉ Subgroup.zpowers (paperPrimitiveHolonomy k p hp) →
        Disjoint (range (fun t : ℝ => a • embeddedCircleConnectorRealLift q hq d t))
          (range (fun t : ℝ => b • embeddedCircleConnectorRealLift q hq d t))) := by
  obtain ⟨q, hq, d, hD⟩ := paperPrimitiveHolonomy_has_embeddedCircle_monodromy k p hp
  let z := embeddedCircleConnectorLiftPoint q d
  let hz := embeddedCircleConnectorLiftPoint_project q d
  have hhyper : 2 < |((embeddedCircleRealLiftDeck q hq z hz).val : IntMatrixTwo).trace| := by
    change 2 < |((embeddedCircleConnectorDeck q hq d).val : IntMatrixTwo).trace|
    rw [hD]
    exact paperPrimitiveHolonomy_hyperbolic k p hp
  refine ⟨q, hq, d, hD,
    embeddedCircleRealLift_isProperMap_of_hyperbolicDeck q hq z hz hhyper,
    embeddedCircleRealLift_isClosedEmbedding_of_hyperbolicDeck q hq z hz hhyper,
    ?_, ?_, ?_, ?_⟩
  · intro t
    rw [embeddedCircleConnectorRealLift_add_one, hD]
  · intro h s t
    have he := embeddedCircleRealLift_deck_intersection_iff q hq z hz h s t
    change (h • embeddedCircleConnectorRealLift q hq d s = embeddedCircleConnectorRealLift q hq d t ↔
      ∃ n : ℤ, t-s = (n : ℝ) ∧ h = (embeddedCircleConnectorDeck q hq d)^n) at he
    simpa only [hD] using he
  · intro h
    have he := embeddedCircleRealLift_range_translate_eq_iff q hq z hz h
    change (range (fun t : ℝ => h • embeddedCircleConnectorRealLift q hq d t) =
      range (embeddedCircleConnectorRealLift q hq d) ↔
        h ∈ Subgroup.zpowers (embeddedCircleConnectorDeck q hq d)) at he
    simpa only [hD] using he
  · intro a b hab
    have hab' : b⁻¹*a ∉ Subgroup.zpowers (embeddedCircleRealLiftDeck q hq z hz) := by
      change b⁻¹*a ∉ Subgroup.zpowers (embeddedCircleConnectorDeck q hq d)
      simpa only [hD] using hab
    exact embeddedCircleRealLift_translates_disjoint_of_not_mem q hq z hz a b hab'

end Markov
