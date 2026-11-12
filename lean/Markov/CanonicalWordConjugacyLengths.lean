import Markov.CanonicalTraceNormPeriods
import Markov.ModularAxisUniqueness
import Markov.PaperAxisOrderedCellWord

/-! Literal canonical-word conjugacy supplies actual metric length, with the
RAW word's negative original marking retained. No arbitrary class theorem is
assumed and S-conjugation is never replaced by inversion. -/
noncomputable section
open Set
namespace Markov

private theorem actualPeriod_isConj (g h : modularTraceSubgroup) (hc : IsConj g h) :
    modularClosedGeodesicPeriod g = modularClosedGeodesicPeriod h := by
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  rw [← hc,modularClosedGeodesicPeriod_conjugate]

private theorem actualTraceNorm_neg (p : ℤ × ℤ) :
    ‖intVector traceBasis (-p)‖ = ‖intVector traceBasis p‖ := by
  have hv : intVector traceBasis (-p) = -intVector traceBasis p := by
    simp only [intVector,Prod.fst_neg,Prod.snd_neg,Int.cast_neg,neg_smul,neg_add]
  rw [hv,norm_neg]

/-- The RAW actual canonical word has the canonical metric period even
though its original marked coordinates are minus its label. Actual S
conjugation preserves trace; explicit hyperbolicity justifies the trace formula. -/
theorem quadrantPrimitiveTraceWord_period_eq_trace_norm
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularClosedGeodesicPeriod (quadrantPrimitiveTraceWord k p hp) =
      ‖intVector traceBasis p‖ := by
  have ht : ((paperPrimitiveHolonomy k p hp).val : IntMatrixTwo).trace =
      ((quadrantPrimitiveTraceWord k p hp).val : IntMatrixTwo).trace := by
    change (paperSeedConjugation (quadrantPrimitiveTraceWord k p hp).val : IntMatrixTwo).trace = _
    exact paperSeedConjugation_trace _
  have hH := paperPrimitiveHolonomy_hyperbolic k p hp
  have hW : 2 < |((quadrantPrimitiveTraceWord k p hp).val : IntMatrixTwo).trace| := by
    rw [← ht]
    exact hH
  calc
    modularClosedGeodesicPeriod (quadrantPrimitiveTraceWord k p hp) =
        modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) := by
      rw [modularClosedGeodesicPeriod_trace _ hW,modularClosedGeodesicPeriod_trace _ hH,ht]
    _ = ‖intVector traceBasis p‖ := paperPrimitiveHolonomy_period_eq_trace_norm k p hp

/-- Genuine conjugacy of an actual deck element to a RAW canonical word or
its literal inverse forces the actual metric period to equal the constructed
trace norm of the element's original marked label. Conjugacy itself derives
the correct plus/minus label; it is not inferred from H1. -/
theorem modularClosedGeodesicPeriod_eq_trace_norm_of_canonical_word_conjugacy
    (D : modularTraceSubgroup) (p : ℤ × ℤ)
    (hcoords : (paperTraceAbelianizationCoordinates D).toAdd = p)
    (k : Fin 4) (v : ℤ × ℤ)
    (hv : NonnegativePrimitiveDirection (quadrantCoordinates k v))
    (hcan : IsConj D (quadrantPrimitiveTraceWord k v hv) ∨
      IsConj D (quadrantPrimitiveTraceWord k v hv)⁻¹) :
    modularClosedGeodesicPeriod D = ‖intVector traceBasis p‖ := by
  rcases hcan with hc | hc
  · have hp := isConj_iff_eq.mp (paperTraceAbelianizationCoordinates.map_isConj hc)
    rw [quadrantPrimitiveTraceWord_coordinates] at hp
    have hlabel : p = -v := by
      exact hcoords.symm.trans (congrArg Multiplicative.toAdd hp)
    rw [actualPeriod_isConj D _ hc,quadrantPrimitiveTraceWord_period_eq_trace_norm,hlabel,actualTraceNorm_neg]
  · have hp := isConj_iff_eq.mp (paperTraceAbelianizationCoordinates.map_isConj hc)
    rw [map_inv,quadrantPrimitiveTraceWord_coordinates] at hp
    have hlabel : p = v := by
      have hh := hcoords.symm.trans (congrArg Multiplicative.toAdd hp)
      change p = -(-v) at hh
      simpa only [neg_neg] using hh
    rw [actualPeriod_isConj D _ hc,modularClosedGeodesicPeriod_inv,
      quadrantPrimitiveTraceWord_period_eq_trace_norm,hlabel]

/-- The actual finite-Q itinerary product is genuinely conjugate to D by
its actual first cell label. Thus a literal canonical-word conjugacy of that
product supplies the actual metric trace-norm period, with original marking. -/
theorem modularClosedGeodesicPeriod_eq_trace_norm_of_cellWord_conjugacy
    (D : modularTraceSubgroup) (hD : 2 < |(D.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts D hD)
    (p : ℤ × ℤ) (hcoords : (paperTraceAbelianizationCoordinates D).toAdd = p)
    (k : Fin 4) (v : ℤ × ℤ)
    (hv : NonnegativePrimitiveDirection (quadrantCoordinates k v))
    (hcan : IsConj (((paperAxisPeriodCellWord D hD a).map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k v hv) ∨
      IsConj (((paperAxisPeriodCellWord D hD a).map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k v hv)⁻¹) :
    modularClosedGeodesicPeriod D = ‖intVector traceBasis p‖ := by
  let C := paperAxisPeriodGapCellLabel D hD a (paperAxisFirstGapIndex D hD a)
  have hprod : IsConj D (((paperAxisPeriodCellWord D hD a).map paperQuadrilateralSideNeighbor).prod) := by
    apply isConj_iff.mpr
    refine ⟨C⁻¹,?_⟩
    simpa only [inv_inv] using (paperAxisPeriodCellWord_prod D hD a ha).symm
  apply modularClosedGeodesicPeriod_eq_trace_norm_of_canonical_word_conjugacy D p hcoords k v hv
  exact hcan.imp hprod.trans hprod.trans

/-- The same supplied actual itinerary conjugacy gives actual metric
variation on a full period of the actual selected projected axis. No canonical
existence, simplicity, least-period or arbitrary-class theorem is repeated. -/
theorem modularClosedGeodesic_trace_norm_variation_of_cellWord_conjugacy
    (D : modularTraceSubgroup) (hD : 2 < |(D.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts D hD)
    (p : ℤ × ℤ) (hcoords : (paperTraceAbelianizationCoordinates D).toAdd = p)
    (k : Fin 4) (v : ℤ × ℤ)
    (hv : NonnegativePrimitiveDirection (quadrantCoordinates k v))
    (hcan : IsConj (((paperAxisPeriodCellWord D hD a).map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k v hv) ∨
      IsConj (((paperAxisPeriodCellWord D hD a).map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k v hv)⁻¹) :
    (eVariationOn (modularClosedGeodesic D hD) (Icc 0 ‖intVector traceBasis p‖)).toReal =
      ‖intVector traceBasis p‖ := by
  rw [← modularClosedGeodesicPeriod_eq_trace_norm_of_cellWord_conjugacy D hD a ha p hcoords k v hv hcan]
  exact modularClosedGeodesic_period_length D hD

end Markov
