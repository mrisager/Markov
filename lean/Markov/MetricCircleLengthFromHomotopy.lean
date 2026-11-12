import Markov.IntrinsicSimpleGeodesicLengths
import Markov.ModularLocalGeodesicLift
import Markov.CanonicalAxisMarkedClass

noncomputable section
open Set Topology
namespace Markov

/-- Actual full-real covering lift of a metric circle from a supplied fibre point. -/
theorem modularMetricCircle_real_lift_exists
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    ∃ F : C(ℝ, UpperHalfPlane), F 0 = z ∧
      ∀ t : ℝ, modularTraceQuotientMk (F t) = q (t : AddCircle L) := by
  let γ : C(ℝ, ModularTraceQuotient) :=
    ⟨fun t => q (t : AddCircle L), q.continuous.comp (AddCircle.continuous_mk' L)⟩
  obtain ⟨F, ⟨hF0, hFp⟩, _⟩ :=
    modularTraceQuotientMk_isCoveringMap.existsUnique_continuousMap_lifts γ 0 z (by
      simpa only [γ, ContinuousMap.coe_mk, AddCircle.coe_zero] using hz)
  exact ⟨F, hF0, fun t => congr_fun hFp t⟩

/-- An actual lifted connector and actual projected period lift identify the
literal forward monodromy from the supplied geometric loop homotopy. -/
theorem modularMetricCircle_deck_eq_of_loop_homotopy
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (z : UpperHalfPlane) (C : Path (modularHyperbolicAxis g hg 0) z)
    (c : Path (modularClosedGeodesic g hg 0) (q 0))
    (hCproj : ∀ t : unitInterval, modularTraceQuotientMk (C t) = c t)
    (F : C(ℝ, UpperHalfPlane)) (hF0 : F 0 = z)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = q (t : AddCircle L))
    (D : modularTraceSubgroup) (hD : F L = D • z)
    (hclass : ((c.trans (modularMetricCirclePositiveLoop L q)).trans c.symm).Homotopic
      (modularClosedGeodesicLoop g hg)) : D = g := by
  let z0 := modularHyperbolicAxis g hg 0
  let η : Path z (D • z) := {
    toFun := fun t => F ((t : ℝ)*L)
    continuous_toFun := F.continuous.comp (continuous_subtype_val.mul continuous_const)
    source' := by simpa using hF0
    target' := by simpa using hD }
  have hηproj (t : unitInterval) :
      modularTraceQuotientMk (η t) = modularMetricCirclePositiveLoop L q t := by
    change modularTraceQuotientMk (F ((t : ℝ)*L)) = _
    rw [hproj, modularMetricCirclePositiveLoop_apply]
  let U : Path z0 (D • z0) :=
    (C.trans η).trans (C.map (modularTraceSubgroup_isometry D).continuous).symm
  let δ : Path (modularTraceQuotientMk z0) (modularTraceQuotientMk z0) :=
    (U.map modularTraceQuotientMk_continuous).cast rfl
      (modularTraceQuotientMk_smul D z0).symm
  have hδeq : δ = ((c.trans (modularMetricCirclePositiveLoop L q)).trans c.symm) := by
    ext t
    simp only [δ, U, Path.cast_coe, Path.map_coe, Function.comp_apply,
      Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact hCproj _
    · exact hηproj _
    · rw [modularTraceQuotientMk_smul]
      exact hCproj _
  have hδhom : δ.Homotopic (modularClosedGeodesicLoop g hg) := by
    rw [hδeq]
    exact hclass
  have hπ : FundamentalGroup.fromPath (.mk δ) =
      FundamentalGroup.fromPath (.mk (modularClosedGeodesicLoop g hg)) :=
    congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr hδhom)
  have hmarkD : modularTraceMarkedFundamentalGroupEquiv z0
      (FundamentalGroup.fromPath (.mk δ)) = modularTraceSeedConjugation D⁻¹ :=
    modularTraceMarkedFundamentalGroupEquiv_projectedPath z0 D U
  have hcanEq :
      (((modularHyperbolicAxisSegment g hg).map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul g z0).symm) = modularClosedGeodesicLoop g hg := by
    ext t
    rfl
  have hmarkg : modularTraceMarkedFundamentalGroupEquiv z0
      (FundamentalGroup.fromPath (.mk (modularClosedGeodesicLoop g hg))) =
        modularTraceSeedConjugation g⁻¹ := by
    rw [← hcanEq]
    exact modularTraceMarkedFundamentalGroupEquiv_projectedPath z0 g
      (modularHyperbolicAxisSegment g hg)
  apply inv_injective
  apply modularTraceSeedConjugation_involutive.injective
  exact hmarkD.symm.trans ((congrArg (modularTraceMarkedFundamentalGroupEquiv z0) hπ).trans hmarkg)

/-- An actual continuous locally unit-speed metric circle whose positive loop
is explicitly homotopic, through an actual connector, to the actual forward
canonical axis loop has that axis's metric period. The full-real lift and its
literal forward monodromy are constructed inside the proof. -/
theorem modularMetricCircle_period_eq_of_axis_loop_homotopy
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u)
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (c : Path (modularClosedGeodesic g hg 0) (q 0))
    (hclass : ((c.trans (modularMetricCirclePositiveLoop L q)).trans c.symm).Homotopic
      (modularClosedGeodesicLoop g hg)) :
    L = modularClosedGeodesicPeriod g := by
  let z0 := modularHyperbolicAxis g hg 0
  let cov := modularTraceQuotientMk_isCoveringMap
  let Cmap := cov.liftPath c z0 c.source
  let z := Cmap 1
  let C : Path z0 z := {
    toFun := Cmap
    continuous_toFun := Cmap.continuous
    source' := cov.liftPath_zero c z0 c.source
    target' := rfl }
  have hCproj (t : unitInterval) : modularTraceQuotientMk (C t) = c t :=
    congr_fun (cov.liftPath_lifts c z0 c.source) t
  have hz : modularTraceQuotientMk z = q 0 := (hCproj 1).trans c.target
  let γ : C(ℝ, ModularTraceQuotient) :=
    ⟨fun t => q (t : AddCircle L), q.continuous.comp (AddCircle.continuous_mk' L)⟩
  obtain ⟨F, hF0, hproj⟩ := modularMetricCircle_real_lift_exists L q z hz
  have hperiod : Function.Periodic γ L := by
    intro t
    change q ((t+L : ℝ) : AddCircle L) = q (t : AddCircle L)
    rw [AddCircle.coe_add, AddCircle.coe_period L, add_zero]
  obtain ⟨D, hD⟩ := (modularTraceQuotientMk_eq_iff (F L) z).mp (by
    rw [hproj, hz, AddCircle.coe_period])
  have hDg : D = g := modularMetricCircle_deck_eq_of_loop_homotopy
    L q g hg z C c hCproj F hF0 hproj D hD.symm hclass
  have hlen := modularTraceQuotientLift_period_eq_translationLength γ F F.continuous
    hproj hloc L hL hperiod D (by rw [hF0]; exact hD.symm)
  rw [hDg] at hlen
  exact hlen.symm

/-- For an actual canonical primitive free class, the explicitly supplied
geometric loop homotopy gives the actual constructed trace-norm length. -/
theorem modularMetricCircle_length_eq_trace_norm_of_canonical_loop_homotopy
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u)
    (c : Path (paperPrimitiveClosedGeodesic k p hp 0) (q 0))
    (hclass : ((c.trans (modularMetricCirclePositiveLoop L q)).trans c.symm).Homotopic
      (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp))) :
    L = ‖intVector traceBasis p‖ :=
  (modularMetricCircle_period_eq_of_axis_loop_homotopy L hL q hloc
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp) c hclass).trans
      (paperPrimitiveHolonomy_period_eq_trace_norm k p hp)

end Markov
