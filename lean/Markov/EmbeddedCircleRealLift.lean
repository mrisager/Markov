import Markov.PaperSimpleGeneratorCalibration
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
namespace Markov

/-- The actual full-real parametrization of an actual closed embedded circle. -/
def embeddedCircleRealParam (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q) :
    C(ℝ, ModularTraceQuotient) :=
  ⟨fun t => q ((t : ℝ) : NormalizedCircle),
    hq.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))⟩

theorem embeddedCircleRealParam_periodic (q : NormalizedCircle → ModularTraceQuotient)
    (hq : Topology.IsClosedEmbedding q) : Function.Periodic (embeddedCircleRealParam q hq) 1 := by
  intro t
  change q (((t+1 : ℝ)) : NormalizedCircle) = q ((t : ℝ) : NormalizedCircle)
  rw [AddCircle.coe_add_period]

/-- Exact equality of projected parameters: their real difference is an integer. -/
theorem embeddedCircleRealParam_eq_iff (q : NormalizedCircle → ModularTraceQuotient)
    (hq : Topology.IsClosedEmbedding q) (s t : ℝ) :
    embeddedCircleRealParam q hq s = embeddedCircleRealParam q hq t ↔
      ∃ n : ℤ, s-t = (n : ℝ) := by
  constructor
  · intro h
    have he : ((s-t : ℝ) : NormalizedCircle) = 0 := by
      change (s : NormalizedCircle) - (t : NormalizedCircle) = 0
      exact sub_eq_zero.mpr (hq.injective h)
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp he
    refine ⟨n, ?_⟩
    simpa only [zsmul_eq_mul, mul_one] using hn.symm
  · rintro ⟨n, hn⟩
    apply congrArg q
    apply sub_eq_zero.mp
    change ((s-t : ℝ) : NormalizedCircle) = 0
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

private theorem embeddedCircleRealLift_existsUnique
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    ∃! F : C(ℝ, UpperHalfPlane), F 0 = z ∧ modularTraceQuotientMk ∘ F = embeddedCircleRealParam q hq :=
  modularTraceQuotientMk_isCoveringMap.existsUnique_continuousMap_lifts
    (embeddedCircleRealParam q hq) 0 z (by
      change modularTraceQuotientMk z = q ((0 : ℝ) : NormalizedCircle)
      simpa only [AddCircle.coe_zero] using hz)

/-- The actual continuous global real lift with a prescribed actual initial point. -/
def embeddedCircleRealLift
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) : C(ℝ, UpperHalfPlane) :=
  (embeddedCircleRealLift_existsUnique q hq z hz).choose

theorem embeddedCircleRealLift_zero
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    embeddedCircleRealLift q hq z hz 0 = z :=
  (embeddedCircleRealLift_existsUnique q hq z hz).choose_spec.1.1

/-- The lift projects exactly to the displayed embedded-circle parametrization. -/
theorem embeddedCircleRealLift_project
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (t : ℝ) :
    modularTraceQuotientMk (embeddedCircleRealLift q hq z hz t) = q (t : NormalizedCircle) :=
  congr_fun (embeddedCircleRealLift_existsUnique q hq z hz).choose_spec.1.2 t

/-- Uniqueness is the actual covering global-lift uniqueness theorem. -/
theorem embeddedCircleRealLift_unique
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0)
    (F : C(ℝ, UpperHalfPlane)) (hF0 : F 0 = z)
    (hFp : modularTraceQuotientMk ∘ F = embeddedCircleRealParam q hq) :
    F = embeddedCircleRealLift q hq z hz :=
  (embeddedCircleRealLift_existsUnique q hq z hz).choose_spec.2 F ⟨hF0, hFp⟩

/-- Exact equality after projecting two lift points. -/
theorem embeddedCircleRealLift_project_eq_iff
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (s t : ℝ) :
    modularTraceQuotientMk (embeddedCircleRealLift q hq z hz s) =
      modularTraceQuotientMk (embeddedCircleRealLift q hq z hz t) ↔
        ∃ n : ℤ, s-t = (n : ℝ) := by
  rw [embeddedCircleRealLift_project, embeddedCircleRealLift_project]
  exact embeddedCircleRealParam_eq_iff q hq s t

/-- Equality of actual lifted points already forces an integral parameter difference. -/
theorem embeddedCircleRealLift_eq_imp_integer
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) {s t : ℝ}
    (h : embeddedCircleRealLift q hq z hz s = embeddedCircleRealLift q hq z hz t) :
    ∃ n : ℤ, s-t = (n : ℝ) :=
  (embeddedCircleRealLift_project_eq_iff q hq z hz s t).mp (congrArg modularTraceQuotientMk h)

theorem embeddedCircleRealLift_one_fiber
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    modularTraceQuotientMk (embeddedCircleRealLift q hq z hz 1) = modularTraceQuotientMk z := by
  rw [embeddedCircleRealLift_project, hz, AddCircle.coe_period]

/-- The actual forward unit deck element labels the actual endpoint of the lifted unit interval. -/
def embeddedCircleRealLiftDeck
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) : modularTraceSubgroup :=
  (modularTraceFibreEquiv z).symm
    ⟨embeddedCircleRealLift q hq z hz 1, embeddedCircleRealLift_one_fiber q hq z hz⟩

theorem embeddedCircleRealLiftDeck_one
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    embeddedCircleRealLiftDeck q hq z hz • z = embeddedCircleRealLift q hq z hz 1 :=
  congrArg Subtype.val ((modularTraceFibreEquiv z).apply_symm_apply _)

/-- Actual full-real unit equivariance, proved by uniqueness of continuous lifts. -/
theorem embeddedCircleRealLift_add_one
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (t : ℝ) :
    embeddedCircleRealLift q hq z hz (t+1) =
      embeddedCircleRealLiftDeck q hq z hz • embeddedCircleRealLift q hq z hz t := by
  let F := embeddedCircleRealLift q hq z hz
  let D := embeddedCircleRealLiftDeck q hq z hz
  have he : (fun s : ℝ => F (s+1)) = (fun s : ℝ => D • F s) :=
    modularTraceQuotientMk_isCoveringMap.eq_of_comp_eq
      (F.continuous.comp (continuous_id.add continuous_const))
      ((modularTraceSubgroup_isometry D).continuous.comp F.continuous)
      (by
        funext s
        change modularTraceQuotientMk (F (s+1)) = modularTraceQuotientMk (D • F s)
        rw [modularTraceQuotientMk_smul]
        exact (embeddedCircleRealLift_project q hq z hz (s+1)).trans
          ((embeddedCircleRealParam_periodic q hq s).trans (embeddedCircleRealLift_project q hq z hz s).symm))
      0 (by
        rw [zero_add, embeddedCircleRealLift_zero]
        exact (embeddedCircleRealLiftDeck_one q hq z hz).symm)
  exact congr_fun he t

/-- The actual lifted positive unit interval, with its actual forward deck endpoint. -/
def embeddedCircleRealLiftUnitPath
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    Path z (embeddedCircleRealLiftDeck q hq z hz • z) where
  toFun u := embeddedCircleRealLift q hq z hz (u : ℝ)
  continuous_toFun := (embeddedCircleRealLift q hq z hz).continuous.comp continuous_subtype_val
  source' := embeddedCircleRealLift_zero q hq z hz
  target' := (embeddedCircleRealLiftDeck_one q hq z hz).symm

/-- The actual once-around circle loop with its basepoint displayed under the chosen lift. -/
def embeddedCircleUnitLoop
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    Path (modularTraceQuotientMk z) (modularTraceQuotientMk z) :=
  (normalizedCircleStandardLoop.map hq.continuous).cast hz hz

/-- The actual lifted interval projects exactly to the actual positive once-around loop. -/
theorem embeddedCircleRealLiftUnitPath_projected
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    (((embeddedCircleRealLiftUnitPath q hq z hz).map modularTraceQuotientMk_continuous).cast rfl
      (modularTraceQuotientMk_smul (embeddedCircleRealLiftDeck q hq z hz) z).symm) =
        embeddedCircleUnitLoop q hq z hz := by
  ext u
  change modularTraceQuotientMk (embeddedCircleRealLift q hq z hz (u : ℝ)) =
    q (normalizedCircleStandardLoop u)
  rw [embeddedCircleRealLift_project, normalizedCircleStandardLoop_apply]

/-- The chosen forward unit deck element is exactly actual covering monodromy. -/
theorem embeddedCircleUnitLoop_deck
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    modularTraceLoopDeckEquiv z (.mk (embeddedCircleUnitLoop q hq z hz)) =
      embeddedCircleRealLiftDeck q hq z hz := by
  apply (modularTraceFibreEquiv z).injective
  rw [modularTraceLoopDeckEquiv_fibre, ← embeddedCircleRealLiftUnitPath_projected]
  exact coveringLoopEndpoint_projectedPath modularTraceQuotientMk_isCoveringMap
    (embeddedCircleRealLiftUnitPath q hq z hz)
    (modularTraceQuotientMk_smul (embeddedCircleRealLiftDeck q hq z hz) z)

/-- The genuine original marking of the positive once-around loop retains the
inverse-endpoint and whole-word S-conjugation convention explicitly. -/
theorem embeddedCircleUnitLoop_marked
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) :
    modularTraceMarkedFundamentalGroupEquiv z
      (FundamentalGroup.fromPath (.mk (embeddedCircleUnitLoop q hq z hz))) =
        modularTraceSeedConjugation (embeddedCircleRealLiftDeck q hq z hz)⁻¹ := by
  rw [← embeddedCircleRealLiftUnitPath_projected]
  exact modularTraceMarkedFundamentalGroupEquiv_projectedPath z _ (embeddedCircleRealLiftUnitPath q hq z hz)

end Markov
