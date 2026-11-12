import Markov.TraceSupportCapLimit
import Markov.CircleNormalOffsets
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual perpendicular sections of the Euclidean trace body and their
one-dimensional length profile. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Markov

/-- The point with longitudinal coordinate `t` and transverse coordinate `s`. -/
def traceSectionPoint (θ : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    EuclideanSpace ℝ (Fin 2) := t • θ + s • quarterTurnNormal θ

/-- The actual transverse section of the trace body. -/
def traceSection (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : Set ℝ :=
  {s | traceSectionPoint θ t s ∈ traceEuclideanBall}

/-- The actual section profile, defined by integrating the body's indicator. -/
def traceSectionProfile (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  ∫ s : ℝ, traceEuclideanBall.indicator (fun _ ↦ (1 : ℝ)) (traceSectionPoint θ t s)

theorem continuous_traceSectionPoint (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    Continuous (traceSectionPoint θ t) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem traceSectionPoint_inner_normal {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t s : ℝ) : inner ℝ (traceSectionPoint θ t s) θ = t := by
  have horth : inner ℝ (quarterTurnNormal θ) θ = 0 := by
    rw [real_inner_comm]
    exact inner_quarterTurnNormal_self θ
  simp only [traceSectionPoint, inner_add_left, real_inner_smul_left, horth, mul_zero,
    add_zero, real_inner_self_eq_norm_sq, hθ, one_pow, mul_one]

theorem traceSectionPoint_inner_transverse {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t s : ℝ) : inner ℝ (traceSectionPoint θ t s) (quarterTurnNormal θ) = s := by
  simp only [traceSectionPoint, inner_add_left, real_inner_smul_left,
    inner_quarterTurnNormal_self, mul_zero, zero_add, real_inner_self_eq_norm_sq,
    norm_quarterTurnNormal, hθ, one_pow, mul_one]

/-- The fixed Euclidean coordinate operator bounds every point of the actual body. -/
theorem norm_le_trace_coordinate_norm_of_mem {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ traceEuclideanBall) : ‖x‖ ≤ ‖traceEuclideanCoordinates‖ := by
  obtain ⟨v, hv, rfl⟩ := hx
  have hv' : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  exact (traceEuclideanCoordinates.le_opNorm v).trans
    ((mul_le_mul_of_nonneg_left hv' (norm_nonneg _)).trans_eq (mul_one _))

theorem traceSection_subset_Icc {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t : ℝ) : traceSection θ t ⊆ Icc (-‖traceEuclideanCoordinates‖) ‖traceEuclideanCoordinates‖ := by
  intro s hs
  have hi := abs_real_inner_le_norm (traceSectionPoint θ t s) (quarterTurnNormal θ)
  rw [traceSectionPoint_inner_transverse hθ, norm_quarterTurnNormal, hθ, mul_one] at hi
  exact abs_le.mp (hi.trans (norm_le_trace_coordinate_norm_of_mem hs))

theorem isClosed_traceSection (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    IsClosed (traceSection θ t) :=
  isCompact_traceEuclideanBall.isClosed.preimage (continuous_traceSectionPoint θ t)

theorem isCompact_traceSection {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t : ℝ) : IsCompact (traceSection θ t) :=
  (isCompact_Icc).of_isClosed_subset (isClosed_traceSection θ t) (traceSection_subset_Icc hθ t)

theorem convex_traceSection (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    Convex ℝ (traceSection θ t) := by
  intro a ha b hb u v hu hv huv
  have key := strictConvex_traceEuclideanBall.convex ha hb hu hv huv
  change traceSectionPoint θ t (u • a + v • b) ∈ traceEuclideanBall
  have hid : traceSectionPoint θ t (u • a + v • b) =
      u • traceSectionPoint θ t a + v • traceSectionPoint θ t b := by
    dsimp [traceSectionPoint]
    change t • θ + (u * a + v * b) • quarterTurnNormal θ = _
    calc
      _ = (u + v) • (t • θ) + (u * a + v * b) • quarterTurnNormal θ := by
        rw [huv, one_smul]
      _ = _ := by module
  rw [hid]
  exact key

/-- A nonempty actual section is the compact interval between its extrema. -/
theorem traceSection_eq_Icc {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t : ℝ) (hne : (traceSection θ t).Nonempty) :
    traceSection θ t = Icc (sInf (traceSection θ t)) (sSup (traceSection θ t)) :=
  eq_Icc_of_connected_compact ⟨hne, (convex_traceSection θ t).isPreconnected⟩
    (isCompact_traceSection hθ t)

theorem traceSectionProfile_nonneg (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    0 ≤ traceSectionProfile θ t := by
  apply integral_nonneg
  intro s
  exact Set.indicator_nonneg (fun _ _ ↦ by norm_num) _

theorem traceSectionProfile_eq_integral_indicator (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    traceSectionProfile θ t = ∫ s : ℝ, (traceSection θ t).indicator (fun _ ↦ (1 : ℝ)) s := by
  rfl

/-- The section profile is precisely the one-dimensional Lebesgue length. -/
theorem traceSectionProfile_eq_volume (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    traceSectionProfile θ t = (volume (traceSection θ t)).toReal := by
  rw [traceSectionProfile_eq_integral_indicator]
  exact integral_indicator_one (isClosed_traceSection θ t).measurableSet

/-- Section indicators are integrable, since actual sections are compact. -/
theorem traceSection_indicator_integrable {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t : ℝ) : Integrable ((traceSection θ t).indicator (fun _ ↦ (1 : ℝ))) := by
  exact (integrableOn_const (isCompact_traceSection hθ t).measure_ne_top).integrable_indicator
    (isClosed_traceSection θ t).measurableSet

/-- No section can occur beyond either supporting line of its normal direction. -/
theorem traceSection_eq_empty_of_outside_support {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) {t : ℝ}
    (ht : t ∉ Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ)) :
    traceSection θ t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  apply ht
  have hup := inner_le_traceEuclideanSupportHeight θ (traceSectionPoint θ t s) hs
  have hlo := inner_le_traceEuclideanSupportHeight (-θ) (traceSectionPoint θ t s) hs
  rw [traceSectionPoint_inner_normal hθ] at hup
  rw [inner_neg_right, traceSectionPoint_inner_normal hθ] at hlo
  exact ⟨by linarith, hup⟩

theorem traceSectionProfile_eq_zero_of_outside_support {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) {t : ℝ}
    (ht : t ∉ Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ)) :
    traceSectionProfile θ t = 0 := by
  rw [traceSectionProfile_eq_volume, traceSection_eq_empty_of_outside_support hθ ht]
  simp

/-- Distances along a unit-normal section are ordinary distances of its real coordinates. -/
theorem dist_traceSectionPoint {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t a b : ℝ) : dist (traceSectionPoint θ t a) (traceSectionPoint θ t b) = |a - b| := by
  rw [dist_eq_norm]
  have hd : traceSectionPoint θ t a - traceSectionPoint θ t b =
      (a - b) • quarterTurnNormal θ := by
    dsimp [traceSectionPoint]
    module
  rw [hd, norm_smul, Real.norm_eq_abs, norm_quarterTurnNormal, hθ, mul_one]

/-- A supporting section contains at most one transverse coordinate. -/
theorem traceSection_subsingleton_of_support_value
    {θ n : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) (hn : n ≠ 0) (t : ℝ)
    (ht : ∀ s ∈ traceSection θ t,
      inner ℝ (traceSectionPoint θ t s) n = traceEuclideanSupportHeight n) :
    (traceSection θ t).Subsingleton := by
  intro a ha b hb
  have heq := (traceEuclideanSupportHeight_exists_unique n hn).unique
    ⟨ha, ht a ha⟩ ⟨hb, ht b hb⟩
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ inner ℝ x (quarterTurnNormal θ)) heq
  simpa only [traceSectionPoint_inner_transverse hθ] using hi

/-- The actual section profile vanishes at both supporting endpoints. -/
theorem traceSectionProfile_support_endpoints {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    traceSectionProfile θ (traceEuclideanSupportHeight θ) = 0 ∧
      traceSectionProfile θ (-traceEuclideanSupportHeight (-θ)) = 0 := by
  have hθne : θ ≠ 0 := by intro hz; simp [hz] at hθ
  have hupper := traceSection_subsingleton_of_support_value hθ hθne
    (traceEuclideanSupportHeight θ) (fun _ _ ↦ traceSectionPoint_inner_normal hθ _ _)
  have hlower := traceSection_subsingleton_of_support_value hθ (neg_ne_zero.mpr hθne)
    (-traceEuclideanSupportHeight (-θ)) (fun s _ ↦ by
      rw [inner_neg_right, traceSectionPoint_inner_normal hθ, neg_neg])
  constructor
  · rw [traceSectionProfile_eq_volume, hupper.measure_zero volume, ENNReal.toReal_zero]
  · rw [traceSectionProfile_eq_volume, hlower.measure_zero volume, ENNReal.toReal_zero]

/-- On a nonempty section, the profile is its upper endpoint minus its lower endpoint. -/
theorem traceSectionProfile_eq_length {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t : ℝ) (hne : (traceSection θ t).Nonempty) :
    traceSectionProfile θ t = sSup (traceSection θ t) - sInf (traceSection θ t) := by
  have hcompact := isCompact_traceSection hθ t
  have hordered : sInf (traceSection θ t) ≤ sSup (traceSection θ t) :=
    csInf_le hcompact.bddBelow (hcompact.sSup_mem hne)
  calc
    _ = (volume (traceSection θ t)).toReal := traceSectionProfile_eq_volume θ t
    _ = (volume (Icc (sInf (traceSection θ t)) (sSup (traceSection θ t)))).toReal :=
      congrArg (fun S : Set ℝ ↦ (volume S).toReal) (traceSection_eq_Icc hθ t hne)
    _ = _ := by rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hordered)]

/-- The actual section length is controlled by the diameter of any bounded
set containing all of its section points. -/
theorem traceSectionProfile_le_diam_of_image_subset
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) (t : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : Bornology.IsBounded S)
    (hsub : ∀ s ∈ traceSection θ t, traceSectionPoint θ t s ∈ S) :
    traceSectionProfile θ t ≤ Metric.diam S := by
  by_cases hne : (traceSection θ t).Nonempty
  · have hcompact := isCompact_traceSection hθ t
    have hmin := hcompact.sInf_mem hne
    have hmax := hcompact.sSup_mem hne
    have hdist := Metric.dist_le_diam_of_mem hS (hsub _ hmax) (hsub _ hmin)
    rw [dist_traceSectionPoint hθ, abs_of_nonneg (sub_nonneg.mpr
      (csInf_le hcompact.bddBelow hmax))] at hdist
    rw [traceSectionProfile_eq_length hθ t hne]
    exact hdist
  · have hemp : traceSection θ t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [traceSectionProfile_eq_volume, hemp, measure_empty, ENNReal.toReal_zero]
    exact Metric.diam_nonneg

/-- A section lying within an upper cap has length at most that actual cap diameter. -/
theorem traceSectionProfile_le_cap_diam {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (t d : ℝ) (ht : traceEuclideanSupportHeight θ - d ≤ t) :
    traceSectionProfile θ t ≤ Metric.diam (traceConvexCap θ d) := by
  apply traceSectionProfile_le_diam_of_image_subset hθ t _
    (isCompact_traceEuclideanBall.isBounded.subset (fun _ hx ↦ hx.1))
  intro s hs
  refine ⟨hs, ?_⟩
  simpa only [traceSectionPoint_inner_normal hθ] using ht

/-- The corresponding bound for a lower cap uses the opposite normal direction. -/
theorem traceSectionProfile_le_opposite_cap_diam {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) (t d : ℝ) (ht : traceEuclideanSupportHeight (-θ) - d ≤ -t) :
    traceSectionProfile θ t ≤ Metric.diam (traceConvexCap (-θ) d) := by
  apply traceSectionProfile_le_diam_of_image_subset hθ t _
    (isCompact_traceEuclideanBall.isBounded.subset (fun _ hx ↦ hx.1))
  intro s hs
  refine ⟨hs, ?_⟩
  simpa only [inner_neg_right, traceSectionPoint_inner_normal hθ] using ht

/-- The actual zero-extended section profile is continuous at both supporting endpoints. -/
theorem traceSectionProfile_continuousAt_support_endpoints
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    ContinuousAt (traceSectionProfile θ) (traceEuclideanSupportHeight θ) ∧
      ContinuousAt (traceSectionProfile θ) (-traceEuclideanSupportHeight (-θ)) := by
  have hθne : θ ≠ 0 := by intro hz; simp [hz] at hθ
  constructor
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := traceConvexCap_diam_small hθne
      (show 0 < ε / 2 by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have ht' : |t - traceEuclideanSupportHeight θ| < δ := by
      simpa only [Real.dist_eq] using ht
    rw [(traceSectionProfile_support_endpoints hθ).1, Real.dist_eq, sub_zero,
      abs_of_nonneg (traceSectionProfile_nonneg θ t)]
    have hbound := traceSectionProfile_le_cap_diam hθ t
      (traceEuclideanSupportHeight θ - t) (by linarith)
    exact (hbound.trans (hsmall _ (by linarith [(abs_lt.mp ht').1]))).trans_lt (by linarith)
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := traceConvexCap_diam_small (neg_ne_zero.mpr hθne)
      (show 0 < ε / 2 by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have ht' : |t - (-traceEuclideanSupportHeight (-θ))| < δ := by
      simpa only [Real.dist_eq] using ht
    rw [(traceSectionProfile_support_endpoints hθ).2, Real.dist_eq, sub_zero,
      abs_of_nonneg (traceSectionProfile_nonneg θ t)]
    have hbound := traceSectionProfile_le_opposite_cap_diam hθ t
      (traceEuclideanSupportHeight (-θ) + t) (by linarith)
    exact (hbound.trans (hsmall _ (by linarith [(abs_lt.mp ht').2]))).trans_lt (by linarith)

end Markov
