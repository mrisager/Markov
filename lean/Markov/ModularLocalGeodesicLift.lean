import Markov.ModularClosedGeodesic
import Markov.HyperbolicLocalStraightening
import Markov.ModularAxisUniqueness
import Markov.IsometricAxisPeriod

/-! Actual local unit-speed quotient curves and their continuous covering
lifts. A forward period is labelled by its literal endpoint g • F(0), without
changing the marked fundamental-group inverse convention. No simplicity or
primitive simple-class classification is asserted. -/

noncomputable section
open Set Metric
open scoped MatrixGroups
namespace Markov

/-- A continuous actual covering lift of a locally unit-speed quotient curve
preserves distances on sufficiently small real parameter neighborhoods. -/
theorem modularTraceQuotientLift_locally_unit_speed
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u) :
    ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (F s) (F u) = dist s u := by
  intro t
  obtain ⟨R, hR, hquot⟩ := modularTraceQuotientMk_local_dist_eq (F t)
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hF.continuousAt) R hR
  obtain ⟨r, hr, hmetric⟩ := hloc t
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro s hs u hu
  have hsF : F s ∈ Metric.ball (F t) R :=
    hnear (lt_of_lt_of_le hs (min_le_left δ r))
  have huF : F u ∈ Metric.ball (F t) R :=
    hnear (lt_of_lt_of_le hu (min_le_left δ r))
  rw [← hquot (F s) hsF (F u) huF, hproj s, hproj u]
  exact hmetric s (lt_of_lt_of_le hs (min_le_right δ r))
    u (lt_of_lt_of_le hu (min_le_right δ r))

/-- Such an actual continuous lift is globally isometric in the genuine
upper-half-plane metric, by the proved local-to-global straightening. -/
theorem modularTraceQuotientLift_isometry
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u) : Isometry F :=
  upperHalfPlane_isometry_of_locally_unit_speed F
    (modularTraceQuotientLift_locally_unit_speed γ F hF hproj hloc)

/-- The literal forward endpoint of one actual lifted period determines its
deck equivariance along the entire continuous lift, by covering uniqueness. -/
theorem modularTraceQuotientLift_deck_action_of_period
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (P : ℝ) (hperiod : Function.Periodic γ P) (g : modularTraceSubgroup)
    (hendpoint : F P = g • F 0) :
    ∀ t : ℝ, g • F t = F (t + P) := by
  have h₁ : Continuous (fun t : ℝ => g • F t) :=
    (modularTraceSubgroup_isometry g).continuous.comp hF
  have h₂ : Continuous (fun t : ℝ => F (t + P)) :=
    hF.comp (continuous_id.add continuous_const)
  have hcomp : modularTraceQuotientMk ∘ (fun t : ℝ => g • F t) =
      modularTraceQuotientMk ∘ (fun t : ℝ => F (t + P)) := by
    funext t
    exact (modularTraceQuotientMk_smul g (F t)).trans
      ((hproj t).trans ((hperiod t).symm.trans (hproj (t + P)).symm))
  have he := modularTraceQuotientMk_isCoveringMap.eq_of_comp_eq h₁ h₂ hcomp 0
    (by simpa only [zero_add] using hendpoint.symm)
  exact congrFun he

/-- The positive parameter period of an actual local unit-speed quotient
curve equals the genuine translation length of its literal forward deck label.
No trace/hyperbolicity or length-equality assumption is used. -/
theorem modularTraceQuotientLift_period_eq_translationLength
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u)
    (P : ℝ) (hP : 0 < P) (hperiod : Function.Periodic γ P)
    (g : modularTraceSubgroup) (hendpoint : F P = g • F 0) :
    modularClosedGeodesicPeriod g = P := by
  apply hyperbolicTranslationLength_eq_invariantIsometricAxis_period (g.val : SL(2, ℝ)) F
    (modularTraceQuotientLift_isometry γ F hF hproj hloc) P hP
  intro t
  simpa only [← modularInteger_smul_eq_real] using
    modularTraceQuotientLift_deck_action_of_period γ F hF hproj P hperiod g hendpoint t

/-- With an actual hyperbolic forward deck label, the entire actual quotient
curve is the existing selected closed axis with a real parameter shift. -/
theorem modularTraceQuotientLift_eq_closedGeodesic
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u)
    (P : ℝ) (hP : 0 < P) (hperiod : Function.Periodic γ P)
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hendpoint : F P = g • F 0) :
    ∃ c : ℝ, ∀ t : ℝ, γ t = modularClosedGeodesic g hg (t + c) := by
  have hlen := modularTraceQuotientLift_period_eq_translationLength γ F hF hproj hloc
    P hP hperiod g hendpoint
  have hact : ∀ t : ℝ, g • F t = F (t + modularClosedGeodesicPeriod g) := by
    rw [hlen]
    exact modularTraceQuotientLift_deck_action_of_period γ F hF hproj P hperiod g hendpoint
  obtain ⟨c, hc⟩ := modularHyperbolicAxis_eq_of_isometry_equivariant g hg F
    (modularTraceQuotientLift_isometry γ F hF hproj hloc) hact
  refine ⟨-c, ?_⟩
  intro t
  have haxis : F t = modularHyperbolicAxis g hg (t - c) := by
    simpa only [sub_add_cancel] using (hc (t - c)).symm
  rw [← hproj t]
  change modularTraceQuotientMk (F t) =
    modularTraceQuotientMk (modularHyperbolicAxis g hg (t + -c))
  rw [haxis, sub_eq_add_neg]

end Markov
