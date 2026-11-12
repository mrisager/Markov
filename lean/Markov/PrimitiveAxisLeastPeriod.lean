import Markov.ModularH1Transport
import Markov.RealCurvePeriodGenerator
import Markov.PrimitiveHolonomyNoProperPower

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The actual projected unit-speed axis is locally injective, even when
its full closed image has self-intersections. -/
theorem modularClosedGeodesic_isLocallyInjective (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    IsLocallyInjective (modularClosedGeodesic g hg) := by
  intro t
  obtain ⟨r, hr, heq⟩ := modularClosedGeodesic_local_dist_eq g hg t
  refine ⟨Metric.ball t r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
  intro s hs u hu hsu
  apply dist_eq_zero.mp
  rw [← heq s hs u hu, hsu, dist_self]

/-- An actual period of the projected axis lifts to a single genuine deck
transform, valid along the whole invariant axis. -/
theorem modularHyperbolicAxis_deck_of_period (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (T : ℝ)
    (hT : Function.Periodic (modularClosedGeodesic g hg) T) :
    ∃ h : modularTraceSubgroup, ∀ t : ℝ,
      h • modularHyperbolicAxis g hg t = modularHyperbolicAxis g hg (t + T) := by
  obtain ⟨h, hh⟩ := (modularTraceQuotientMk_eq_iff
    (modularHyperbolicAxis g hg T) (modularHyperbolicAxis g hg 0)).mp (by
      simpa only [modularClosedGeodesic, zero_add] using hT 0)
  refine ⟨h, ?_⟩
  have h₁ : Continuous (fun t : ℝ => h • modularHyperbolicAxis g hg t) :=
    (modularTraceSubgroup_isometry h).continuous.comp
      (modularHyperbolicAxis_isometry g hg).continuous
  have h₂ : Continuous (fun t : ℝ => modularHyperbolicAxis g hg (t + T)) :=
    (modularHyperbolicAxis_isometry g hg).continuous.comp (continuous_id.add continuous_const)
  have hcomp : modularTraceQuotientMk ∘ (fun t : ℝ => h • modularHyperbolicAxis g hg t) =
      modularTraceQuotientMk ∘ (fun t : ℝ => modularHyperbolicAxis g hg (t + T)) := by
    funext t
    exact (modularTraceQuotientMk_smul h _).trans (hT t).symm
  have he := modularTraceQuotientMk_isCoveringMap.eq_of_comp_eq h₁ h₂ hcomp 0
    (by simpa only [zero_add] using hh)
  exact congrFun he

/-- Iterating the actual period deck transform shifts the invariant axis
by the corresponding positive integral multiple. -/
theorem modularHyperbolicAxis_pow_action (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (T : ℝ) (h : modularTraceSubgroup)
    (hh : ∀ t : ℝ, h • modularHyperbolicAxis g hg t =
      modularHyperbolicAxis g hg (t + T)) (n : ℕ) (t : ℝ) :
    h ^ n • modularHyperbolicAxis g hg t =
      modularHyperbolicAxis g hg (t + (n : ℝ) * T) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, hh]
      congr 1
      push_cast
      ring

/-- Divisibility of actual real periods gives a genuine power identity
of deck matrices, by freeness of the proved covering action. -/
theorem modularHyperbolicAxis_power_of_period_multiple (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (T : ℝ)
    (hT : Function.Periodic (modularClosedGeodesic g hg) T) (n : ℕ)
    (hn : modularClosedGeodesicPeriod g = (n : ℝ) * T) :
    ∃ h : modularTraceSubgroup, h ^ n = g := by
  obtain ⟨h, hh⟩ := modularHyperbolicAxis_deck_of_period g hg T hT
  refine ⟨h, IsCancelSMul.right_cancel _ _ (modularHyperbolicAxis g hg 0) ?_⟩
  rw [modularHyperbolicAxis_pow_action g hg T h hh, ← hn,
    ← modularHyperbolicAxis_action g hg]

/-- An actual displayed axis period is the least positive real period if
its actual deck matrix is not a proper natural power. -/
theorem modularClosedGeodesic_period_isLeast_of_noProperPower (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hprimitive : ∀ (h : modularTraceSubgroup) (n : ℕ), h ^ n = g → n = 1) :
    IsLeast {T : ℝ | Function.Periodic (modularClosedGeodesic g hg) T ∧ 0 < T}
      (modularClosedGeodesicPeriod g) ∧
    realCurvePeriodSubgroup (modularClosedGeodesic g hg) =
      AddSubgroup.zmultiples (modularClosedGeodesicPeriod g) := by
  obtain ⟨T0, hT0, hper, hmin, hgen, n, _hn, hnL⟩ :=
    realCurvePeriodGenerator_of_isLocallyInjective (modularClosedGeodesic g hg)
      (modularClosedGeodesic_isLocallyInjective g hg)
      (modularClosedGeodesicPeriod_pos g hg) (modularClosedGeodesic_periodic g hg)
  obtain ⟨h, hh⟩ := modularHyperbolicAxis_power_of_period_multiple g hg T0 hper n hnL
  have hn1 : n = 1 := hprimitive h n hh
  have hLT0 : modularClosedGeodesicPeriod g = T0 := by simpa only [hn1, Nat.cast_one, one_mul] using hnL
  refine ⟨⟨⟨modularClosedGeodesic_periodic g hg, modularClosedGeodesicPeriod_pos g hg⟩, ?_⟩, ?_⟩
  · intro T hT
    rw [hLT0]
    exact hmin T hT.2 hT.1
  · simpa only [hLT0] using hgen

/-- Primitive actual marked integral coordinates forbid proper deck powers,
and therefore give the genuine least positive period. -/
theorem modularClosedGeodesic_period_isLeast_of_primitive_coordinates (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hp : IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2) :
    IsLeast {T : ℝ | Function.Periodic (modularClosedGeodesic g hg) T ∧ 0 < T}
      (modularClosedGeodesicPeriod g) ∧
    realCurvePeriodSubgroup (modularClosedGeodesic g hg) =
      AddSubgroup.zmultiples (modularClosedGeodesicPeriod g) := by
  apply modularClosedGeodesic_period_isLeast_of_noProperPower g hg
  intro h n he
  apply primitiveDirection_nat_smul_eq_one hp
  rw [← he, paperTraceAbelianizationCoordinates_pow_toAdd]

/-- Primitivity in the single fixed-I actual singular-H1 marking is enough
for least positive period, without a simple-curve assumption. -/
theorem modularClosedGeodesic_period_isLeast_of_primitive_fixedSingularCoordinates
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hp : IsCoprime
      (modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (modularClosedGeodesicLoop g hg))).1
      (modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (modularClosedGeodesicLoop g hg))).2) :
    IsLeast {T : ℝ | Function.Periodic (modularClosedGeodesic g hg) T ∧ 0 < T}
      (modularClosedGeodesicPeriod g) ∧
    realCurvePeriodSubgroup (modularClosedGeodesic g hg) =
      AddSubgroup.zmultiples (modularClosedGeodesicPeriod g) := by
  apply modularClosedGeodesic_period_isLeast_of_primitive_coordinates g hg
  simpa only [modularClosedGeodesicLoop_fixedSingularCoordinates] using hp

/-- The canonical primitive projected hyperbolic axis has its genuine
least positive real period equal to the original primitive trace length. -/
theorem paperPrimitiveClosedGeodesic_period_isLeast (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    IsLeast {T : ℝ | Function.Periodic (paperPrimitiveClosedGeodesic k p hp) T ∧ 0 < T}
      (primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp) := by
  rw [← paperPrimitiveHolonomy_period k p hp]
  exact (modularClosedGeodesic_period_isLeast_of_noProperPower
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)
    (fun h n he => paperPrimitiveHolonomy_pow_eq_one k p hp h n he.symm)).1

/-- Every positive real period of the actual canonical closed geodesic is
at least its primitive length. -/
theorem paperPrimitiveClosedGeodesic_least_period (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (T : ℝ) (hT : 0 < T) (hper : Function.Periodic (paperPrimitiveClosedGeodesic k p hp) T) :
    primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantCoordinates k p) hp ≤ T :=
  (paperPrimitiveClosedGeodesic_period_isLeast k p hp).2 ⟨hper, hT⟩

/-- All real periods of the actual canonical projected axis are exactly
the integral multiples of the original primitive trace length. -/
theorem paperPrimitiveClosedGeodesic_periodSubgroup (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    realCurvePeriodSubgroup (paperPrimitiveClosedGeodesic k p hp) =
      AddSubgroup.zmultiples
        (primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
          (quadrantCoordinates k p) hp) := by
  rw [← paperPrimitiveHolonomy_period k p hp]
  exact (modularClosedGeodesic_period_isLeast_of_noProperPower
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)
    (fun h n he => paperPrimitiveHolonomy_pow_eq_one k p hp h n he.symm)).2

end Markov
