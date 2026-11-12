import Markov.ModularTraceQuotientMetric
import Markov.HyperbolicDiagonalization
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.LocallyConstant.Basic

/-! Genuine periodic local unit-speed geodesics in the actual hyperbolic
orbit quotient, obtained by projecting invariant hyperbolic axes. No
simplicity, minimal-period, or uniqueness assertion is made. The metric
variation on every increasing parameter interval is its parameter length. -/
noncomputable section
open scoped MatrixGroups ENNReal
open Set Metric Topology
namespace Markov

private theorem modularTraceReal_hyperbolic (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    2 < |((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  have ht : ((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      ((g.val : IntMatrixTwo).trace : ℝ) := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [ht]
  exact_mod_cast hg

/-- The genuine metric translation length of the actual deck matrix. -/
def modularClosedGeodesicPeriod (g : modularTraceSubgroup) : ℝ :=
  hyperbolicTranslationLength (g.val : SL(2, ℝ))

/-- A genuine invariant hyperbolic unit-speed axis, with no conjugacy premise. -/
def modularHyperbolicAxis (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : ℝ → UpperHalfPlane :=
  (hyperbolicTranslationLength_axis (g.val : SL(2, ℝ)) (modularTraceReal_hyperbolic g hg)).choose

theorem modularHyperbolicAxis_isometry (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : Isometry (modularHyperbolicAxis g hg) :=
  (hyperbolicTranslationLength_axis (g.val : SL(2, ℝ)) (modularTraceReal_hyperbolic g hg)).choose_spec.1

theorem modularHyperbolicAxis_action (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (t : ℝ) :
    g • modularHyperbolicAxis g hg t =
      modularHyperbolicAxis g hg (t + modularClosedGeodesicPeriod g) := by
  change g.val • modularHyperbolicAxis g hg t = _
  rw [modularInteger_smul_eq_real]
  exact (hyperbolicTranslationLength_axis (g.val : SL(2, ℝ))
    (modularTraceReal_hyperbolic g hg)).choose_spec.2 t

theorem modularClosedGeodesicPeriod_pos (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : 0 < modularClosedGeodesicPeriod g :=
  hyperbolicTranslationLength_pos _ (modularTraceReal_hyperbolic g hg)

/-- Projection of the actual invariant axis into the actual metric orbit quotient. -/
def modularClosedGeodesic (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (t : ℝ) : ModularTraceQuotient :=
  modularTraceQuotientMk (modularHyperbolicAxis g hg t)

theorem modularClosedGeodesic_periodic (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Function.Periodic (modularClosedGeodesic g hg) (modularClosedGeodesicPeriod g) := by
  intro t
  change modularTraceQuotientMk (modularHyperbolicAxis g hg (t + _)) = _
  rw [← modularHyperbolicAxis_action g hg t, modularTraceQuotientMk_smul]
  rfl

theorem modularClosedGeodesic_continuous (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : Continuous (modularClosedGeodesic g hg) :=
  modularTraceQuotientMk_continuous.comp (modularHyperbolicAxis_isometry g hg).continuous

theorem modularClosedGeodesic_lipschitz (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : LipschitzWith 1 (modularClosedGeodesic g hg) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [NNReal.coe_one, one_mul] using
    (modularTraceQuotientMk_dist_le (modularHyperbolicAxis g hg s) (modularHyperbolicAxis g hg t)).trans_eq
      ((modularHyperbolicAxis_isometry g hg).dist_eq s t)

/-- The actual projected axis is unit-speed and distance-preserving on a
real neighborhood of each parameter. -/
theorem modularClosedGeodesic_local_dist_eq (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (t : ℝ) :
    ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (modularClosedGeodesic g hg s) (modularClosedGeodesic g hg u) = dist s u := by
  obtain ⟨r, hr, heq⟩ := modularTraceQuotientMk_local_dist_eq (modularHyperbolicAxis g hg t)
  refine ⟨r, hr, ?_⟩
  intro s hs u hu
  change dist (modularTraceQuotientMk (modularHyperbolicAxis g hg s))
    (modularTraceQuotientMk (modularHyperbolicAxis g hg u)) = _
  rw [heq, (modularHyperbolicAxis_isometry g hg).dist_eq]
  · simpa only [Metric.mem_ball, (modularHyperbolicAxis_isometry g hg).dist_eq] using hs
  · simpa only [Metric.mem_ball, (modularHyperbolicAxis_isometry g hg).dist_eq] using hu

private theorem eVariationOn_le_sub_of_one_lipschitz {E : Type*} [PseudoMetricSpace E]
    (c : ℝ → E) (hc : LipschitzWith 1 c) (a b : ℝ) :
    eVariationOn c (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hcomp := hc.lipschitzOnWith.comp_eVariationOn_le
    (g := (id : ℝ → ℝ)) (s := Icc a b) (mapsTo_univ _ _)
  have hle : eVariationOn c (Icc a b) ≤ eVariationOn (id : ℝ → ℝ) (Icc a b) := by
    simpa only [Function.comp_id, ENNReal.coe_one, one_mul] using hcomp
  have hid : eVariationOn (id : ℝ → ℝ) (Icc a b) ≤ ENNReal.ofReal (b - a) := by
    simpa only [univ_inter, id_eq] using
      (@monotoneOn_id ℝ _ univ).eVariationOn_le (a := a) (b := b) (by trivial) (by trivial)
  exact hle.trans hid

private theorem variation_eq_sub_of_one_lipschitz_of_dist {E : Type*} [PseudoMetricSpace E]
    (c : ℝ → E) (hc : LipschitzWith 1 c) (a b : ℝ) (hab : a ≤ b)
    (hd : dist (c a) (c b) = b - a) : variationOnFromTo c univ a b = b - a := by
  have hlo := eVariationOn.edist_le c (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [edist_dist, hd] at hlo
  have heq : eVariationOn c (Icc a b) = ENNReal.ofReal (b - a) :=
    le_antisymm (eVariationOn_le_sub_of_one_lipschitz c hc a b) hlo
  rw [variationOnFromTo.eq_of_le c univ hab, univ_inter, heq,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- A globally nonexpanding, locally unit-speed curve has its actual metric
variation equal to parameter length. The proof uses additivity of variation
and connectedness, so no uniform injectivity radius is assumed. -/
theorem variation_eq_sub_of_local_unit_speed {E : Type*} [PseudoMetricSpace E]
    (c : ℝ → E) (hc : LipschitzWith 1 c)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (c s) (c u) = dist s u) (a b : ℝ) :
    variationOnFromTo c univ a b = b - a := by
  have hvar := hc.locallyBoundedVariationOn univ
  have hconst : IsLocallyConstant (fun t : ℝ => variationOnFromTo c univ 0 t - t) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro t
    obtain ⟨r, hr, heq⟩ := hloc t
    refine ⟨Metric.ball t r, isOpen_ball, mem_ball_self hr, ?_⟩
    intro u hu
    rcases le_total u t with hut | htu
    · have hd : dist (c u) (c t) = t - u := by
        rw [heq u hu t (mem_ball_self hr), Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hut)]
        ring
      have hv := variation_eq_sub_of_one_lipschitz_of_dist c hc u t hut hd
      have hadd := variationOnFromTo.add hvar (a := 0) (b := u) (c := t)
        (by trivial) (by trivial) (by trivial)
      linarith
    · have hd : dist (c t) (c u) = u - t := by
        rw [heq t (mem_ball_self hr) u hu, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr htu)]
        ring
      have hv := variation_eq_sub_of_one_lipschitz_of_dist c hc t u htu hd
      have hadd := variationOnFromTo.add hvar (a := 0) (b := t) (c := u)
        (by trivial) (by trivial) (by trivial)
      linarith
  have heq := hconst.apply_eq_of_preconnectedSpace b a
  have hadd := variationOnFromTo.add hvar (a := 0) (b := a) (c := b)
    (by trivial) (by trivial) (by trivial)
  linarith

/-- The metric variation over any increasing parameter interval is its
ordinary real length. In particular this applies to a full closed period. -/
theorem modularClosedGeodesic_eVariation (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (modularClosedGeodesic g hg) (Icc a b) = ENNReal.ofReal (b - a) := by
  have hv := variation_eq_sub_of_local_unit_speed (modularClosedGeodesic g hg)
    (modularClosedGeodesic_lipschitz g hg) (modularClosedGeodesic_local_dist_eq g hg) a b
  rw [variationOnFromTo.eq_of_le _ univ hab, univ_inter] at hv
  have hfinite : eVariationOn (modularClosedGeodesic g hg) (Icc a b) ≠ ∞ :=
    ne_of_lt ((eVariationOn_le_sub_of_one_lipschitz _ (modularClosedGeodesic_lipschitz g hg) a b).trans_lt
      ENNReal.ofReal_lt_top)
  calc
    _ = ENNReal.ofReal (eVariationOn (modularClosedGeodesic g hg) (Icc a b)).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = _ := congrArg ENNReal.ofReal hv

/-- The genuine metric length of one displayed period equals the actual
hyperbolic translation length of the deck matrix. -/
theorem modularClosedGeodesic_period_length (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    (eVariationOn (modularClosedGeodesic g hg) (Icc 0 (modularClosedGeodesicPeriod g))).toReal =
      modularClosedGeodesicPeriod g := by
  rw [modularClosedGeodesic_eVariation g hg 0 _ (modularClosedGeodesicPeriod_pos g hg).le,
    sub_zero, ENNReal.toReal_ofReal (modularClosedGeodesicPeriod_pos g hg).le]

/-- The actual lifted full-period endpoint is the specified deck transform. -/
theorem modularHyperbolicAxis_period_endpoint (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    modularHyperbolicAxis g hg (modularClosedGeodesicPeriod g) =
      g • modularHyperbolicAxis g hg 0 := by
  simpa only [zero_add] using (modularHyperbolicAxis_action g hg 0).symm

/-- The genuine lifted axis segment, with its actual deck-transformed endpoint. -/
def modularHyperbolicAxisSegment (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path (modularHyperbolicAxis g hg 0) (g • modularHyperbolicAxis g hg 0) where
  toFun t := modularHyperbolicAxis g hg ((t : ℝ) * modularClosedGeodesicPeriod g)
  continuous_toFun := (modularHyperbolicAxis_isometry g hg).continuous.comp
    (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simpa using modularHyperbolicAxis_period_endpoint g hg

/-- The actual closed loop obtained by traversing one displayed period. -/
def modularClosedGeodesicLoop (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path (modularClosedGeodesic g hg 0) (modularClosedGeodesic g hg 0) where
  toFun t := modularClosedGeodesic g hg ((t : ℝ) * modularClosedGeodesicPeriod g)
  continuous_toFun := (modularClosedGeodesic_continuous g hg).comp
    (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simpa using modularClosedGeodesic_periodic g hg 0

/-- The constructed loop really is the projection of the displayed lifted axis segment. -/
theorem modularClosedGeodesicLoop_lift (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (t : unitInterval) :
    modularTraceQuotientMk (modularHyperbolicAxisSegment g hg t) =
      modularClosedGeodesicLoop g hg t := rfl

/-- The full-period metric length has the genuine hyperbolic trace formula. -/
theorem modularClosedGeodesicPeriod_trace (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    modularClosedGeodesicPeriod g = 2 * Real.arcosh (|((g.val : IntMatrixTwo).trace : ℝ)| / 2) := by
  have ht : ((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      ((g.val : IntMatrixTwo).trace : ℝ) := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [modularClosedGeodesicPeriod, hyperbolicTranslationLength_trace _
    (modularTraceReal_hyperbolic g hg), ht]

end Markov
