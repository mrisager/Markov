import Markov.ModularClosedGeodesic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Uniform axis bounds and properness for actual equivariant curves. Compact
period reduction is supplied by the pinned actual periodic-function theorem.
No injectivity, separation, or simplicity of the curve is assumed or concluded. -/

noncomputable section
open Set Metric Topology
namespace Markov

/-- Distances between two curves with the same actual isometric period law are periodic. -/
theorem equivariant_curves_distance_periodic {E : Type*} [PseudoMetricSpace E]
    (S : E → E) (hS : Isometry S) (γ α : ℝ → E) (L : ℝ)
    (hγ : ∀ t, γ (t+L) = S (γ t)) (hα : ∀ t, α (t+L) = S (α t)) :
    Function.Periodic (fun t => dist (γ t) (α t)) L := by
  intro t
  change dist (γ (t+L)) (α (t+L)) = dist (γ t) (α t)
  rw [hγ, hα]
  exact hS.dist_eq _ _

/-- Actual continuity and compact period reduction bound the matching-point distance globally. -/
theorem equivariant_curves_uniform_distance {E : Type*} [PseudoMetricSpace E]
    (S : E → E) (hS : Isometry S) (γ α : ℝ → E) (L : ℝ) (hL : L ≠ 0)
    (hcγ : Continuous γ) (hcα : Continuous α)
    (hγ : ∀ t, γ (t+L) = S (γ t)) (hα : ∀ t, α (t+L) = S (α t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, dist (γ t) (α t) ≤ C := by
  have hp := equivariant_curves_distance_periodic S hS γ α L hγ hα
  have hk := hp.compact_of_continuous hL (hcγ.dist hcα)
  rcases hk.bddAbove with ⟨C, hC⟩
  refine ⟨C, (dist_nonneg : 0 ≤ dist (γ 0) (α 0)).trans (hC (mem_range_self 0)), ?_⟩
  intro t
  exact hC (mem_range_self t)

/-- A continuous curve uniformly close to a positive-speed isometric line is
proper. The proof bounds every compact preimage inside an actual real closed ball. -/
theorem isProperMap_of_uniform_distance_to_scaled_isometry
    {E : Type*} [MetricSpace E] (γ α : ℝ → E) (hcγ : Continuous γ)
    (κ : ℝ) (hκ : 0 < κ)
    (hα : ∀ s t, dist (α s) (α t) = κ * dist s t)
    (C : ℝ) (hC : ∀ t, dist (γ t) (α t) ≤ C) : IsProperMap γ := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcγ, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (γ 0)
  apply (isCompact_closedBall (0 : ℝ) ((2*C+R)/κ)).of_isClosed_subset
    (hK.isClosed.preimage hcγ)
  intro t ht
  have htR : dist (γ t) (γ 0) ≤ R := hR ht
  have ht1 := dist_triangle (α t) (γ t) (α 0)
  have ht2 := dist_triangle (γ t) (γ 0) (α 0)
  rw [dist_comm (α t) (γ t), hα t 0] at ht1
  change dist t 0 ≤ (2*C+R)/κ
  apply (le_div_iff₀ hκ).mpr
  nlinarith [hC t, hC 0]

/-- In particular, any continuous curve with the same actual isometric period
law as an isometric real line is proper. -/
theorem equivariant_curve_isProperMap_of_isometric_axis
    {E : Type*} [MetricSpace E] (S : E → E) (hS : Isometry S)
    (γ α : ℝ → E) (hcγ : Continuous γ) (hαiso : Isometry α)
    (L : ℝ) (hL : L ≠ 0)
    (hγ : ∀ t, γ (t+L) = S (γ t)) (hα : ∀ t, α (t+L) = S (α t)) :
    IsProperMap γ := by
  obtain ⟨C, _, hC⟩ := equivariant_curves_uniform_distance S hS γ α L hL
    hcγ hαiso.continuous hγ hα
  apply isProperMap_of_uniform_distance_to_scaled_isometry γ α hcγ 1 (by norm_num) _ C hC
  intro s t
  simpa only [one_mul] using hαiso.dist_eq s t

/-- The checked actual invariant axis rescaled to match an arbitrary positive
curve period L. Its speed is the actual translation length divided by L. -/
def modularEquivariantComparisonAxis (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) : ℝ → UpperHalfPlane :=
  fun t => modularHyperbolicAxis g hg (t * (modularClosedGeodesicPeriod g / L))

theorem modularEquivariantComparisonAxis_continuous (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) :
    Continuous (modularEquivariantComparisonAxis g hg L) :=
  (modularHyperbolicAxis_isometry g hg).continuous.comp (continuous_id.mul continuous_const)

/-- The rescaled actual axis has exactly the same actual deck/period law. -/
theorem modularEquivariantComparisonAxis_period (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    modularEquivariantComparisonAxis g hg L (t+L) =
      g • modularEquivariantComparisonAxis g hg L t := by
  unfold modularEquivariantComparisonAxis
  rw [modularHyperbolicAxis_action]
  congr 1
  field_simp

theorem modularEquivariantComparisonAxis_dist (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) (hL : 0 < L) (s t : ℝ) :
    dist (modularEquivariantComparisonAxis g hg L s) (modularEquivariantComparisonAxis g hg L t) =
      (modularClosedGeodesicPeriod g / L) * dist s t := by
  unfold modularEquivariantComparisonAxis
  rw [(modularHyperbolicAxis_isometry g hg).dist_eq]
  simp only [Real.dist_eq]
  rw [← sub_mul, abs_mul, abs_of_pos (div_pos (modularClosedGeodesicPeriod_pos g hg) hL)]
  ring

/-- Every actual continuous hyperbolic-deck-equivariant curve stays a uniform
finite distance from the matching-parameter actual rescaled axis. -/
theorem modularEquivariantCurve_uniform_distance (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) (hL : 0 < L)
    (γ : ℝ → UpperHalfPlane) (hcγ : Continuous γ)
    (hγ : ∀ t, γ (t+L) = g • γ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, dist (γ t) (modularEquivariantComparisonAxis g hg L t) ≤ C := by
  exact equivariant_curves_uniform_distance (fun z => g • z) (modularTraceSubgroup_isometry g)
    γ (modularEquivariantComparisonAxis g hg L) L hL.ne' hcγ
    (modularEquivariantComparisonAxis_continuous g hg L) hγ
    (modularEquivariantComparisonAxis_period g hg L hL)

/-- Such an actual equivariant curve is proper, with no assumption that it is
simple or embedded. Hyperbolicity supplies the positive comparison speed. -/
theorem modularEquivariantCurve_isProperMap (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (L : ℝ) (hL : 0 < L)
    (γ : ℝ → UpperHalfPlane) (hcγ : Continuous γ)
    (hγ : ∀ t, γ (t+L) = g • γ t) : IsProperMap γ := by
  obtain ⟨C, _, hC⟩ := modularEquivariantCurve_uniform_distance g hg L hL γ hcγ hγ
  exact isProperMap_of_uniform_distance_to_scaled_isometry γ
    (modularEquivariantComparisonAxis g hg L) hcγ (modularClosedGeodesicPeriod g / L)
    (div_pos (modularClosedGeodesicPeriod_pos g hg) hL)
    (modularEquivariantComparisonAxis_dist g hg L hL) C hC

end Markov
