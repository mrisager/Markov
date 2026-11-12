import Markov.TracePlane
import Markov.RadialLipschitz
import Markov.FareyScale
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Euclidean variation bounds for the actual algebraic trace unit section.
The Euclidean coordinate map is explicit and continuous. Farey denominator
estimates are used only under stated determinant and cutoff assumptions. -/

noncomputable section
open scoped NNReal ENNReal
namespace Markov

/-- Continuous Euclidean coordinates for the constructed trace normed plane. -/
def traceEuclideanEquiv : TracePlane ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := by
  letI : FiniteDimensional ℝ TracePlane := traceBasis.finiteDimensional_of_finite
  exact (traceBasis.equivFun.trans (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm).toContinuousLinearEquiv

def traceEuclideanCoordinates : TracePlane →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  traceEuclideanEquiv.toContinuousLinearMap

theorem traceEuclideanCoordinates_apply (x : TracePlane) (i : Fin 2) :
    traceEuclideanCoordinates x i = traceBasis.equivFun x i := rfl

@[simp] theorem traceEuclideanCoordinates_basis (i : Fin 2) :
    traceEuclideanCoordinates (traceBasis i) = EuclideanSpace.single i 1 := by
  ext j
  rw [traceEuclideanCoordinates_apply, Module.Basis.equivFun_self]
  simp only [EuclideanSpace.single_apply]
  split_ifs <;> simp_all

/-- A single positive denominator bound on the whole parameter interval. -/
def traceRadialLowerBound : ℝ :=
  Classical.choose (radialBasisSection_exists_norm_lower_bound traceBasis)

theorem traceRadialLowerBound_pos : 0 < traceRadialLowerBound :=
  (Classical.choose_spec (radialBasisSection_exists_norm_lower_bound traceBasis)).1

theorem traceRadialLowerBound_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    traceRadialLowerBound ≤ ‖traceBasis 0 + t • traceBasis 1‖ :=
  (Classical.choose_spec (radialBasisSection_exists_norm_lower_bound traceBasis)).2 t ht

/-- The trace unit section viewed in the standard Euclidean coordinate metric. -/
def traceEuclideanRadialSection : ℝ → EuclideanSpace ℝ (Fin 2) :=
  traceEuclideanCoordinates ∘ radialBasisSection traceBasis

def traceEuclideanArcConstant : ℝ≥0 :=
  ‖traceEuclideanCoordinates‖₊ *
    radialSectionLipschitzConstant traceBasis traceRadialLowerBound traceRadialLowerBound_pos

theorem traceEuclideanRadialSection_lipschitzOnWith :
    LipschitzOnWith traceEuclideanArcConstant traceEuclideanRadialSection (Set.Icc (0 : ℝ) 1) :=
  radialBasisSection_target_lipschitzOnWith traceBasis traceEuclideanCoordinates _
    traceRadialLowerBound traceRadialLowerBound_pos traceRadialLowerBound_le

/-- Euclidean metric variation is bounded by the parameter length. -/
theorem traceEuclideanRadialSection_eVariationOn_le (a b : ℝ)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ 1) :
    eVariationOn traceEuclideanRadialSection (Set.Icc a b) ≤
      ENNReal.ofReal ((traceEuclideanArcConstant : ℝ) * (b - a)) := by
  rw [ENNReal.ofReal_mul (p := (traceEuclideanArcConstant : ℝ)) (q := b - a)
    traceEuclideanArcConstant.property, ENNReal.ofReal_coe_nnreal]
  apply radialBasisSection_target_eVariationOn_le traceBasis traceEuclideanCoordinates
    a b traceRadialLowerBound traceRadialLowerBound_pos
  intro t ht
  exact traceRadialLowerBound_le t ⟨ha.trans ht.1, ht.2.trans hb⟩

theorem traceEuclideanRadialSection_variation_le (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (eVariationOn traceEuclideanRadialSection (Set.Icc a b)).toReal ≤
      (traceEuclideanArcConstant : ℝ) * (b - a) := by
  have h := traceEuclideanRadialSection_eVariationOn_le a b ha hab hb
  exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg traceEuclideanArcConstant.property (sub_nonneg.mpr hab)))

/-- A real constant with the uniform Euclidean arc-variation property. -/
theorem traceEuclideanRadialSection_exists_arc_constant :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      eVariationOn traceEuclideanRadialSection (Set.Icc a b) ≤ ENNReal.ofReal (K * (b - a)) :=
  ⟨traceEuclideanArcConstant, traceEuclideanArcConstant.property,
    traceEuclideanRadialSection_eVariationOn_le⟩

/-- Determinant-one slopes satisfying the explicit cutoff denominator
condition have the required Euclidean variation scale. -/
theorem traceEuclideanRadialSection_farey_eVariationOn_le (p q r s H : ℝ)
    (hp : 0 < p) (hr : 0 < r) (hH : 0 < H) (hcutoff : H < p + r)
    (hdet : |p * s - q * r| = 1)
    (hq : q / p ∈ Set.Icc (0 : ℝ) 1) (hs : s / r ∈ Set.Icc (0 : ℝ) 1) :
    eVariationOn traceEuclideanRadialSection (Set.Icc (min (q / p) (s / r)) (max (q / p) (s / r))) ≤
      ENNReal.ofReal (2 * (traceEuclideanArcConstant : ℝ) / (H * min p r)) := by
  have hgap := farey_slope_gap_le_scale p q r s H hp hr hH hcutoff hdet
  have hnum := mul_le_mul_of_nonneg_left hgap traceEuclideanArcConstant.property
  have hwidth : max (q / p) (s / r) - min (q / p) (s / r) = |q / p - s / r| := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
  calc
    eVariationOn traceEuclideanRadialSection
        (Set.Icc (min (q / p) (s / r)) (max (q / p) (s / r))) ≤
        ENNReal.ofReal ((traceEuclideanArcConstant : ℝ) *
          (max (q / p) (s / r) - min (q / p) (s / r))) :=
      traceEuclideanRadialSection_eVariationOn_le _ _ (le_min hq.1 hs.1) (min_le_max)
        (max_le hq.2 hs.2)
    _ ≤ ENNReal.ofReal (2 * (traceEuclideanArcConstant : ℝ) / (H * min p r)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (traceEuclideanArcConstant : ℝ) * (max (q / p) (s / r) - min (q / p) (s / r)) =
            (traceEuclideanArcConstant : ℝ) * |q / p - s / r| := by rw [hwidth]
        _ ≤ (traceEuclideanArcConstant : ℝ) * (2 / (H * min p r)) := hnum
        _ = 2 * (traceEuclideanArcConstant : ℝ) / (H * min p r) := by ring

theorem traceEuclideanRadialSection_farey_variation_le (p q r s H : ℝ)
    (hp : 0 < p) (hr : 0 < r) (hH : 0 < H) (hcutoff : H < p + r)
    (hdet : |p * s - q * r| = 1)
    (hq : q / p ∈ Set.Icc (0 : ℝ) 1) (hs : s / r ∈ Set.Icc (0 : ℝ) 1) :
    (eVariationOn traceEuclideanRadialSection
      (Set.Icc (min (q / p) (s / r)) (max (q / p) (s / r)))).toReal ≤
      2 * (traceEuclideanArcConstant : ℝ) / (H * min p r) := by
  have h := traceEuclideanRadialSection_farey_eVariationOn_le p q r s H hp hr hH hcutoff hdet hq hs
  exact (ENNReal.toReal_mono (by finiteness) h).trans_eq (ENNReal.toReal_ofReal (by positivity))

end Markov
