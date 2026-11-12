import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite component regrouping before estimating the complete weights. -/

noncomputable section
open Classical
namespace Markov

/-- Regroup reciprocal-length weights by their actual component label,
then use a uniform fibre bound and the sum of component variations. -/
theorem finite_sum_component_div_le
    {ι κ : Type*} (S : Finset ι) (component : ι → κ) (r : ι → ℝ)
    (w : κ → ℝ) (B V : ℝ)
    (hB : 0 ≤ B) (hw : ∀ j ∈ S.image component, 0 ≤ w j)
    (hV : ∑ j ∈ S.image component, w j ≤ V)
    (hfibre : ∀ j ∈ S.image component,
      ∑ i ∈ S.filter (fun i => component i = j), 1 / r i ≤ B) :
    ∑ i ∈ S, w (component i) / r i ≤ V * B := by
  classical
  have hid : (∑ i ∈ S, w (component i) / r i) =
      ∑ j ∈ S.image component,
        w j * ∑ i ∈ S.filter (fun i => component i = j), 1 / r i := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image component) (g := component)
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (fun i => w (component i) / r i)]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
    ring
  rw [hid]
  calc
    _ ≤ ∑ j ∈ S.image component, w j * B :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hfibre j hj) (hw j hj))
    _ = (∑ j ∈ S.image component, w j) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ V * B := mul_le_mul_of_nonneg_right hV hB

end Markov
