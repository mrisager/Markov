import Markov.FiniteComponentWeights
import Mathlib.Data.Finset.Max

/-! Finite maximum representatives allow varying nonnegative weights inside
one component fibre without assuming those weights are equal. -/

noncomputable section
open Classical
namespace Markov

/-- Fibrewise maximal representatives reduce variable weights to one
nonnegative component weight. The representative sum hypothesis is needed
only for subsets on which the component label is injective. -/
theorem finite_sum_component_div_le_of_representative_sums
    {ι κ : Type*} (S : Finset ι) (component : ι → κ) (r w : ι → ℝ) (B V : ℝ)
    (hB : 0 ≤ B) (hw : ∀ i ∈ S, 0 ≤ w i) (hr : ∀ i ∈ S, 0 < r i)
    (hfibre : ∀ j ∈ S.image component,
      ∑ i ∈ S.filter (fun i => component i = j), 1 / r i ≤ B)
    (hrep : ∀ T : Finset ι, T ⊆ S → Set.InjOn component T →
      ∑ i ∈ T, w i ≤ V) :
    ∑ i ∈ S, w i / r i ≤ V * B := by
  classical
  let J := S.image component
  have hex (j : J) : ∃ i ∈ S, component i = j.val ∧
      ∀ l ∈ S, component l = j.val → w l ≤ w i := by
    have hne : (S.filter fun i => component i = j.val).Nonempty := by
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp j.property
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
    obtain ⟨i, hi, hmax⟩ := (S.filter fun i => component i = j.val).exists_max_image w hne
    exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2,
      fun l hl hlj => hmax l (Finset.mem_filter.mpr ⟨hl, hlj⟩)⟩
  choose rep hrepS hrepLabel hrepMax using hex
  have hrepinj : Function.Injective rep := by
    intro j l hjl
    apply Subtype.ext
    exact (hrepLabel j).symm.trans ((congrArg component hjl).trans (hrepLabel l))
  let T : Finset ι := Finset.univ.image rep
  have hTS : T ⊆ S := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hrepS j
  have hTinj : Set.InjOn component T := by
    intro i hi l hl hil
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    have hjk : j = k := Subtype.ext ((hrepLabel j).symm.trans (hil.trans (hrepLabel k)))
    exact congrArg rep hjk
  let W : κ → ℝ := fun j => if hj : j ∈ J then w (rep ⟨j, hj⟩) else 0
  have hW (j : κ) (hj : j ∈ J) : W j = w (rep ⟨j, hj⟩) := by
    simp only [W, dif_pos hj]
  have hWnonneg : ∀ j ∈ S.image component, 0 ≤ W j := by
    intro j hj
    rw [hW j hj]
    exact hw _ (hrepS _)
  have hWsum : (∑ j ∈ S.image component, W j) ≤ V := by
    have heq : (∑ j : J, w (rep j)) = ∑ j ∈ J, W j := by
      rw [← Finset.sum_coe_sort J W]
      apply Finset.sum_congr rfl
      intro j _
      exact (hW j.val j.property).symm
    have hTsum : (∑ i ∈ T, w i) = ∑ j : J, w (rep j) := by
      exact Finset.sum_image (fun j _ l _ hjl => hrepinj hjl)
    rw [← heq, ← hTsum]
    exact hrep T hTS hTinj
  have hbound : (∑ i ∈ S, w i / r i) ≤ ∑ i ∈ S, W (component i) / r i := by
    apply Finset.sum_le_sum
    intro i hi
    have hci : component i ∈ J := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    apply div_le_div_of_nonneg_right _ (hr i hi).le
    rw [hW _ hci]
    exact hrepMax _ i hi rfl
  exact hbound.trans
    (finite_sum_component_div_le S component r W B V hB hWnonneg hWsum hfibre)

end Markov
