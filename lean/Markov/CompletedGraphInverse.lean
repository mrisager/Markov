import Markov.StieltjesCompletedGraph

/-! Existence and inverse location in the completed graph of an actual
Stieltjes function. Strict bounds across endpoint jumps localize every
support parameter; no strict monotonicity is assumed. -/

noncomputable section
open Set
namespace Markov

/-- Strict separation from the two exterior endpoint values forces a
completed-graph parameter into the closed parameter interval. -/
theorem completedGraph_parameter_mem_Icc (F : StieltjesFunction ℝ)
    {a b t φ : ℝ}
    (hφ : φ ∈ Icc (Function.leftLim F t) (F t))
    (ha : Function.leftLim F a < φ) (hb : φ < F b) : t ∈ Icc a b := by
  constructor
  · by_contra h
    have ht : t < a := lt_of_not_ge h
    have horder := F.mono.le_leftLim ht
    linarith [hφ.2]
  · by_contra h
    have ht : b < t := lt_of_not_ge h
    have horder := F.mono.le_leftLim ht
    linarith [hφ.1]

/-- Every angle between the full endpoint fibres is attained somewhere
on the closed interval, including either endpoint jump. -/
theorem completedGraph_exists_mem_Icc (F : StieltjesFunction ℝ)
    {a b φ : ℝ} (hab : a < b)
    (hφ : φ ∈ Icc (Function.leftLim F a) (F b)) :
    ∃ t ∈ Icc a b, φ ∈ Icc (Function.leftLim F t) (F t) := by
  by_cases hleft : φ ≤ F a
  · exact ⟨a, ⟨le_rfl, hab.le⟩, hφ.1, hleft⟩
  by_cases hright : Function.leftLim F b ≤ φ
  · exact ⟨b, ⟨hab.le, le_rfl⟩, hright, hφ.2⟩
  obtain ⟨t, ht, hgraph⟩ := stieltjes_completedGraph_intermediate F hab
    (lt_of_not_ge hleft) (lt_of_not_ge hright)
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hgraph⟩

/-- A jump wider than twice the chosen neighborhood radius contains the
entire enlarged interval of adjacent interior angles. -/
theorem completedGraph_offset_mem_between_endpoint_jumps
    (F : StieltjesFunction ℝ) (a b η ψ ξ : ℝ)
    (hleft : 2 * η < F a - Function.leftLim F a)
    (hright : 2 * η < F b - Function.leftLim F b)
    (hψ : ψ ∈ Icc (F a - η) (Function.leftLim F b + η))
    (hξ : |ξ - ψ| ≤ η) :
    Function.leftLim F a < ξ ∧ ξ < F b := by
  have hξ' := abs_le.mp hξ
  constructor <;> linarith [hψ.1, hψ.2, hξ'.1, hξ'.2]

end Markov
