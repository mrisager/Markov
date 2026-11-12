import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Intermediate values of the completed graph of a real Stieltjes function. -/

noncomputable section

open Set Filter
open scoped Topology

namespace Markov

/-- Every value strictly between the endpoint fibers of a Stieltjes function
belongs to the completed graph at an interior parameter. -/
theorem stieltjes_completedGraph_intermediate (F : StieltjesFunction ℝ)
    {a b θ : ℝ} (_hab : a < b) (ha : F a < θ)
    (hb : θ < Function.leftLim F b) :
    ∃ c ∈ Ioo a b, θ ∈ Icc (Function.leftLim F c) (F c) := by
  let S : Set ℝ := {t | F t ≤ θ}
  have hS : S.Nonempty := ⟨a, ha.le⟩
  have hSb : ∀ t ∈ S, t ≤ b := by
    intro t ht
    by_contra htb
    have hbt : b ≤ t := (lt_of_not_ge htb).le
    exact (not_le_of_gt hb) ((F.mono.leftLim_le hbt).trans ht)
  have hSbdd : BddAbove S := ⟨b, hSb⟩
  let c : ℝ := sSup S
  have hac : a ≤ c := le_csSup hSbdd ha.le
  have hcb : c ≤ b := csSup_le hS hSb
  have hleft : Function.leftLim F c ≤ θ := by
    rw [F.mono.leftLim_eq_sSup (by exact (inferInstance : NeBot (𝓝[<] c)).ne)]
    apply csSup_le
    · exact ⟨F (c - 1), c - 1, by simp, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, huv⟩ := exists_lt_of_lt_csSup hS hu
      exact (F.mono huv.le).trans hv
  have hright : θ ≤ F c := by
    rw [← F.rightLim_eq c,
      F.mono.rightLim_eq_sInf (by exact (inferInstance : NeBot (𝓝[>] c)).ne)]
    apply le_csInf
    · exact ⟨F (c + 1), c + 1, by simp, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      by_contra hθu
      have huS : u ∈ S := (lt_of_not_ge hθu).le
      exact (not_le_of_gt hu) (le_csSup hSbdd huS)
  refine ⟨c, ⟨?_, ?_⟩, hleft, hright⟩
  · exact lt_of_le_of_ne hac (by
      intro hac'
      exact (not_le_of_gt ha) (hac'.symm ▸ hright))
  · exact lt_of_le_of_ne hcb (by
      intro hcb'
      exact (not_le_of_gt hb) (hcb' ▸ hleft))

end Markov
