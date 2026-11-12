import Markov.FrontierEnvelope

/-! The actual finite convex Farey profiles decrease under refinement on
the physical section [0,1]. This is proved from the strict mediant inequality,
not imposed as an assumption on a hypothetical sequence. -/

namespace Markov

theorem frontierProfile_eq_of_mem_interval (n : ℕ) (e : FareyEdge)
    (he : e ∈ fareyFrontier n) (t : ℝ)
    (hl : profileParameter e.u ≤ t) (hr : t ≤ profileParameter e.v) :
    frontierProfile n t = e.profile t := by
  obtain ⟨i, hi, hei⟩ := fareyFrontier_mem_exists_index n e he
  simpa only [hei] using frontierProfile_eq_on_interval n i t hi
    (by simpa only [hei] using hl) (by simpa only [hei] using hr)

/-- Every refinement lowers its actual interpolating profile. -/
theorem frontierProfile_succ_le (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    frontierProfile (n + 1) t ≤ frontierProfile n t := by
  obtain ⟨child, hchild, hval, hl, hr⟩ := frontierProfile_piece_exists (n + 1) t ht0 ht1
  change child ∈ (fareyFrontier n).flatMap FareyEdge.refine at hchild
  obtain ⟨parent, hp, hpc⟩ := List.mem_flatMap.mp hchild
  simp only [FareyEdge.refine, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · have hpr : t ≤ profileParameter parent.v := hr.trans parent.right.profileParameter_lt.le
    have hpval := frontierProfile_eq_of_mem_interval n parent hp t hl hpr
    rw [hval, hpval]
    exact parent.left_profile_le t hl hr
  · have hpl : profileParameter parent.u ≤ t := parent.left.profileParameter_lt.le.trans hl
    have hpval := frontierProfile_eq_of_mem_interval n parent hp t hpl hr
    rw [hval, hpval]
    exact parent.right_profile_le t hl hr

/-- The explicit sequence is pointwise antitone on the full section. -/
theorem frontierProfile_antitone (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun n : ℕ => frontierProfile n t) :=
  antitone_nat_of_succ_le (fun n => frontierProfile_succ_le n t ht0 ht1)

end Markov
