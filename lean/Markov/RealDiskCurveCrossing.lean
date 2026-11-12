import Markov.RealCurveCompactification
import Markov.DiskArcTransverseCrossing

/-! Actual real-parameter disk crossing from actual endpoint chord crossing.
The compactification is constructed by the checked logarithmic formula. Unit
boundary endpoints and strict disk interiors exclude endpoint-only crossings;
the literal open-interval range theorem supplies actual real parameters. -/

noncomputable section
open Set Topology Filter
namespace Markov

private theorem unit_point_ne_path_interior (c d : ℂ) (β : Path c d)
    (hβ : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖β t‖ < 1)
    (a : ℂ) (ha : ‖a‖=1) (hac : a≠c) (had : a≠d) (t : unitInterval) : a≠β t := by
  by_cases ht0 : t=0
  · subst t
    simpa only [β.source] using hac
  by_cases ht1 : t=1
  · subst t
    simpa only [β.target] using had
  have ht0' : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
  have ht1' : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
  intro he
  have hn := congrArg norm he
  have hl := hβ t ht0' ht1'
  linarith

/-- Actual continuous real disk curves meet if their actual four distinct unit
boundary limits have transverse endpoint chords crossing at interior parameters.
Every compactified arc and the resulting real parameters are constructed. -/
theorem realDiskCurves_intersect_of_transverse_endpoint_chords
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (a b c d : ℂ)
    (hfa : Tendsto f atBot (𝓝 a)) (hfb : Tendsto f atTop (𝓝 b))
    (hgc : Tendsto g atBot (𝓝 c)) (hgd : Tendsto g atTop (𝓝 d))
    (hfn : ∀ x : ℝ, ‖f x‖<1) (hgn : ∀ x : ℝ, ‖g x‖<1)
    (han : ‖a‖=1) (hbn : ‖b‖=1) (hcn : ‖c‖=1) (hdn : ‖d‖=1)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hdet : (b-a).re*(d-c).im-(b-a).im*(d-c).re≠0)
    (u v : unitInterval) (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1)
    (hv0 : 0<(v:ℝ)) (hv1 : (v:ℝ)<1)
    (hchord : (1-(u:ℝ)) • a+(u:ℝ) • b = (1-(v:ℝ)) • c+(v:ℝ) • d) :
    ∃ s t : ℝ, f s=g t := by
  let α := realCurveCompactifiedPath f hf a b hfa hfb
  let β := realCurveCompactifiedPath g hg c d hgc hgd
  have hα : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → ‖α t‖<1 :=
    fun t ht0 ht1 => realCurveCompactifiedPath_norm_lt_one f hf a b hfa hfb hfn t ht0 ht1
  have hβ : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → ‖β t‖<1 :=
    fun t ht0 ht1 => realCurveCompactifiedPath_norm_lt_one g hg c d hgc hgd hgn t ht0 ht1
  have hend : ∀ t s : unitInterval, (t=0 ∨ t=1) → (s=0 ∨ s=1) → α t≠β s := by
    intro t s ht hs
    rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
    · simpa only [α.source,β.source] using hac
    · simpa only [α.source,β.target] using had
    · simpa only [α.target,β.source] using hbc
    · simpa only [α.target,β.target] using hbd
  have hdet' : (α 1-α 0).re*(β 1-β 0).im-(α 1-α 0).im*(β 1-β 0).re≠0 := by
    simpa only [α.source,α.target,β.source,β.target] using hdet
  have hchord' : diskArcChord α u=diskArcChord β v := by
    simpa only [diskArcChord,α.source,α.target,β.source,β.target] using hchord
  obtain ⟨t,s,he⟩ := diskArcs_intersect_of_transverse_interior_chords α β α.continuous β.continuous
    (by simpa only [α.source] using han) (by simpa only [α.target] using hbn)
    (by simpa only [α.source,α.target] using hab)
    (by simpa only [β.source] using hcn) (by simpa only [β.target] using hdn)
    (by simpa only [β.source,β.target] using hcd)
    hα hβ hend hdet' u v hu0 hu1 hv0 hv1 hchord'
  have ht0 : t≠0 := by
    intro h
    subst t
    exact unit_point_ne_path_interior c d β hβ a han hac had s (α.source.symm.trans he)
  have ht1 : t≠1 := by
    intro h
    subst t
    exact unit_point_ne_path_interior c d β hβ b hbn hbc hbd s (α.target.symm.trans he)
  have hs0 : s≠0 := by
    intro h
    subst s
    exact unit_point_ne_path_interior a b α hα c hcn hac.symm hbc.symm t (β.source.symm.trans he.symm)
  have hs1 : s≠1 := by
    intro h
    subst s
    exact unit_point_ne_path_interior a b α hα d hdn had.symm hbd.symm t (β.target.symm.trans he.symm)
  have ht : 0<(t:ℝ) ∧ (t:ℝ)<1 :=
    ⟨lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))⟩
  have hs : 0<(s:ℝ) ∧ (s:ℝ)<1 :=
    ⟨lt_of_le_of_ne s.property.1 (fun h => hs0 (Subtype.ext h.symm)),
      lt_of_le_of_ne s.property.2 (fun h => hs1 (Subtype.ext h))⟩
  have hfr : α t∈range f := by
    rw [← realCurveCompactifiedPath_interior_range f hf a b hfa hfb]
    exact ⟨t,ht,rfl⟩
  have hgr : β s∈range g := by
    rw [← realCurveCompactifiedPath_interior_range g hg c d hgc hgd]
    exact ⟨s,hs,rfl⟩
  obtain ⟨x,hx⟩ := hfr
  obtain ⟨y,hy⟩ := hgr
  exact ⟨x,y,hx.trans (he.trans hy.symm)⟩

end Markov
