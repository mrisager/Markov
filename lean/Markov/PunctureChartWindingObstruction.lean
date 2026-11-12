import Markov.ModularOriginalPrimitiveCircles

/-! Actual deleted quarter-square puncture neighborhoods have zero coordinate
winding and zero genuine singular H1 for every contained loop. The coordinate
lifts are constructed using the actual AddCircle local chart inverse. No
peripheral class is defined by H1, and no arbitrary curve classification is used. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual small circle window is the projection of (-1/4,1/4). -/
def normalizedCirclePunctureWindow : Set NormalizedCircle :=
  normalizedCircleCover '' Ioo (-1/4 : ℝ) (1/4 : ℝ)

theorem normalizedCirclePunctureWindow_isOpen : IsOpen normalizedCirclePunctureWindow :=
  normalizedCircleCover_isCoveringMap.isOpenMap _ isOpen_Ioo

theorem normalizedCirclePunctureWindow_zero : (0 : NormalizedCircle) ∈ normalizedCirclePunctureWindow :=
  ⟨0,by norm_num,rfl⟩

/-- The small window avoids the actual cutpoint of the local inverse chart on
(-1/2,1/2), by injectivity of the actual quotient on that real interval. -/
theorem normalizedCirclePunctureWindow_avoids_cut {z : NormalizedCircle}
    (hz : z∈normalizedCirclePunctureWindow) : z≠((-1/2 : ℝ) : NormalizedCircle) := by
  obtain ⟨r,hr,he⟩ := hz
  intro hc
  have hi : r∈Ico (-1/2 : ℝ) (-1/2+1) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hj : (-1/2 : ℝ)∈Ico (-1/2 : ℝ) (-1/2+1) := by constructor <;> norm_num
  have heq : (r : NormalizedCircle)=((-1/2 : ℝ) : NormalizedCircle) := he.trans hc
  have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico hi hj).mp heq
  linarith [hr.1]

private def circleRealChartLift (z : NormalizedCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-1/2 : ℝ) z).val

private theorem circleRealChartLift_coe (z : NormalizedCircle) :
    normalizedCircleCover (circleRealChartLift z)=z :=
  (AddCircle.equivIco (1 : ℝ) (-1/2 : ℝ)).symm_apply_apply z

/-- Avoidance of the literal local-chart cutpoint gives an actual closed real
lift of the loop and an explicit contraction of each translated coordinate loop. -/
theorem normalizedCircleWinding_translated_eq_zero_of_avoids_cut
    {a : NormalizedCircle} (γ : Path a a)
    (hγ : ∀ t : unitInterval, γ t≠((-1/2 : ℝ) : NormalizedCircle)) :
    normalizedCircleWinding (normalizedCircleTranslatedLoop γ)=0 := by
  have hl : Continuous (fun t : unitInterval => circleRealChartLift (γ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco (1 : ℝ) (-1/2 : ℝ) (hγ t)).comp γ.continuous.continuousAt)
  let H : Path.Homotopy (normalizedCircleTranslatedLoop γ) (Path.refl (0 : NormalizedCircle)) :=
    { toFun := fun st => normalizedCircleCover
        ((1-(st.1 : ℝ))*(circleRealChartLift (γ st.2)-circleRealChartLift a))
      continuous_toFun := normalizedCircleCover_isCoveringMap.continuous.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          ((hl.comp continuous_snd).sub continuous_const))
      map_zero_left := fun t => by
        change normalizedCircleCover ((1-0)*(circleRealChartLift (γ t)-circleRealChartLift a)) = γ t-a
        simp only [sub_zero,one_mul]
        change normalizedCircleCover (circleRealChartLift (γ t))-
          normalizedCircleCover (circleRealChartLift a) = γ t-a
        rw [circleRealChartLift_coe,circleRealChartLift_coe]
      map_one_left := fun t => by
        change normalizedCircleCover ((1-1)*(circleRealChartLift (γ t)-circleRealChartLift a)) = 0
        simp [normalizedCircleCover]
      prop' := fun s t ht => by
        have he : γ t=a := by rcases ht with rfl | rfl; exact γ.source; exact γ.target
        change normalizedCircleCover ((1-(s : ℝ))*(circleRealChartLift (γ t)-circleRealChartLift a)) = γ t-a
        rw [he]
        simp [normalizedCircleCover] }
  have hw := normalizedCircleWinding_homotopic
    (show (normalizedCircleTranslatedLoop γ).Homotopic (Path.refl (0 : NormalizedCircle)) from ⟨H⟩)
  simpa only [normalizedCircleWinding_refl] using hw

/-- The explicit ambient quarter-square around the actual torus origin. -/
def standardTorusPunctureBox : Set StandardTorus :=
  normalizedCirclePunctureWindow ×ˢ normalizedCirclePunctureWindow

theorem standardTorusPunctureBox_isOpen : IsOpen standardTorusPunctureBox :=
  normalizedCirclePunctureWindow_isOpen.prod normalizedCirclePunctureWindow_isOpen

theorem standardTorusPunctureBox_zero : (0 : StandardTorus)∈standardTorusPunctureBox :=
  ⟨normalizedCirclePunctureWindow_zero,normalizedCirclePunctureWindow_zero⟩

/-- The actual deleted quarter-square neighborhood in the standard torus minus0. -/
def standardPunctureNeighborhood : Set StandardPuncturedTorus :=
  Subtype.val ⁻¹' standardTorusPunctureBox

theorem standardPunctureNeighborhood_isOpen : IsOpen standardPunctureNeighborhood :=
  standardTorusPunctureBox_isOpen.preimage continuous_subtype_val

/-- The actual same neighborhood in the modular quotient via its checked homeomorphism. -/
def modularPunctureNeighborhood : Set ModularTraceQuotient :=
  modularTraceQuotientPuncturedTorusHomeomorph ⁻¹' standardPunctureNeighborhood

theorem modularPunctureNeighborhood_isOpen : IsOpen modularPunctureNeighborhood :=
  standardPunctureNeighborhood_isOpen.preimage modularTraceQuotientPuncturedTorusHomeomorph.continuous

/-- Both actual standard coordinate windings of a contained loop vanish. -/
theorem standardTorusLoopWinding_eq_zero_of_punctureNeighborhood
    {x : StandardPuncturedTorus} (γ : Path x x)
    (hγ : ∀ t : unitInterval, γ t∈standardPunctureNeighborhood) :
    standardTorusLoopWinding γ=0 := by
  apply Prod.ext
  · exact normalizedCircleWinding_translated_eq_zero_of_avoids_cut
      (γ.map (continuous_fst.comp continuous_subtype_val))
      (fun t => normalizedCirclePunctureWindow_avoids_cut (hγ t).1)
  · exact normalizedCircleWinding_translated_eq_zero_of_avoids_cut
      (γ.map (continuous_snd.comp continuous_subtype_val))
      (fun t => normalizedCirclePunctureWindow_avoids_cut (hγ t).2)

/-- The actual quotient neighborhood inherits both zero windings. -/
theorem modularStandardLoopWinding_eq_zero_of_punctureNeighborhood
    {x : ModularTraceQuotient} (γ : Path x x)
    (hγ : ∀ t : unitInterval, γ t∈modularPunctureNeighborhood) :
    modularStandardLoopWinding γ=0 :=
  standardTorusLoopWinding_eq_zero_of_punctureNeighborhood
    (γ.map modularTraceQuotientPuncturedTorusHomeomorph.continuous) hγ

/-- The already checked all-loop comparison gives zero genuine fixed-I H1
coordinates for every loop in the actual deleted quarter-square neighborhood. -/
theorem modularPunctureNeighborhood_loop_fixedSingularCoordinates_zero
    {x : ModularTraceQuotient} (γ : Path x x)
    (hγ : ∀ t : unitInterval, γ t∈modularPunctureNeighborhood) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient γ)=0 := by
  rw [modularTraceFixedSingularH1Equiv_loop_standardWinding,
    modularStandardLoopWinding_eq_zero_of_punctureNeighborhood γ hγ]
  simp [originalToStandardCircleLabel]

/-- The actual integral singular-H1 class itself is zero. -/
theorem modularPunctureNeighborhood_loop_singularClass_zero
    {x : ModularTraceQuotient} (γ : Path x x)
    (hγ : ∀ t : unitInterval, γ t∈modularPunctureNeighborhood) :
    singularLoopClass ModularTraceQuotient γ=0 := by
  apply modularTraceFixedSingularH1Equiv.injective
  rw [modularPunctureNeighborhood_loop_fixedSingularCoordinates_zero γ hγ,map_zero]

/-- Every actual circle map contained in the explicit puncture neighborhood has
zero original fixed-I coordinates on its actual positive once-around loop. -/
theorem modularPunctureNeighborhood_circle_fixedSingularCoordinates_zero
    (q : C(NormalizedCircle,ModularTraceQuotient))
    (hq : ∀ u : NormalizedCircle, q u∈modularPunctureNeighborhood) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      (normalizedCircleStandardLoop.map q.continuous))=0 :=
  modularPunctureNeighborhood_loop_fixedSingularCoordinates_zero _
    (fun t => hq (normalizedCircleStandardLoop t))

/-- Such an actual circle map has zero genuine singular-H1 loop class. -/
theorem modularPunctureNeighborhood_circle_singularClass_zero
    (q : C(NormalizedCircle,ModularTraceQuotient))
    (hq : ∀ u : NormalizedCircle, q u∈modularPunctureNeighborhood) :
    singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map q.continuous)=0 :=
  modularPunctureNeighborhood_loop_singularClass_zero _
    (fun t => hq (normalizedCircleStandardLoop t))

end Markov
