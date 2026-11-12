import Markov.NormalizedCircleWinding

/-! Genuine normalized circle winding is invariant under based-path conjugation,
after translating each loop's own basepoint to zero. The proof uses actual
covering monodromy, unique lifts and deck translations; no H1 comparison is assumed. -/

noncomputable section
namespace Markov

/-- Translate the basepoint of an actual circle loop to zero, literally pointwise. -/
def normalizedCircleTranslatedLoop {a : NormalizedCircle} (γ : Path a a) :
    Path (0 : NormalizedCircle) 0 where
  toFun t := γ t - a
  continuous_toFun := by fun_prop
  source' := by rw [γ.source, sub_self]
  target' := by rw [γ.target, sub_self]

@[simp] theorem normalizedCircleTranslatedLoop_apply {a : NormalizedCircle}
    (γ : Path a a) (t : unitInterval) :
    normalizedCircleTranslatedLoop γ t = γ t - a := rfl

/-- An integer period translates the actual fibre over any circle point. -/
def normalizedCircleFibreAtTranslate (a : NormalizedCircle) (n : ℤ)
    (e : normalizedCircleCover ⁻¹' {a}) : normalizedCircleCover ⁻¹' {a} :=
  ⟨(n : ℝ) + e.val, by
    change normalizedCircleCover ((n : ℝ) + e.val) = a
    rw [normalizedCircleCover_add, normalizedCircleCover_intCast, zero_add]
    exact e.property⟩

/-- Actual monodromy along an arbitrary circle path commutes with integer periods. -/
theorem normalizedCircleMonodromyAt_translate {a b : NormalizedCircle} (n : ℤ)
    (c : Path.Homotopic.Quotient a b) (e : normalizedCircleCover ⁻¹' {a}) :
    normalizedCircleCover_isCoveringMap.monodromy c (normalizedCircleFibreAtTranslate a n e) =
      normalizedCircleFibreAtTranslate b n
        (normalizedCircleCover_isCoveringMap.monodromy c e) := by
  obtain ⟨γ⟩ := c
  apply Subtype.ext
  let cov := normalizedCircleCover_isCoveringMap
  let L := cov.liftPath γ e.val (γ.source.trans e.property.symm)
  have hl : (fun t => (n : ℝ) + L t) =
      cov.liftPath γ ((n : ℝ) + e.val)
        (γ.source.trans (normalizedCircleFibreAtTranslate a n e).property.symm) := by
    apply (cov.eq_liftPath_iff _).mpr
    refine ⟨by fun_prop, ?_, ?_⟩
    · funext t
      change normalizedCircleCover ((n : ℝ) + L t) = γ t
      rw [normalizedCircleCover_add, normalizedCircleCover_intCast, zero_add]
      exact congr_fun (cov.liftPath_lifts γ e.val _) t
    · change (n : ℝ) + L 0 = (n : ℝ) + e.val
      rw [show L 0 = e.val from cov.liftPath_zero γ e.val _]
  exact (congr_fun hl 1).symm

/-- Winding after translating a loop is its actual lifted displacement from
any point of its actual covering fibre. -/
theorem normalizedCircleMonodromy_loop_eq_translate {a : NormalizedCircle}
    (γ : Path a a) (e : normalizedCircleCover ⁻¹' {a}) :
    normalizedCircleCover_isCoveringMap.monodromy (.mk γ) e =
      normalizedCircleFibreAtTranslate a
        (normalizedCircleWinding (normalizedCircleTranslatedLoop γ)) e := by
  apply Subtype.ext
  let cov := normalizedCircleCover_isCoveringMap
  let L := cov.liftPath γ e.val (γ.source.trans e.property.symm)
  have hshift : (fun t => L t - e.val) =
      cov.liftPath (normalizedCircleTranslatedLoop γ) 0
        (normalizedCircleTranslatedLoop γ).source := by
    apply (cov.eq_liftPath_iff _).mpr
    refine ⟨by fun_prop, ?_, ?_⟩
    · funext t
      change normalizedCircleCover (L t - e.val) = γ t - a
      change normalizedCircleCover (L t) - normalizedCircleCover e.val = γ t - a
      rw [e.property]
      exact congrArg (fun z => z - a) (congr_fun (cov.liftPath_lifts γ e.val _) t)
    · rw [show L 0 = e.val from cov.liftPath_zero γ e.val _, sub_self]
  have hw := normalizedCircleWinding_eq_liftPath_endpoint (normalizedCircleTranslatedLoop γ)
  rw [← congr_fun hshift 1] at hw
  change L 1 = (normalizedCircleWinding (normalizedCircleTranslatedLoop γ) : ℝ) + e.val
  linarith

/-- Conjugating a loop by an actual connecting path preserves its genuine
integer winding, with each actual basepoint translated to zero. -/
theorem normalizedCircleWinding_translated_conjugate {a b : NormalizedCircle}
    (α : Path a b) (γ : Path b b) :
    normalizedCircleWinding
      (normalizedCircleTranslatedLoop ((α.trans γ).trans α.symm)) =
        normalizedCircleWinding (normalizedCircleTranslatedLoop γ) := by
  obtain ⟨s, _, hs⟩ := AddCircle.eq_coe_Ico a
  let e : normalizedCircleCover ⁻¹' {a} := ⟨s, hs⟩
  let cov := normalizedCircleCover_isCoveringMap
  let w := normalizedCircleWinding (normalizedCircleTranslatedLoop γ)
  have hcancel : cov.monodromy (.mk α.symm) (cov.monodromy (.mk α) e) = e := by
    rw [← cov.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_symm, cov.monodromy_refl]
    rfl
  have hconj : cov.monodromy (.mk ((α.trans γ).trans α.symm)) e =
      normalizedCircleFibreAtTranslate a w e := by
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      cov.monodromy_trans_apply, cov.monodromy_trans_apply,
      normalizedCircleMonodromy_loop_eq_translate,
      normalizedCircleMonodromyAt_translate, hcancel]
  have hdisplacement := normalizedCircleMonodromy_loop_eq_translate
    ((α.trans γ).trans α.symm) e
  rw [hconj] at hdisplacement
  have hreal := congrArg Subtype.val hdisplacement
  apply Int.cast_injective (α := ℝ)
  change ((normalizedCircleWinding (normalizedCircleTranslatedLoop
    ((α.trans γ).trans α.symm)) : ℤ) : ℝ) = (w : ℝ)
  change (w : ℝ) + e.val =
    (normalizedCircleWinding (normalizedCircleTranslatedLoop
      ((α.trans γ).trans α.symm)) : ℝ) + e.val at hreal
  linarith

end Markov
