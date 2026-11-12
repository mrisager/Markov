import Markov.FilledTorusCircleHomotopy
import Markov.StandardPrimitiveCircles

noncomputable section
namespace Markov

/-- Integer linear combinations of actual based circle paths have the
corresponding genuine covering winding, proved by their actual real lifts. -/
theorem normalizedCircleWinding_integer_linear
    (a b : ℤ) (γ δ ε : Path (0 : NormalizedCircle) 0)
    (hε : ∀ t, ε t = a • γ t - b • δ t) :
    normalizedCircleWinding ε = a*normalizedCircleWinding γ - b*normalizedCircleWinding δ := by
  let cov := normalizedCircleCover_isCoveringMap
  let G := cov.liftPath γ 0 γ.source
  let D := cov.liftPath δ 0 δ.source
  have he : (fun t => a • G t - b • D t) = cov.liftPath ε 0 ε.source := by
    apply (cov.eq_liftPath_iff _).mpr
    refine ⟨by fun_prop, ?_, ?_⟩
    · funext t
      change (((a • G t - b • D t : ℝ)) : NormalizedCircle) = ε t
      rw [AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_zsmul]
      have hG := congr_fun (cov.liftPath_lifts γ 0 γ.source) t
      have hD := congr_fun (cov.liftPath_lifts δ 0 δ.source) t
      change (G t : NormalizedCircle) = γ t at hG
      change (D t : NormalizedCircle) = δ t at hD
      rw [hG, hD, hε t]
    · change a • G 0 - b • D 0 = 0
      rw [cov.liftPath_zero γ 0 γ.source, cov.liftPath_zero δ 0 δ.source]
      simp
  have hεend := normalizedCircleWinding_eq_liftPath_endpoint ε
  have hγend := normalizedCircleWinding_eq_liftPath_endpoint γ
  have hδend := normalizedCircleWinding_eq_liftPath_endpoint δ
  rw [← congr_fun he 1] at hεend
  change (normalizedCircleWinding γ : ℝ) = G 1 at hγend
  change (normalizedCircleWinding δ : ℝ) = D 1 at hδend
  rw [← hγend, ← hδend] at hεend
  simp only [zsmul_eq_mul] at hεend
  exact_mod_cast hεend

/-- The genuine winding of the literal first dual coordinate of a filled
torus circle map is its explicit integral linear combination of coordinate windings. -/
theorem standardTorusCircleMap_firstDual_winding
    (f : C(NormalizedCircle, StandardTorus)) (q : ℤ × ℤ) :
    normalizedCircleMapWinding
      ⟨fun u => standardTorusFirstDual q (f u),
        (continuous_standardTorusFirstDual q).comp f.continuous⟩ =
      q.2*(standardTorusCircleMapWinding f).1 - q.1*(standardTorusCircleMapWinding f).2 := by
  apply normalizedCircleWinding_integer_linear q.2 q.1
  intro t
  change standardTorusFirstDual q (f (normalizedCircleStandardLoop t)) -
      standardTorusFirstDual q (f 0) =
    q.2 • ((f (normalizedCircleStandardLoop t)).1 - (f 0).1) -
      q.1 • ((f (normalizedCircleStandardLoop t)).2 - (f 0).2)
  simp only [standardTorusFirstDual, smul_sub]
  abel

end Markov
