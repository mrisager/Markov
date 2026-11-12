import Markov.StandardAffineCircleComplement
import Mathlib.Topology.Homotopy.Basic

/-! Genuine puncture-preserving curve homotopies from an explicit continuous
family of filled-torus homeomorphisms. The ambient family is input data: no
arbitrary simple-curve classification or isotopy-existence theorem is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- Correct an actual filled-torus ambient family by subtracting the moving
puncture, then correct the final translation along an actual complement path.
Both stages are genuine continuous homotopies in the punctured torus. -/
theorem standardPuncturedTorus_homotopic_of_filled_family_and_complement_path
    (q0 q1 : C(NormalizedCircle, StandardPuncturedTorus))
    (F : unitInterval → StandardTorus ≃ₜ StandardTorus)
    (hF : Continuous (fun z : unitInterval × StandardTorus => F z.1 z.2))
    (hF0 : ∀ z : StandardTorus, F 0 z = z)
    (hF1 : ∀ u : NormalizedCircle, F 1 (q0 u).val = (q1 u).val)
    (η : Path (F 1 0) (0 : StandardTorus))
    (hη : ∀ t : unitInterval, η t ∉ Set.range (fun u : NormalizedCircle => (q1 u).val)) :
    q0.Homotopic q1 := by
  have hne (z : unitInterval × NormalizedCircle) :
      F z.1 (q0 z.2).val - F z.1 0 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (F z.1).injective.ne (q0 z.2).property
  let Kfun : unitInterval × NormalizedCircle → StandardPuncturedTorus :=
    fun z => ⟨F z.1 (q0 z.2).val - F z.1 0, hne z⟩
  have hKfun : Continuous Kfun := by
    apply Continuous.subtype_mk
    exact (hF.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp (q0.continuous.comp continuous_snd)))).sub
      (hF.comp (continuous_fst.prodMk continuous_const))
  let qmid : C(NormalizedCircle, StandardPuncturedTorus) :=
    ⟨fun u => Kfun (1, u), hKfun.comp (continuous_const.prodMk continuous_id)⟩
  let K : q0.Homotopy qmid :=
    { toFun := Kfun
      continuous_toFun := hKfun
      map_zero_left := fun u => by
        apply Subtype.ext
        change F 0 (q0 u).val - F 0 0 = (q0 u).val
        rw [hF0, hF0, sub_zero]
      map_one_left := fun _ => rfl }
  let Lfun : unitInterval × NormalizedCircle → StandardPuncturedTorus :=
    fun z => ⟨(q1 z.2).val - η z.1,
      sub_ne_zero.mpr (fun he => hη z.1 ⟨z.2, he⟩)⟩
  have hLfun : Continuous Lfun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (q1.continuous.comp continuous_snd)).sub
      (η.continuous.comp continuous_fst)
  let L : qmid.Homotopy q1 :=
    { toFun := Lfun
      continuous_toFun := hLfun
      map_zero_left := fun u => by
        apply Subtype.ext
        change (q1 u).val - η 0 = F 1 (q0 u).val - F 1 0
        rw [η.source, hF1 u]
      map_one_left := fun u => by
        apply Subtype.ext
        change (q1 u).val - η 1 = (q1 u).val
        rw [η.target, sub_zero] }
  exact ⟨K.trans L⟩

/-- An actual path-connected filled complement discharges the correction path
constructively from its actual two endpoints; no point-pushing field is used. -/
theorem standardPuncturedTorus_homotopic_of_filled_family_and_pathConnected_complement
    (q0 q1 : C(NormalizedCircle, StandardPuncturedTorus))
    (F : unitInterval → StandardTorus ≃ₜ StandardTorus)
    (hF : Continuous (fun z : unitInterval × StandardTorus => F z.1 z.2))
    (hF0 : ∀ z : StandardTorus, F 0 z = z)
    (hF1 : ∀ u : NormalizedCircle, F 1 (q0 u).val = (q1 u).val)
    (hcomp : IsPathConnected ((Set.range (fun u : NormalizedCircle => (q1 u).val))ᶜ)) :
    q0.Homotopic q1 := by
  have hp : F 1 0 ∈ (Set.range (fun u : NormalizedCircle => (q1 u).val))ᶜ := by
    rintro ⟨u, hu⟩
    have he : F 1 (q0 u).val = F 1 0 := (hF1 u).trans hu
    exact (q0 u).property ((F 1).injective he)
  have hzero : (0 : StandardTorus) ∈
      (Set.range (fun u : NormalizedCircle => (q1 u).val))ᶜ := by
    rintro ⟨u, hu⟩
    exact (q1 u).property hu
  let hpath := hcomp.joinedIn (F 1 0) hp 0 hzero
  exact standardPuncturedTorus_homotopic_of_filled_family_and_complement_path
    q0 q1 F hF hF0 hF1 hpath.somePath (fun t => hpath.somePath_mem t)

/-- For the actual primitive affine target, the correction complement and path
are supplied by the proved filled-torus affine-complement theorem. The actual
filled ambient family remains an explicit hypothesis, not a classification. -/
theorem standardPuncturedTorus_homotopic_of_filled_family_affine_target
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0)
    (q0 : C(NormalizedCircle, StandardPuncturedTorus))
    (F : unitInterval → StandardTorus ≃ₜ StandardTorus)
    (hF : Continuous (fun z : unitInterval × StandardTorus => F z.1 z.2))
    (hF0 : ∀ z : StandardTorus, F 0 z = z)
    (hF1 : ∀ u : NormalizedCircle,
      F 1 (q0 u).val = (standardPuncturedAffineCircle p q hpq c hc u).val) :
    q0.Homotopic
      ⟨standardPuncturedAffineCircle p q hpq c hc,
        continuous_standardPuncturedAffineCircle p q hpq c hc⟩ := by
  apply standardPuncturedTorus_homotopic_of_filled_family_and_pathConnected_complement
    q0 ⟨standardPuncturedAffineCircle p q hpq c hc,
      continuous_standardPuncturedAffineCircle p q hpq c hc⟩ F hF hF0 hF1
  exact standardPuncturedAffineCircle_filled_complement_isPathConnected p q hpq c hc

end Markov
