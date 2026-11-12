import Markov.UnimodularTorusHomeomorphisms
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Instances.AddCircle.Real

/-! Path connectedness of actual complements of primitive affine circles in
the literal filled torus. No arbitrary embedded-curve classification is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- Removing one actual point from the normalized circle leaves a
path-connected set, via the literal open-interval quotient chart. -/
theorem normalizedCircle_compl_singleton_isPathConnected (c : NormalizedCircle) :
    IsPathConnected ({c}ᶜ : Set NormalizedCircle) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) a
  have hinterval : IsPathConnected (Set.Ioo a (a + 1)) :=
    (convex_Ioo a (a + 1)).isPathConnected
      ⟨a + 1 / 2, by constructor <;> linarith⟩
  have hpath := hinterval.image' e.continuousOn_toFun
  change IsPathConnected (e '' e.source) at hpath
  rw [e.image_source_eq_target] at hpath
  exact hpath

/-- The complement of an actual horizontal circle in the filled literal
two-circle torus is path connected. -/
theorem standardTorus_horizontal_complement_isPathConnected (c : NormalizedCircle) :
    IsPathConnected {z : StandardTorus | z.2 ≠ c} := by
  have hcircle := normalizedCircle_compl_singleton_isPathConnected c
  obtain ⟨d, hd⟩ := hcircle.nonempty
  refine isPathConnected_iff.mpr ⟨⟨(0, d), hd⟩, ?_⟩
  intro x hx y hy
  let p := PathConnectedSpace.somePath x.1 y.1
  let q := hcircle.joinedIn x.2 hx y.2 hy
  refine ⟨p.prod q.somePath, ?_⟩
  intro t
  exact q.somePath_mem t

/-- The filled affine circle is literally one fibre of the actual dual
coordinate, with both directions proved from the existing inverse map. -/
theorem standardPrimitiveAffineCircle_range_eq_secondDual
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) (c : NormalizedCircle) :
    Set.range (fun t : NormalizedCircle => standardTorusIntegerCombination p q t c) =
      {z : StandardTorus | standardTorusSecondDual p z = c} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact (standardTorusSecondDual_integerCombination p q t c).trans (by rw [hpq, one_smul])
  · intro hz
    have he := standardTorusColumnMap_dualMap p q z
    rw [hpq, one_smul] at he
    change standardTorusIntegerCombination p q (standardTorusFirstDual q z)
      (standardTorusSecondDual p z) = z at he
    rw [hz] at he
    exact ⟨standardTorusFirstDual q z, he⟩

/-- Every actual primitive affine-circle complement in the filled literal
torus is path connected; the offset is arbitrary, including zero. -/
theorem standardTorus_primitiveAffineCircle_complement_isPathConnected
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) (c : NormalizedCircle) :
    IsPathConnected
      ((Set.range (fun t : NormalizedCircle => standardTorusIntegerCombination p q t c))ᶜ) := by
  let e := standardUnimodularTorusHomeomorph p q hpq
  have himage : e '' {z : StandardTorus | z.2 ≠ c} =
      {z : StandardTorus | standardTorusSecondDual p z ≠ c} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have he : standardTorusSecondDual p (e w) = w.2 :=
        (standardTorusSecondDual_integerCombination p q w.1 w.2).trans
          (by rw [hpq, one_smul])
      change standardTorusSecondDual p (e w) ≠ c
      rw [he]
      exact hw
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      exact hz
  have hpath := (standardTorus_horizontal_complement_isPathConnected c).image e.continuous
  rw [himage] at hpath
  rw [standardPrimitiveAffineCircle_range_eq_secondDual p q hpq c]
  exact hpath

/-- The same actual filled complement for the existing puncture-avoiding
primitive affine circle map, with its original nonzero offset retained. -/
theorem standardPuncturedAffineCircle_filled_complement_isPathConnected
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    IsPathConnected
      ((Set.range (fun t : NormalizedCircle =>
        (standardPuncturedAffineCircle p q hpq c hc t).val))ᶜ) :=
  standardTorus_primitiveAffineCircle_complement_isPathConnected p q hpq c

end Markov
