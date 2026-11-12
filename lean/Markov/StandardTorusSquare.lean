import Markov.StandardCircleSquareScalar
import Markov.PaperQuadrilateralSquareChart

noncomputable section
open Set Topology
namespace Markov

/-- The literal compact closed square used for the standard torus presentation. -/
def standardClosedSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

/-- The standard topological torus, as the product of two real additive circles. -/
abbrev StandardTorus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- Its puncture is the common image of the four square corners. -/
def standardTorusPunctureComplement : Set StandardTorus := {t | t ≠ 0}

abbrev StandardPuncturedTorus := standardTorusPunctureComplement

theorem standardClosedSquare_isCompact : IsCompact standardClosedSquare :=
  isCompact_Icc.prod isCompact_Icc

instance standardClosedSquare_compactSpace : CompactSpace standardClosedSquare :=
  isCompact_iff_compactSpace.mp standardClosedSquare_isCompact

/-- The literal closed square map to the standard torus. -/
def standardTorusSquareMap (p : standardClosedSquare) : StandardTorus :=
  (standardCircleSquareScalar p.1.1, standardCircleSquareScalar p.1.2)

theorem continuous_standardTorusSquareMap : Continuous standardTorusSquareMap := by
  unfold standardTorusSquareMap standardCircleSquareScalar
  exact ((AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop))

theorem standardTorusSquareMap_surjective : Function.Surjective standardTorusSquareMap := by
  rintro ⟨u, v⟩
  obtain ⟨a, ha, hua⟩ := standardCircleSquareScalar_surjective u
  obtain ⟨b, hb, hvb⟩ := standardCircleSquareScalar_surjective v
  exact ⟨⟨(a, b), ha, hb⟩, by exact Prod.ext hua hvb⟩

/-- Compactness and the actual Hausdorff torus topology make the full map closed. -/
theorem standardTorusSquareMap_isClosedMap : IsClosedMap standardTorusSquareMap :=
  continuous_standardTorusSquareMap.isClosedMap

/-- The full closed-square map is an actual quotient map. -/
theorem standardTorusSquareMap_isQuotientMap : IsQuotientMap standardTorusSquareMap :=
  standardTorusSquareMap_isClosedMap.isQuotientMap
    continuous_standardTorusSquareMap standardTorusSquareMap_surjective

/-- The inverse image of the torus puncture consists exactly of the four corners. -/
theorem standardTorusSquareMap_eq_zero_iff (p : standardClosedSquare) :
    standardTorusSquareMap p = 0 ↔
      (p.1.1 = -1 ∨ p.1.1 = 1) ∧ (p.1.2 = -1 ∨ p.1.2 = 1) := by
  change (standardCircleSquareScalar p.1.1, standardCircleSquareScalar p.1.2) =
    (0, 0) ↔ _
  rw [Prod.mk.injEq, standardCircleSquareScalar_eq_zero_iff p.2.1,
    standardCircleSquareScalar_eq_zero_iff p.2.2]

/-- Exact puncture correspondence in the literal closed square. -/
theorem standardClosedSquare_punctured_iff (p : standardClosedSquare) :
    p.1 ∈ paperPuncturedSquare ↔ standardTorusSquareMap p ≠ 0 := by
  rw [Ne, standardTorusSquareMap_eq_zero_iff]
  change (|p.1.1| ≤ 1 ∧ |p.1.2| ≤ 1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 < 2) ↔ _
  have ha : |p.1.1| ≤ 1 := abs_le.mpr p.2.1
  have hb : |p.1.2| ≤ 1 := abs_le.mpr p.2.2
  constructor
  · rintro ⟨_, _, hlt⟩ ⟨hae, hbe⟩
    rcases hae with ha' | ha' <;> rcases hbe with hb' | hb' <;>
      rw [ha', hb'] at hlt <;> norm_num at hlt
  · intro hnc
    refine ⟨ha, hb, ?_⟩
    have ha₂ := paperSquare_coord_sq_le_one ha
    have hb₂ := paperSquare_coord_sq_le_one hb
    by_contra hn
    have hae : p.1.1 ^ 2 = 1 := by nlinarith
    have hbe : p.1.2 ^ 2 = 1 := by nlinarith
    have ha' : p.1.1 = -1 ∨ p.1.1 = 1 := by
      have : p.1.1 ^ 2 = (1 : ℝ) ^ 2 := by simpa using hae
      exact ((sq_eq_sq_iff_eq_or_eq_neg).mp this).symm
    have hb' : p.1.2 = -1 ∨ p.1.2 = 1 := by
      have : p.1.2 ^ 2 = (1 : ℝ) ^ 2 := by simpa using hbe
      exact ((sq_eq_sq_iff_eq_or_eq_neg).mp this).symm
    exact hnc ⟨ha', hb'⟩

/-- The complement of the puncture is open in the actual standard torus. -/
theorem standardTorusPunctureComplement_isOpen : IsOpen standardTorusPunctureComplement :=
  isClosed_singleton.isOpen_compl

/-- The chart's punctured square is exactly the open preimage under the full map,
with both subtype topologies and unchanged coordinates. -/
def standardPuncturedSquarePreimageHomeomorph :
    paperPuncturedSquare ≃ₜ standardTorusSquareMap ⁻¹' standardTorusPunctureComplement where
  toFun p := ⟨⟨p.1, abs_le.mp p.2.1, abs_le.mp p.2.2.1⟩,
    (standardClosedSquare_punctured_iff _).mp p.2⟩
  invFun p := ⟨p.1.1, (standardClosedSquare_punctured_iff p.1).mpr p.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The actual punctured square map to the actual punctured standard torus. -/
def standardPuncturedTorusMap (p : paperPuncturedSquare) : StandardPuncturedTorus :=
  standardTorusPunctureComplement.restrictPreimage standardTorusSquareMap
    (standardPuncturedSquarePreimageHomeomorph p)

/-- The restricted map retains its literal coordinate formula. -/
theorem standardPuncturedTorusMap_coe (p : paperPuncturedSquare) :
    (standardPuncturedTorusMap p).1 =
      (standardCircleSquareScalar p.1.1, standardCircleSquareScalar p.1.2) := rfl

/-- Restriction to the open complement of the puncture preserves the quotient topology. -/
theorem standardPuncturedTorusMap_isQuotientMap : IsQuotientMap standardPuncturedTorusMap :=
  (standardTorusSquareMap_isQuotientMap.restrictPreimage_isOpen
    standardTorusPunctureComplement_isOpen).comp
      standardPuncturedSquarePreimageHomeomorph.isQuotientMap

theorem continuous_standardPuncturedTorusMap : Continuous standardPuncturedTorusMap :=
  standardPuncturedTorusMap_isQuotientMap.continuous

theorem standardPuncturedTorusMap_surjective : Function.Surjective standardPuncturedTorusMap :=
  standardPuncturedTorusMap_isQuotientMap.surjective

end Markov
