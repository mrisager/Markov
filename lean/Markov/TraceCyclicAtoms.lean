import Markov.TraceCyclicTurn
import Markov.ChordCornerGeometry
import Mathlib.Topology.Order.LeftRightLim

/-! Atoms of the actual cyclic support-angle lift are the differences of
the actual outgoing and incoming support angles. The half-open quarter
convention includes all four axis seams exactly once. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Markov

/-- A complete closed quarter agrees with its shifted chord lift. The
agreement at its upper endpoint follows from the proved glue seam. -/
theorem traceCyclicAngleLift_eq_shifted_on_Icc (i : Fin 4) (t : ℝ)
    (ht : t ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1)) :
    traceCyclicAngleLift t = traceShiftedChordLift i t := by
  fin_cases i
  all_goals norm_num only [Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add] at ht ⊢
  · rw [traceCyclicAngleLift, stieltjesGlue_of_le _ _ _ _ _ (by linarith [ht.2]),
      traceFirstThreeChordLift, stieltjesGlue_of_le _ _ _ _ _ (by linarith [ht.2]),
      traceFirstTwoChordLift, stieltjesGlue_of_le _ _ _ _ _ ht.2]
    rfl
  · rw [traceCyclicAngleLift, stieltjesGlue_of_le _ _ _ _ _ (by linarith [ht.2]),
      traceFirstThreeChordLift, stieltjesGlue_of_le _ _ _ _ _ ht.2,
      traceFirstTwoChordLift, stieltjesGlue_of_ge _ _ _ _ _ ht.1]
    rfl
  · rw [traceCyclicAngleLift, stieltjesGlue_of_le _ _ _ _ _ ht.2,
      traceFirstThreeChordLift, stieltjesGlue_of_ge _ _ _ _ _ ht.1]
    rfl
  · exact traceCyclicAngleLift_of_three_le t ht.1

/-- On a closed chord the actual cyclic angle is its selected support
angle with the quadrant's fixed angle offset. -/
theorem traceCyclicAngleLift_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    traceCyclicAngleLift ((i.val : ℝ) + s) =
      chordSelectedAngle (traceRotationBasis i.val) s + (i.val : ℝ) * Real.pi / 2 := by
  rw [traceCyclicAngleLift_eq_shifted_on_Icc i _ ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    traceShiftedChordLift_apply, add_sub_cancel_left,
    traceChordAngleLift_eq_chord i s hs]

/-- The local clamped lift approaches the actual incoming support angle
from the left whenever the initial clamped endpoint is excluded. -/
theorem traceChordAngleLift_tendsto_left (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Tendsto (traceChordAngleLift i) (𝓝[<] s)
      (𝓝 (chordLeftSelectedAngle (traceRotationBasis i.val) s)) := by
  apply (chordSelectedAngle_tendsto_left (traceRotationBasis i.val) traceAxisLength s
    (norm_traceRotationBasis_zero i) (norm_traceRotationBasis_one i)
    (norm_traceRotationBasis_sub_lt i) ⟨hs.1.le, hs.2⟩).congr'
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] s, 0 < t :=
    (eventually_gt_nhds hs.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with t ht hts
  exact (traceChordAngleLift_eq_chord i t ⟨ht.le, (show t < s from hts).le.trans hs.2⟩).symm

/-- Translation carries the actual incoming chord angle to the left limit
of the corresponding shifted lift. -/
theorem traceShiftedChordLift_tendsto_left (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Tendsto (traceShiftedChordLift i) (𝓝[<] ((i.val : ℝ) + s))
      (𝓝 (chordLeftSelectedAngle (traceRotationBasis i.val) s +
        (i.val : ℝ) * Real.pi / 2)) := by
  have hsub : Tendsto (fun t : ℝ => t - (i.val : ℝ))
      (𝓝[<] ((i.val : ℝ) + s)) (𝓝[<] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => t - (i.val : ℝ)) :=
        continuous_id.sub continuous_const
      have hfull : Tendsto (fun t : ℝ => t - (i.val : ℝ))
          (𝓝[<] ((i.val : ℝ) + s)) (𝓝 (((i.val : ℝ) + s) - (i.val : ℝ))) :=
        (hc.tendsto _).mono_left nhdsWithin_le_nhds
      simpa only [add_sub_cancel_left] using hfull
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t - (i.val : ℝ) < s
      have ht' : t < (i.val : ℝ) + s := ht
      linarith
  exact ((traceChordAngleLift_tendsto_left i s hs).comp hsub).add_const _

/-- The global cyclic lift has the same incoming angle as its actual
quarter chord, including the terminal axis seam at parameter four. -/
theorem traceCyclicAngleLift_tendsto_left_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Tendsto traceCyclicAngleLift (𝓝[<] ((i.val : ℝ) + s))
      (𝓝 (chordLeftSelectedAngle (traceRotationBasis i.val) s +
        (i.val : ℝ) * Real.pi / 2)) := by
  apply (traceShiftedChordLift_tendsto_left i s hs).congr'
  have hgt : (i.val : ℝ) < (i.val : ℝ) + s := by linarith [hs.1]
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] ((i.val : ℝ) + s), (i.val : ℝ) < t :=
    (eventually_gt_nhds hgt).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with t ht hts
  exact (traceCyclicAngleLift_eq_shifted_on_Icc i t
    ⟨ht.le, (show t < (i.val : ℝ) + s from hts).le.trans (by linarith [hs.2])⟩).symm

theorem traceCyclicAngleLift_leftLim_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Function.leftLim traceCyclicAngleLift ((i.val : ℝ) + s) =
      chordLeftSelectedAngle (traceRotationBasis i.val) s + (i.val : ℝ) * Real.pi / 2 :=
  leftLim_eq_of_tendsto
    (NeBot.ne (inferInstance : (𝓝[<] ((i.val : ℝ) + s)).NeBot))
    (traceCyclicAngleLift_tendsto_left_at_chord i s hs)

/-- Every point atom in the actual cyclic lift is the full difference of
its actual outgoing and incoming support angles. -/
theorem traceCyclicTurn_singleton_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    angleTurnMeasure traceCyclicAngleLift {((i.val : ℝ) + s)} =
      ENNReal.ofReal (chordSelectedAngle (traceRotationBasis i.val) s -
        chordLeftSelectedAngle (traceRotationBasis i.val) s) := by
  rw [angleTurnMeasure_singleton, traceCyclicAngleLift_at_chord i s ⟨hs.1.le, hs.2⟩,
    traceCyclicAngleLift_leftLim_at_chord i s hs, add_sub_add_right_eq_sub]

theorem traceCyclicTurn_singleton_at_chord_toReal (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    (angleTurnMeasure traceCyclicAngleLift {((i.val : ℝ) + s)}).toReal =
      chordSelectedAngle (traceRotationBasis i.val) s -
        chordLeftSelectedAngle (traceRotationBasis i.val) s := by
  rw [angleTurnMeasure_singleton_toReal,
    traceCyclicAngleLift_at_chord i s ⟨hs.1.le, hs.2⟩,
    traceCyclicAngleLift_leftLim_at_chord i s hs, add_sub_add_right_eq_sub]

/-- The same atom is retained by restriction to the half-open period. -/
theorem traceCyclicParameterTurn_singleton_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    traceCyclicParameterTurn {((i.val : ℝ) + s)} =
      ENNReal.ofReal (chordSelectedAngle (traceRotationBasis i.val) s -
        chordLeftSelectedAngle (traceRotationBasis i.val) s) := by
  have hi : (i.val : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [traceCyclicParameterTurn,
    angleTurnMeasureOn_apply_of_subset _ _ _ _
      (singleton_subset_iff.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
  exact traceCyclicTurn_singleton_at_chord i s hs

theorem traceCyclicParameterTurn_singleton_at_chord_toReal (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    (traceCyclicParameterTurn {((i.val : ℝ) + s)}).toReal =
      chordSelectedAngle (traceRotationBasis i.val) s -
        chordLeftSelectedAngle (traceRotationBasis i.val) s := by
  rw [traceCyclicParameterTurn_singleton_at_chord i s hs,
    ENNReal.toReal_ofReal (sub_nonneg.mpr
      (chord_leftSelectedAngle_le_selected (traceRotationBasis i.val) traceAxisLength s
        (norm_traceRotationBasis_zero i) (norm_traceRotationBasis_one i)
        (norm_traceRotationBasis_sub_lt i) ⟨hs.1.le, hs.2⟩))]

end Markov
