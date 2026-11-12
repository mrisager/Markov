import Markov.TraceCornerEstimate
import Markov.PrimitiveAngularSpacing
import Mathlib.MeasureTheory.Measure.Real

/-! The eight actual corners of the first primitive height cutoff force
an upper bound on the uniform corner-mass scale. Consequently the basic
corner-separation hypothesis already makes the angular radius less than π/8. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Markov

/-- The first primitive height cutoff contains exactly eight directions. -/
theorem primitiveDirectionsUpTo_one_card : (primitiveDirectionsUpTo 1).card = 8 := by
  classical
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold primitiveDirectionsUpTo
  rw [show (-(↑(1 : ℕ)) : ℤ) = -1 from rfl, show ((1 : ℕ) : ℤ) = 1 from rfl, hI]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  have hn : (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) := by norm_num
  have hz : (0 : ℤ) ∉ ({1} : Finset ℤ) := by norm_num
  simp only [Finset.sum_insert hn, Finset.sum_insert hz, Finset.sum_singleton]
  norm_num

/-- Normalization distinguishes primitive integral directions in the actual
trace norm, including opposite primitive directions. -/
theorem trace_normalize_intVector_injective_primitive (p q : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) (hq : IsCoprime q.1 q.2)
    (heq : NormedSpace.normalize (intVector traceBasis p) =
      NormedSpace.normalize (intVector traceBasis q)) : p = q := by
  have hp0 : intVector traceBasis p ≠ 0 :=
    norm_pos_iff.mp (traceAxisLength_pos.trans_le (traceAxisLength_le_norm_intVector p hp))
  have h0 := congrArg (traceBasis.coord 0) heq
  have h1 := congrArg (traceBasis.coord 1) heq
  simp only [NormedSpace.normalize, map_smul, intVector, map_add,
    Module.Basis.coord_apply, Module.Basis.repr_self] at h0 h1
  simp only [Finsupp.single_apply, Fin.reduceEq, if_true, if_false,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h0 h1
  change ‖intVector traceBasis p‖⁻¹ * (p.1 : ℝ) =
    ‖intVector traceBasis q‖⁻¹ * (q.1 : ℝ) at h0
  change ‖intVector traceBasis p‖⁻¹ * (p.2 : ℝ) =
    ‖intVector traceBasis q‖⁻¹ * (q.2 : ℝ) at h1
  have hdetreal : (p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1 = 0 := by
    apply (mul_eq_zero.mp (show ‖intVector traceBasis p‖⁻¹ *
      ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1) = 0 from ?_)).resolve_left
      (inv_ne_zero (norm_ne_zero_iff.mpr hp0))
    calc
      _ = (‖intVector traceBasis p‖⁻¹ * (p.1 : ℝ)) * q.2 -
          (‖intVector traceBasis p‖⁻¹ * (p.2 : ℝ)) * q.1 := by ring
      _ = 0 := by rw [h0, h1]; ring
  have hdet : intDet p q = 0 := by
    unfold intDet
    exact_mod_cast hdetreal
  rcases primitive_intDet_zero_eq_or_eq_neg p q hp hq hdet with h | h
  · exact h.symm
  · have hneg : intVector traceBasis q = -intVector traceBasis p := by
      rw [h]
      simp only [intVector, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_smul, neg_add_rev]
      abel
    rw [hneg, NormedSpace.normalize_neg] at heq
    have htwo : (2 : ℝ) • NormedSpace.normalize (intVector traceBasis p) = 0 := by
      rw [two_smul]
      conv_lhs => lhs; rw [heq]
      exact neg_add_cancel _
    have hz : NormedSpace.normalize (intVector traceBasis p) = 0 :=
      (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact (hp0 ((NormedSpace.normalize_eq_zero_iff _).mp hz)).elim

/-- The actual height-one cutoff has eight distinct boundary corners. -/
theorem trace_cutoffCorners_one_card : (cutoffCorners traceBasis 1).card = 8 := by
  classical
  rw [cutoffCorners, Finset.card_image_iff.mpr ?_, primitiveDirectionsUpTo_one_card]
  intro p hp q hq heq
  exact trace_normalize_intVector_injective_primitive p q
    ((mem_primitiveDirectionsUpTo 1 p).mp hp).1
    ((mem_primitiveDirectionsUpTo 1 q).mp hq).1 heq

/-- Eight distinct actual cutoff atoms fit inside the full boundary turn 2π. -/
theorem trace_cutoff_corner_lower_scale_le_pi_div_four (H : ℝ) (hH : 1 ≤ H) :
    traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)) ≤ Real.pi / 4 := by
  classical
  let δ := traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))
  have hlower : ∀ x ∈ cutoffCorners traceBasis 1, δ ≤ (traceBoundaryTurn {x}).toReal := by
    intro x hx
    apply trace_real_cutoff_corner_atom_lower H x
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hcop, hheight⟩ := (mem_primitiveDirectionsUpTo 1 p).mp hp
    have hheight1 : intHeight p ≤ (1 : ℝ) := by simpa only [Nat.cast_one] using hheight
    exact ⟨p, hcop, hheight1.trans hH, hpx.symm⟩
  have hsum : 8 * δ ≤ (traceBoundaryTurn (↑(cutoffCorners traceBasis 1) : Set TracePlane)).toReal := by
    have hs := Finset.sum_le_sum hlower
    simpa only [Finset.sum_const, nsmul_eq_mul, trace_cutoffCorners_one_card,
      Nat.cast_ofNat, ← measureReal_def, sum_measureReal_singleton] using hs
  have htotal : (traceBoundaryTurn (↑(cutoffCorners traceBasis 1) : Set TracePlane)).toReal ≤
      2 * Real.pi := by
    have hm := ENNReal.toReal_mono (measure_ne_top traceBoundaryTurn univ)
      (measure_mono (Set.subset_univ (↑(cutoffCorners traceBasis 1) : Set TracePlane)))
    simpa only [traceBoundaryTurn_univ, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] using hm
  dsimp [δ] at hsum
  linarith

/-- The basic corner estimate in Lemma 8 forces its angular radius below π/8. -/
theorem trace_basic_angle_lt_pi_div_eight (H ε η : ℝ)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H))) : η < Real.pi / 8 := by
  have hscale := trace_cutoff_corner_lower_scale_le_pi_div_four H hH
  have hstrict : 2 * η < (2 + ε) * η := by nlinarith
  linarith

end Markov
