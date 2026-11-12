import Markov.TraceCorollaryEleven
import Markov.TraceFourierTail
import Markov.TracePrimitiveRayCutoff

/-! The actual smoothed trace-lattice discrepancy with the paper's sharp
radial-block and quantitative Fourier-tail errors. -/

noncomputable section
namespace Markov

/-- The finite-head/complete-ray cancellation and the quantitative tail
combine without taking individual Fourier norms on the head. -/
theorem trace_smoothed_lattice_sharp_parameter_bound :
    ∃ C c H0 : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ H0 ∧
      ∀ S Q K H ε η : ℝ,
      8 / traceEuclideanInradius + 1 ≤ S → 0 < Q → 1 ≤ K → H0 ≤ H →
      0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength * H)) →
      |traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea| ≤
        C * (Real.log (2 * K) / η + S / (H * Real.sqrt H) +
          S * K * Real.exp (-(c * H)) + S * Q ^ 3 / K ^ 2) := by
  obtain ⟨Cb, c, H0, hCb, hc, hH0, hb⟩ := trace_corollary11
  obtain ⟨Ct, hCt, ht⟩ := trace_fourier_tail_bound
  let C := Cb + Ct
  refine ⟨C, c, H0, by dsimp [C]; positivity, hc, hH0, ?_⟩
  intro S Q K H ε η hS hQ hK hH hε hη hbasic
  have hSp : 0 < S := trace_radial_scale_pos_of_threshold hS
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one (hH0.trans hH)
  have hsplit := trace_smoothed_lattice_discrepancy_primitive_cutoff_bound S Q K hSp hQ hK
  have hblock := hb S Q K H ε η hS hQ hK hH hε hη hbasic
  have htail := ht S Q K hSp hQ hK
  have hmain : 0 ≤ Real.log (2 * K) / η + S / (H * Real.sqrt H) +
      S * K * Real.exp (-(c * H)) := by
    have hlog : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith)
    positivity
  have hrest : 0 ≤ S * Q ^ 3 / K ^ 2 := by positivity
  calc
    _ ≤ Cb * (Real.log (2 * K) / η + S / (H * Real.sqrt H) +
        S * K * Real.exp (-(c * H))) + Ct * S * Q ^ 3 / K ^ 2 :=
      hsplit.trans (add_le_add hblock htail)
    _ = Cb * (Real.log (2 * K) / η + S / (H * Real.sqrt H) +
        S * K * Real.exp (-(c * H))) + Ct * (S * Q ^ 3 / K ^ 2) := by ring
    _ ≤ C * (Real.log (2 * K) / η + S / (H * Real.sqrt H) +
        S * K * Real.exp (-(c * H))) + C * (S * Q ^ 3 / K ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hmain
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hrest
    _ = _ := by ring

end Markov
