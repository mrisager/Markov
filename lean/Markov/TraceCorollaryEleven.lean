import Markov.TraceRadialBlockFiniteSum
import Markov.PrimitiveEuclideanDirections
import Markov.TraceWeightedGeneral

/-! The full signed primitive-block sum in the original Corollary 11. -/

noncomputable section
open Classical
namespace Markov

/-- The full primitive-block sum reduces to the actual unresolved weighted
sum and an explicit logarithmic lattice error. -/
theorem trace_radial_block_full_sum_le
    (S Q K H ε η : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q) (hK : 1 ≤ K)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H))) :
    (∑ d ∈ primitiveEuclideanDirectionsUpTo K, ‖traceRadialBlock S Q d‖) ≤
      7 * S * (∑ d ∈ primitiveUnresolvedUpTo K H η K,
        traceUnresolvedArcLength d K H η / intEuclidean d) +
      700 * Real.pi * Real.log (2 * K) / η := by
  have hb := trace_radial_block_finite_sum_le (primitiveEuclideanDirectionsUpTo K)
    S Q K H ε η hS hQ hH hε hη hbasic
    (fun d hd => ((mem_primitiveEuclideanDirectionsUpTo K d).mp hd).1)
    (fun d hd => ((mem_primitiveEuclideanDirectionsUpTo K d).mp hd).2)
  rw [primitiveEuclideanDirectionsUpTo_filter_unresolved] at hb
  have hn := primitiveEuclideanDirectionsUpTo_reciprocal_square_le_log K hK
  have hc : 0 ≤ 14 * Real.pi / η := by positivity
  have he := mul_le_mul_of_nonneg_left hn hc
  have heq : (14 * Real.pi / η) * (50 * Real.log (2 * K)) =
      700 * Real.pi * Real.log (2 * K) / η := by ring
  rw [heq] at he
  exact hb.trans (add_le_add_right he _)

/-- Corollary 11 for the constructed trace ball, for every full primitive
cutoff. The height threshold and all constants are independent of `K,Q,ε,η`. -/
theorem trace_corollary11 :
    ∃ C c H0 : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ H0 ∧
      ∀ S Q K H ε η : ℝ,
      8 / traceEuclideanInradius + 1 ≤ S → 0 < Q → 1 ≤ K → H0 ≤ H →
      0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength * H)) →
      (∑ d ∈ primitiveEuclideanDirectionsUpTo K, ‖traceRadialBlock S Q d‖) ≤
        C * (Real.log (2 * K) / η + S / (H * Real.sqrt H) +
          S * K * Real.exp (-(c * H))) := by
  obtain ⟨Cw, c, H0, hCw, hc, hH0, hw⟩ := trace_weighted_unresolved_general
  let C := 700 * Real.pi + 7 * Cw + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, H0, hC, hc, hH0, ?_⟩
  intro S Q K H ε η hS hQ hK hH hε hη hbasic
  have hHone : 1 ≤ H := hH0.trans hH
  have hSp : 0 < S := trace_radial_scale_pos_of_threshold hS
  have hHp : 0 < H := by linarith
  have hlog : 0 ≤ Real.log (2 * K) / η :=
    div_nonneg (Real.log_nonneg (by linarith)) hη.le
  have hmain : 0 ≤ S / (H * Real.sqrt H) := by positivity
  have hexp : 0 ≤ S * K * Real.exp (-(c * H)) := by positivity
  have hcoeff : 0 ≤ 7 * S := by positivity
  have hweight := hw K H ε η hK hH hε hη (by simpa only [neg_mul] using hbasic)
  have hbound := trace_radial_block_full_sum_le S Q K H ε η
    hS hQ hK hHone hε hη hbasic
  calc
    _ ≤ 7 * S * (Cw * (1 / (H * Real.sqrt H) + K * Real.exp (-(c * H)))) +
        700 * Real.pi * Real.log (2 * K) / η :=
      hbound.trans (add_le_add_left (mul_le_mul_of_nonneg_left hweight hcoeff) _)
    _ = (700 * Real.pi) * (Real.log (2 * K) / η) +
        (7 * Cw) * (S / (H * Real.sqrt H)) +
        (7 * Cw) * (S * K * Real.exp (-(c * H))) := by ring
    _ ≤ C * (Real.log (2 * K) / η) + C * (S / (H * Real.sqrt H)) +
        C * (S * K * Real.exp (-(c * H))) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hlog
        · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Real.pi_pos]) hmain
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Real.pi_pos]) hexp
    _ = _ := by ring

end Markov
