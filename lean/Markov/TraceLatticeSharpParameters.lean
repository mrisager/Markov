import Markov.TraceSmoothedSharpBound
import Markov.TraceLatticeDiscrepancy

/-! The original Theorem 12 discrepancy inequality before choosing its
parameters, for the actual full constructed trace-lattice count and area. -/

noncomputable section
namespace Markov

theorem trace_lattice_sharp_parameter_bound :
    ∃ C c H0 : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ H0 ∧
      ∀ R Q K H ε η : ℝ,
      8 / traceEuclideanInradius + 1 ≤ R - traceEuclideanGaugeConstant / Q →
      0 < Q → 1 ≤ K → H0 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength * H)) →
      |(traceLatticeCount R : ℝ) - R ^ 2 * traceEuclideanArea| ≤
        C * (Real.log (2 * K) / η + R / (H * Real.sqrt H) +
          R * K * Real.exp (-(c * H)) + R / Q + R * Q ^ 3 / K ^ 2) := by
  obtain ⟨Cs, c, H0, hCs, hc, hH0, hsharp⟩ := trace_smoothed_lattice_sharp_parameter_bound
  let D := 3 * traceEuclideanArea * traceEuclideanGaugeConstant
  have hD : 0 < D := mul_pos (mul_pos (by norm_num) traceEuclideanArea_pos)
    traceEuclideanGaugeConstant_pos
  let C := D + 2 * Cs + 1
  refine ⟨C, c, H0, by dsimp [C]; positivity, hc, hH0, ?_⟩
  intro R Q K H ε η hR hQ hK hH hε hη hbasic
  let e := traceEuclideanGaugeConstant / Q
  have he : 0 < e := div_pos traceEuclideanGaugeConstant_pos hQ
  have hminus : 0 < R - e := trace_radial_scale_pos_of_threshold hR
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one (hH0.trans hH)
  have hA : 0 ≤ Real.log (2 * K) / η :=
    div_nonneg (Real.log_nonneg (by linarith)) hη.le
  have hB : 0 ≤ R / (H * Real.sqrt H) := by positivity
  have hE : 0 ≤ R * K * Real.exp (-(c * H)) := by positivity
  have hT : 0 ≤ R * Q ^ 3 / K ^ 2 := by positivity
  have hV : 0 ≤ R / Q := by positivity
  let P := Real.log (2 * K) / η + R / (H * Real.sqrt H) +
    R * K * Real.exp (-(c * H)) + R * Q ^ 3 / K ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hlocal (S : ℝ) (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hSR : S ≤ 2 * R) :
      |traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea| ≤ 2 * Cs * P := by
    have hb := hsharp S Q K H ε η hS hQ hK hH hε hη hbasic
    calc
      _ ≤ Cs * (Real.log (2 * K) / η + (2 * R) / (H * Real.sqrt H) +
          (2 * R) * K * Real.exp (-(c * H)) + (2 * R) * Q ^ 3 / K ^ 2) := by
        apply hb.trans
        gcongr
      _ = 2 * Cs * P - Cs * (Real.log (2 * K) / η) := by dsimp [P]; ring
      _ ≤ _ := sub_le_self _ (mul_nonneg hCs.le hA)
  have hEminus := hlocal (R - e) hR (by linarith)
  have hSplus : 8 / traceEuclideanInradius + 1 ≤ R + e := by
    change 8 / traceEuclideanInradius + 1 ≤ R - e at hR
    linarith
  have hEplus := hlocal (R + e) hSplus (by linarith)
  have hsand := traceSmoothingSandwich_latticeCount R Q hQ hminus
  have hmain := smoothing_quadratic_mainterm_bounds traceEuclideanArea R e
    traceEuclideanArea_pos.le he.le (by linarith)
  have hcount : |(traceLatticeCount R : ℝ) - R ^ 2 * traceEuclideanArea| ≤
      3 * traceEuclideanArea * R * e + 2 * Cs * P := by
    change traceSmoothedLatticeCount (R - e) Q ≤ (traceLatticeCount R : ℝ) ∧
      (traceLatticeCount R : ℝ) ≤ traceSmoothedLatticeCount (R + e) Q at hsand
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hEminus).1, (abs_le.mp hEplus).2,
      (abs_le.mp hmain.1).1, (abs_le.mp hmain.2).2, hsand.1, hsand.2]
  calc
    _ ≤ 3 * traceEuclideanArea * R * e + 2 * Cs * P := hcount
    _ = D * (R / Q) + (2 * Cs) * P := by dsimp [D, e]; ring
    _ ≤ C * (R / Q) + C * P := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hV
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hP
    _ = _ := by dsimp [P]; ring

end Markov
