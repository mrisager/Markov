import Markov.Transfer
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! The actual full geodesic-length variable in the paper. Its squared
main-term correction is uniformly bounded, without any orbit assumption. -/
noncomputable section
open Filter Asymptotics
namespace Markov

def t1_markovLength (x : ℝ) : ℝ := 2 * Real.arcosh (3*x/2)

theorem t1_arcosh_log_gap (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Real.log (2*y) - Real.arcosh y ∧
      Real.log (2*y) - Real.arcosh y ≤ 1/y := by
  have hy0 : 0 < y := by linarith
  let b := y + Real.sqrt (y^2-1)
  have hs0 := Real.sqrt_nonneg (y^2-1)
  have hs2 := Real.sq_sqrt (show 0 ≤ y^2-1 by nlinarith)
  have hsu : Real.sqrt (y^2-1) ≤ y := by nlinarith
  have hsl : y-1 ≤ Real.sqrt (y^2-1) := by nlinarith
  have hb : y ≤ b := by dsimp [b]; linarith
  have hb0 : 0 < b := hy0.trans_le hb
  have hb2 : b ≤ 2*y := by dsimp [b]; linarith
  have hgap : 2*y-b ≤ 1 := by dsimp [b]; linarith
  change 0 ≤ Real.log (2*y) - Real.log b ∧
    Real.log (2*y) - Real.log b ≤ 1/y
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hb0 hb2)
  · calc
      _ = Real.log (2*y/b) := (Real.log_div (by positivity) hb0.ne').symm
      _ ≤ 2*y/b-1 := Real.log_le_sub_one_of_pos (div_pos (by positivity) hb0)
      _ = (2*y-b)/b := by field_simp
      _ ≤ 1/b := div_le_div_of_nonneg_right hgap hb0.le
      _ ≤ 1/y := one_div_le_one_div_of_le hy0 hb

theorem t1_arcosh_square_log_gap (y : ℝ) (hy : 1 ≤ y) :
    |(2 * Real.arcosh y)^2 - (2 * Real.log (2*y))^2| ≤ 16 := by
  obtain ⟨hg0, hg1⟩ := t1_arcosh_log_gap y hy
  have hy0 : 0 < y := by linarith
  have ha0 := Real.arcosh_nonneg hy
  have hl0 : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hlu : Real.log (2*y) ≤ 2*y := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hp : (Real.log (2*y) - Real.arcosh y) *
      (Real.log (2*y) + Real.arcosh y) ≤ (1/y) * (2 * Real.log (2*y)) :=
    mul_le_mul hg1 (by linarith) (by linarith) (by positivity)
  have hu : (1/y) * (2 * Real.log (2*y)) ≤ 4 := by
    have hid : (1/y)*(2*Real.log (2*y)) = (2*Real.log (2*y))/y := by ring
    rw [hid]
    exact (div_le_iff₀ hy0).mpr (by linarith)
  rw [abs_of_nonpos (by nlinarith :
    (2 * Real.arcosh y)^2 - (2 * Real.log (2*y))^2 ≤ 0)]
  nlinarith

theorem t1_markovLength_square_error (x : ℝ) (hx : 1 ≤ x) :
    |t1_markovLength x ^ 2 - (2 * Real.log (3*x))^2| ≤ 16 := by
  have h := t1_arcosh_square_log_gap (3*x/2) (by linarith)
  have hid : 2*(3*x/2) = 3*x := by ring
  simpa only [t1_markovLength, hid] using h

theorem t1_markovLength_square_error_isBigO_one :
    (fun x => t1_markovLength x ^ 2 - (2 * Real.log (3*x))^2) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (c := 16)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using t1_markovLength_square_error x hx

end Markov
