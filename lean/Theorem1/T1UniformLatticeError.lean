import T1GeometricMobius
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A uniform large-radius error bound for the actual nonzero geometric
lattice count, derived from the completed unconditional Theorem 12. -/

noncomputable section
open Filter Asymptotics
namespace Markov

def t1_latticeErrorScale (R : ℝ) : ℝ := R / Real.log R ^ ((3 : ℝ) / 2)

def t1_nonzeroLatticeError (R : ℝ) : ℝ :=
  ((modularMcShaneRivinLatticeCount R - 1 : ℕ) : ℝ) - modularMcShaneRivinArea * R ^ 2

theorem t1_latticeErrorScale_pos {R : ℝ} (hR : 1 < R) : 0 < t1_latticeErrorScale R :=
  div_pos (zero_lt_one.trans hR) (Real.rpow_pos_of_pos (Real.log_pos hR) _)

theorem t1_one_isBigO_latticeErrorScale :
    (fun _ : ℝ => (1 : ℝ)) =O[atTop] t1_latticeErrorScale := by
  have hsmall := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) ((3 : ℝ) / 2) zero_lt_one
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hsmall.bound (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with R hb hR
  have hpow : 0 < Real.log R ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (Real.log_pos hR) _
  have hRpos : 0 < R := zero_lt_one.trans hR
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hpow, abs_of_pos hRpos,
    one_mul] at hb
  have hE : 1 ≤ t1_latticeErrorScale R := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [one_mul] using hb
  simpa only [norm_one, one_mul, Real.norm_eq_abs,
    abs_of_pos (t1_latticeErrorScale_pos hR)] using hE

theorem t1_nonzeroLatticeError_isBigO :
    t1_nonzeroLatticeError =O[atTop] t1_latticeErrorScale := by
  have hmain : (fun R : ℝ => (modularMcShaneRivinLatticeCount R : ℝ) -
      modularMcShaneRivinArea * R ^ 2) =O[atTop] t1_latticeErrorScale := by
    simpa only [modularMcShaneRivinArea, t1_latticeErrorScale] using
      modularMcShaneRivin_lattice_asymptotic
  have hbase := hmain.sub t1_one_isBigO_latticeErrorScale
  apply hbase.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hN : 1 ≤ modularMcShaneRivinLatticeCount R := t1_geometricLatticeCount_pos R hR
  simp only [t1_nonzeroLatticeError, Nat.cast_sub hN, Nat.cast_one]
  ring

/-- A single constant and threshold control every sufficiently large
radius in the genuine nonzero full count. This is a proved consequence of
Theorem 12, not a new analytic input. -/
theorem t1_uniform_nonzero_lattice_error :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 1 < T ∧
      ∀ R : ℝ, T ≤ R → |t1_nonzeroLatticeError R| ≤ C * t1_latticeErrorScale R := by
  obtain ⟨C, hC, hbound⟩ := t1_nonzeroLatticeError_isBigO.exists_pos
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hbound.bound
  refine ⟨C, hC, max T 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro R hR
  have hRgt : 1 < R := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_right T 2).trans hR)
  have h := hT R ((le_max_left T 2).trans hR)
  simpa only [Real.norm_eq_abs, abs_of_pos (t1_latticeErrorScale_pos hRgt)] using h

end Markov
