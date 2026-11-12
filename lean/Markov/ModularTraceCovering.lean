import Markov.ModularTraceCongruence
import Markov.ModularProperDiscontinuity
import Markov.HyperbolicFixedPointTrace

/-! Freeness and the actual covering projection for the generated modular
subgroup. No commutator/index, torus topology or geodesic marking is assumed. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem modularInteger_real_injective :
    Function.Injective (fun g : SL(2, ℤ) => (g : SL(2, ℝ))) := by
  intro g h heq
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun k : SL(2, ℝ) => k i j) heq
  change ((g i j : ℤ) : ℝ) = ((h i j : ℤ) : ℝ) at hh
  exact_mod_cast hh

/-- The actual integral trace subgroup has no nonidentity element fixing
an upper-half-plane point. The arithmetic and real fixed-point bounds are proved. -/
theorem modularTraceSubgroup_eq_one_of_fixed_point
    (g : SL(2, ℤ)) (hg : g ∈ modularTraceSubgroup)
    (z : UpperHalfPlane) (hz : g • z = z) : g = 1 := by
  let gr : SL(2, ℝ) := g
  have hz' : gr • z = z := by
    rw [← modularInteger_smul_eq_real]
    exact hz
  have htr : (gr : Matrix (Fin 2) (Fin 2) ℝ).trace =
      ((g : IntMatrixTwo).trace : ℝ) := by
    simp [gr, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  have hlo : (2 : ℝ) ≤ |(gr : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
    rw [htr]
    exact_mod_cast modularTraceSubgroup_trace_abs_ge_two g hg
  have hhi := sl_fixed_point_trace_sq_le_four gr z hz'
  have heq : (gr : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4 := by
    nlinarith [sq_abs (gr : Matrix (Fin 2) (Fin 2) ℝ).trace]
  rcases sl_fixed_point_eq_one_or_neg_one_of_trace_sq_eq_four gr z hz' heq with hpos | hneg
  · apply modularInteger_real_injective
    simpa [gr] using hpos
  · have hneg' : g = -1 := by
      apply modularInteger_real_injective
      simpa [gr] using hneg
    exact (neg_one_not_mem_modularTraceSubgroup (hneg' ▸ hg)).elim

instance modularTraceSubgroup_isCancelSMul :
    IsCancelSMul modularTraceSubgroup UpperHalfPlane := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g z hz
  apply Subtype.ext
  exact modularTraceSubgroup_eq_one_of_fixed_point g.val g.property z hz

theorem modularTraceSubgroup_stabilizer_eq_bot (z : UpperHalfPlane) :
    MulAction.stabilizer modularTraceSubgroup z = ⊥ :=
  IsCancelSMul.stabilizer_eq_bot z

/-- The explicitly constructed orbit projection is a quotient covering map
for the genuine generated subgroup action. -/
theorem modularTraceQuotientMk_isQuotientCoveringMap :
    IsQuotientCoveringMap modularTraceQuotientMk modularTraceSubgroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem modularTraceQuotientMk_isCoveringMap : IsCoveringMap modularTraceQuotientMk :=
  modularTraceQuotientMk_isQuotientCoveringMap.isCoveringMap

end Markov
