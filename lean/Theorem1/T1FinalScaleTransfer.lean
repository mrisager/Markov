import T1ActualMarkovCountIdentity
import T1ScaleComposition
import T1ScaleGrowth
import T1PowerPrimitiveEstimate

/-! The exact final count transfer. The sole remaining input in each
transfer is the stated asymptotic estimate for the actual primitive count. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_transfer_actual_markov_rate (E F : ℝ → ℝ)
    (hP : (fun R => (t1_geometricPrimitiveCount R : ℝ) -
      t1_primitiveLeadingCoefficient*R^2) =O[atTop] E)
    (hEF : (fun x => E (t1_markovLength x)) =O[atTop] F)
    (hOne : (fun _ : ℝ => (1 : ℝ)) =O[atTop] F) :
    (fun x => count x - mainTerm t1_markovLeadingCoefficient x) =O[atTop] F := by
  have hPrim := (hP.comp_tendsto t1_markovLength_tendsto).trans hEF
  have hLength := t1_markovLength_square_error_isBigO_one.trans hOne
  have h := transfer_error_bound count (fun R => (t1_geometricPrimitiveCount R : ℝ))
    t1_markovLength (fun x => Real.log (3*x)) F t1_primitiveLeadingCoefficient
    t1_actual_markov_primitive_identity_eventually hPrim hLength hOne
  simpa only [mainTerm, t1_leadingCoefficient_div_three] using h

theorem t1_markovConditional_of_primitive
    (hP : (fun R => (t1_geometricPrimitiveCount R : ℝ) -
      t1_primitiveLeadingCoefficient*R^2) =O[atTop] primitiveConditionalScale) :
    ConditionalBound t1_markovLeadingCoefficient :=
  t1_transfer_actual_markov_rate _ _ hP t1_primitiveConditional_composed_isBigO
    t1_one_isBigO_conditionalScale

theorem t1_markovUnconditional_of_primitive
    (hP : (fun R => (t1_geometricPrimitiveCount R : ℝ) -
      t1_primitiveLeadingCoefficient*R^2) =O[atTop] primitiveUnconditionalScale) :
    UnconditionalBound t1_markovLeadingCoefficient :=
  t1_transfer_actual_markov_rate _ _ hP t1_primitiveUnconditional_composed_isBigO
    t1_one_isBigO_unconditionalScale

theorem t1_markovConditional_of_mertens_power (δ : ℝ) (hδ : 0 < δ)
    (hM : t1_MertensPowerBound δ) :
    ConditionalBound t1_markovLeadingCoefficient :=
  t1_markovConditional_of_primitive (t1_primitiveConditional_of_mertens_power δ hδ hM)

end Markov
