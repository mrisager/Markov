import T1ScaleComparison
import T1LengthAsymptotics

/-! Compare the primitive rates at the actual geodesic length with the
paper's Markov count error scales. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_primitiveConditional_composed_isBigO :
    (fun x => primitiveConditionalScale (t1_markovLength x)) =O[atTop] conditionalScale := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (3 : ℝ),Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with x hx hR
  obtain ⟨hlo,hhi⟩ := t1_markovLength_log_bounds x hx
  have h := t1_primitiveConditionalScale_compare (Real.log x) (t1_markovLength x) hR hlo hhi
  rw [t1_conditionalScale_log]
  simpa only [Real.norm_eq_abs,abs_of_pos (t1_primitiveConditionalScale_pos _ hR),
    abs_of_pos (t1_primitiveConditionalScale_pos _ (hR.trans_le hlo))] using h

theorem t1_primitiveUnconditional_composed_isBigO :
    (fun x => primitiveUnconditionalScale (t1_markovLength x)) =O[atTop] unconditionalScale := by
  apply IsBigO.of_bound (4*(2 : ℝ)^((1 : ℝ)/10))
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 4)] with x hx hR
  obtain ⟨hlo,hhi⟩ := t1_markovLength_log_bounds x hx
  have hp : Real.exp 1 < Real.log x :=
    (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ)<4)).trans_le hR
  have h := t1_primitiveUnconditionalScale_compare (Real.log x) (t1_markovLength x) hR hlo hhi
  rw [t1_unconditionalScale_log]
  simpa only [Real.norm_eq_abs,abs_of_pos (t1_primitiveUnconditionalScale_pos _ hp),
    abs_of_pos (t1_primitiveUnconditionalScale_pos _ (hp.trans_le hlo))] using h

end Markov
