import T1GeometricYCutoff
import T1PowerCutoffEnvelopeTerm
import T1PrimitiveErrorScales

/-! The exact conditional primitive error rate follows from an explicit
power saving for the genuine summatory Möbius function. This module does
not prove that power saving from the zero-free half-plane hypothesis. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_primitiveConditional_of_mertens_power (δ : ℝ) (hδ : 0 < δ)
    (hM : t1_MertensPowerBound δ) :
    (fun R : ℝ => (t1_geometricPrimitiveCount R : ℝ) -
      (6*modularMcShaneRivinArea/Real.pi^2)*R^2) =O[atTop] primitiveConditionalScale := by
  obtain ⟨C,hC,T,hT,hcut⟩ := t1_geometric_primitive_Y_cutoff
  obtain ⟨K,hK,N,hEnv⟩ := t1_mertens_power_implies_envelope δ hδ hM
  let ε := cutoffExponent δ
  have hε0 : 0 < ε := (cutoffExponent_spec δ hδ).1
  have hε1 : ε < 1 := t1_cutoffExponent_lt_one δ hδ
  have hsmall := (t1_power_saving_isLittleO_primitiveConditional δ hδ).bound
    (c := 1) (by norm_num)
  apply IsBigO.of_bound (C*(ε^(-(1 : ℝ)/2)+K*2^δ))
  filter_upwards [t1_powerCutoff_eventually_admissible ε hε0 hε1 T N,hsmall]
    with R hR hsmallR
  have hR0 : 0 < R := by linarith [hR.1]
  have hE := t1_primitiveConditionalScale_pos R hR.1
  have hp : R^(1-δ/2) ≤ primitiveConditionalScale R := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hR0.le (1-δ/2)),
      abs_of_pos hE,one_mul] using hsmallR
  have hpt := hcut R (R^ε) hR.2.1 hR.2.2.1
  have ht := t1_powerCutoff_envelope_term R δ K hR.1 hδ hK.le hR.2.2.1
    (hEnv _ hR.2.2.2)
  have ht' : R*R^ε*t1_mertensEnvelope (t1_realCutoff R (R^ε)) ≤
      K*2^δ*primitiveConditionalScale R :=
    ht.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  rw [t1_power_cutoff_head_identity R ε hR.1 hε0] at hpt
  have hbound : |(t1_geometricPrimitiveCount R : ℝ) -
      (6*modularMcShaneRivinArea/Real.pi^2)*R^2| ≤
      C*(ε^(-(1 : ℝ)/2)+K*2^δ)*primitiveConditionalScale R := by
    calc
      _ ≤ C*(ε^(-(1 : ℝ)/2)*primitiveConditionalScale R+
          R*R^ε*t1_mertensEnvelope (t1_realCutoff R (R^ε))) := hpt
      _ ≤ C*(ε^(-(1 : ℝ)/2)*primitiveConditionalScale R+
          K*2^δ*primitiveConditionalScale R) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl ht') hC.le
      _ = _ := by ring
  simpa only [Real.norm_eq_abs,abs_of_pos hE] using hbound

end Markov
