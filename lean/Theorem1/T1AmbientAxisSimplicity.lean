import T1AmbientConjugation
import Markov.PrimitiveAxisTraceNorm

/-! Actual ambient modular conjugation transports projected-axis simplicity.
The existing geometric primitive-axis theorem then identifies its true period. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

theorem t1_ambientConjugation_projected_axis_injective
    (h : SL(2,ℤ)) (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hcg : 2 < |((t1_ambientConjugation h g).val : IntMatrixTwo).trace|)
    (hproj : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g))) :
    ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk
        (modularHyperbolicAxis (t1_ambientConjugation h g) hcg t))
      (Ioo b (b+modularClosedGeodesicPeriod (t1_ambientConjugation h g))) := by
  obtain ⟨c,hc⟩ := t1_ambientConjugation_axis h g hg hcg
  intro b s hs t ht he
  have hper := t1_ambientConjugation_period h g
  rw [hper] at hs ht
  have hs' : s+c ∈ Ioo (b+c) (b+c+modularClosedGeodesicPeriod g) := by
    constructor <;> linarith [hs.1,hs.2]
  have ht' : t+c ∈ Ioo (b+c) (b+c+modularClosedGeodesicPeriod g) := by
    constructor <;> linarith [ht.1,ht.2]
  change modularTraceQuotientMk (modularHyperbolicAxis (t1_ambientConjugation h g) hcg s) =
    modularTraceQuotientMk (modularHyperbolicAxis (t1_ambientConjugation h g) hcg t) at he
  rw [hc s,hc t] at he
  have he' := (t1_ambient_quotient_eq_iff h _ _).mp he
  exact add_right_cancel (hproj (b+c) hs' ht' he')

theorem t1_ambientConjugation_period_eq_primitive_norm
    (h : SL(2,ℤ)) (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hproj : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hp : IsCoprime (paperTraceAbelianizationCoordinates (t1_ambientConjugation h g)).toAdd.1
      (paperTraceAbelianizationCoordinates (t1_ambientConjugation h g)).toAdd.2) :
    modularClosedGeodesicPeriod g =
      ‖intVector traceBasis (paperTraceAbelianizationCoordinates (t1_ambientConjugation h g)).toAdd‖ := by
  have hcg : 2 < |((t1_ambientConjugation h g).val : IntMatrixTwo).trace| := by
    rw [t1_ambientConjugation_trace]
    exact hg
  have hproj' := t1_ambientConjugation_projected_axis_injective h g hg hcg hproj
  obtain ⟨a,_,ha,_⟩ := paperAxisSideCuts_exists_period_base_off (t1_ambientConjugation h g) hcg
  have he := paperAxisPrimitive_period_eq_trace_norm (t1_ambientConjugation h g)
    hcg a ha hproj' hp
  rwa [t1_ambientConjugation_period] at he

end Markov
