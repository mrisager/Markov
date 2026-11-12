import T1ReflectionAlgebra
import T1GeometricThreshold
import Markov.TraceCompatibility

/-! Trace reflection transports the already proved genuine primitive
length dictionary. No reflection agreement is supplied as a hypothesis. -/
noncomputable section
namespace Markov

theorem t1_primitive_exists_quadrantWordTrace (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ t : ℤ, QuadrantWordTrace p t := by
  obtain ⟨k,u,v,M,N,hh,hlabel⟩ := primitive_exists_quadrantSeededFarey p hp
  rcases hlabel with rfl | rfl
  · exact ⟨M.trace,k,p,v,M,N,hh,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨N.trace,k,u,p,M,N,hh,Or.inr ⟨rfl,rfl⟩⟩

theorem t1_quadrantWordTrace_geometricLength (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2)
    (t : ℤ) (h : QuadrantWordTrace p t) :
    t1_geometricLength p = 2 * Real.arcosh ((t : ℝ)/2) := by
  obtain ⟨k,u,v,M,N,hh,hlabel⟩ := h
  have hc := tracePlane_quadrantTraceLengthCompatible k hh
  rcases hlabel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · change modularMcShaneRivinNorm (euclideanIntDirection p) = _
    rw [modularMcShaneRivinNorm_primitive_trace_value _ hp,hc.1,
      mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.arcosh_cosh (by positivity)]
    ring
  · change modularMcShaneRivinNorm (euclideanIntDirection p) = _
    rw [modularMcShaneRivinNorm_primitive_trace_value _ hp,hc.2,
      mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.arcosh_cosh (by positivity)]
    ring

theorem t1_geometricLength_swap (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    t1_geometricLength (t1_latticeSwap p) = t1_geometricLength p := by
  obtain ⟨t,ht⟩ := t1_primitive_exists_quadrantWordTrace p hp
  have hp' : IsCoprime (t1_latticeSwap p).1 (t1_latticeSwap p).2 := hp.symm
  exact (t1_quadrantWordTrace_geometricLength (t1_latticeSwap p) hp' t
    (t1_quadrantWordTrace_reflection ht)).trans
    (t1_quadrantWordTrace_geometricLength p hp t ht).symm

end Markov
