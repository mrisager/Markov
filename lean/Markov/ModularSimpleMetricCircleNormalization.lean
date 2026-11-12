import Markov.ModularMetricCircleAxisNormalization

/-! Actual embedding transfers exact parameter injectivity to the selected
axis provided by actual metric-circle normalization. -/
noncomputable section
open Set Topology
namespace Markov

/-- A literal embedded period circle has exactly the integer-period real
parameter identifications. -/
theorem modularMetricCircle_eq_iff_int_period
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (hq : IsClosedEmbedding q) (s t : ℝ) :
    q (s : AddCircle L) = q (t : AddCircle L) ↔
      ∃ n : ℤ, s - t = (n : ℝ) * L := by
  constructor
  · intro he
    have hst := hq.injective he
    have hz : ((s - t : ℝ) : AddCircle L) = 0 := by
      rw [AddCircle.coe_sub, hst, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := L)).mp hz
    exact ⟨n, by simpa only [zsmul_eq_mul] using hn.symm⟩
  · rintro ⟨n, hn⟩
    have hz : ((s - t : ℝ) : AddCircle L) = 0 :=
      (AddCircle.coe_eq_zero_iff (p := L)).mpr
        ⟨n, by simpa only [zsmul_eq_mul] using hn.symm⟩
    exact congrArg q (sub_eq_zero.mp (by simpa only [AddCircle.coe_sub] using hz))

/-- An actual closed embedded locally unit-speed period circle determines an
actual hyperbolic selected deck axis with the same period and the exact same
integer-period point identifications. Simplicity is transferred from the
supplied actual embedding, without a class or homology inference. -/
theorem modularSimpleMetricCircle_axis_normalization
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hq : IsClosedEmbedding q)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) :
    ∃ (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c : ℝ),
      modularClosedGeodesicPeriod D = L ∧
      (∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t + c)) ∧
      (∀ s t : ℝ, modularClosedGeodesic D hg s = modularClosedGeodesic D hg t ↔
        ∃ n : ℤ, s - t = (n : ℝ) * modularClosedGeodesicPeriod D) := by
  obtain ⟨z, F, D, hg, c, _, _, _, _, _, _, hlen, _, hphase⟩ :=
    modularMetricCircle_axis_normalization L hL q hloc
  refine ⟨D, hg, c, hlen, hphase, ?_⟩
  intro s t
  have hs : s - c + c = s := sub_add_cancel s c
  have ht : t - c + c = t := sub_add_cancel t c
  have he := modularMetricCircle_eq_iff_int_period L q hq (s - c) (t - c)
  rw [hphase, hphase, hs, ht] at he
  have hsub : (s - c) - (t - c) = s - t := by ring
  rwa [hsub, ← hlen] at he

end Markov
