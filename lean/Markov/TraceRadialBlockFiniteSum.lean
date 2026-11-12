import Markov.TraceLemmaTenCovector
import Markov.PrimitiveUnresolvedSet

/-! Summing the norms of complete positive-frequency radial blocks after
their internal cancellation has already been retained. -/

noncomputable section
open Classical
namespace Markov

/-- The finite form of the reduction in Corollary 11. Each summand is the
complete complex radial block, rather than an individual Fourier frequency. -/
theorem trace_radial_block_finite_sum_le
    (D : Finset (ℤ × ℤ)) (S Q K H ε η : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ D, intEuclidean d ≤ K) :
    (∑ d ∈ D, ‖traceRadialBlock S Q d‖) ≤
      7 * S * (∑ d ∈ D.filter (fun d => IsTraceUnresolved d K H η),
        traceUnresolvedArcLength d K H η / intEuclidean d) +
      (14 * Real.pi / η) * (∑ d ∈ D, 1 / intEuclidean d ^ 2) := by
  calc
    _ ≤ ∑ d ∈ D,
        ((7 * S / intEuclidean d) *
          (if IsTraceUnresolved d K H η then traceUnresolvedArcLength d K H η else 0) +
          14 * Real.pi / (η * intEuclidean d ^ 2)) := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [euclideanIntDirection_norm] using
        trace_lemma10_covector S Q K H ε η hS hQ hH hε hη hbasic d
          (primitiveIntDirection_ne_zero d (hprimitive d hd)) (hsize d hd)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ring

end Markov
