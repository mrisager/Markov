import Markov.TraceLemmaTen
import Markov.TraceLemmaEight

/-! The second directional-block estimate, obtained from the actual cap
bound. The unresolved term is the same finite component variation used by
the proved weighted unresolved-direction estimate. -/

noncomputable section
open Classical
namespace Markov

/-- The explicit resolved/unresolved form of the actual Lemma 10 block bound. -/
theorem trace_lemma10_covector (S Q K H ε η : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (k : ℤ × ℤ) (hk : k ≠ 0) (hK : intEuclidean k ≤ K) :
    ‖traceRadialBlock S Q k‖ ≤
      (7 * S / ‖euclideanIntDirection k‖) *
          (if IsTraceUnresolved k K H η then traceUnresolvedArcLength k K H η else 0) +
        14 * Real.pi / (η * ‖euclideanIntDirection k‖ ^ 2) := by
  classical
  have hSp := trace_radial_scale_pos_of_threshold hS
  have hkn : 0 < ‖euclideanIntDirection k‖ :=
    norm_pos_iff.mpr (euclideanIntDirection_ne_zero k hk)
  have hmesh := traceRadialMesh_pos S hSp k hk
  have hcap := trace_lemma8_covector K H ε η (traceRadialMesh S k)
    hH hε hη hmesh.le hbasic k hk hK
  have hcoef : 0 ≤ 7 * S / ‖euclideanIntDirection k‖ := by positivity
  calc
    _ ≤ (7 * S / ‖euclideanIntDirection k‖) *
        Metric.diam (traceConvexCap (traceRadialNormal k) (traceRadialMesh S k)) :=
      trace_lemma10_first S Q hS hQ k hk
    _ ≤ (7 * S / ‖euclideanIntDirection k‖) *
        ((if IsTraceUnresolved k K H η then traceUnresolvedArcLength k K H η else 0) +
          2 * Real.pi * traceRadialMesh S k / η) :=
      mul_le_mul_of_nonneg_left hcap hcoef
    _ = _ := by
      unfold traceRadialMesh
      field_simp
      ring

theorem trace_lemma10_resolved (S Q K H ε η : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (k : ℤ × ℤ) (hk : k ≠ 0) (hK : intEuclidean k ≤ K)
    (hu : ¬ IsTraceUnresolved k K H η) :
    ‖traceRadialBlock S Q k‖ ≤ 14 * Real.pi / (η * ‖euclideanIntDirection k‖ ^ 2) := by
  simpa only [if_neg hu, mul_zero, zero_add] using
    trace_lemma10_covector S Q K H ε η hS hQ hH hε hη hbasic k hk hK

theorem trace_lemma10_unresolved (S Q K H ε η : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (k : ℤ × ℤ) (hk : k ≠ 0) (hK : intEuclidean k ≤ K)
    (hu : IsTraceUnresolved k K H η) :
    ‖traceRadialBlock S Q k‖ ≤
      (7 * S / ‖euclideanIntDirection k‖) * traceUnresolvedArcLength k K H η +
        14 * Real.pi / (η * ‖euclideanIntDirection k‖ ^ 2) := by
  simpa only [if_pos hu] using
    trace_lemma10_covector S Q K H ε η hS hQ hH hε hη hbasic k hk hK

end Markov
