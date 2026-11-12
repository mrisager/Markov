import Markov.TraceStrictNormalOrder
import Markov.TraceEuclideanSupport
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Strict convexity of the actual trace norm and uniqueness of supporting
points of its actual Euclidean image ball. -/

noncomputable section
open Set

namespace Markov

/-- The constructed trace norm is strictly convex, because a common
norming functional at two unit points would give a common actual normal. -/
theorem tracePlane_strictConvexSpace : StrictConvexSpace ℝ TracePlane := by
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hxy hsum
  obtain ⟨f, hf⟩ := normingFunctionals_nonempty (x + y)
  have hfx : f x ≤ 1 := normingFunctional_on_unitBall (x + y) f hf x hx.le
  have hfy : f y ≤ 1 := normingFunctional_on_unitBall (x + y) f hf y hy.le
  have hval : f x + f y = 2 := by
    simpa only [map_add, hsum] using hf.2
  have hfx' : f ∈ normingFunctionals x := ⟨hf.1, by rw [hx]; linarith⟩
  have hfy' : f ∈ normingFunctionals y := ⟨hf.1, by rw [hy]; linarith⟩
  apply hxy
  exact traceBoundary_normal_point_unique hx hy
    (⟨x, rfl, f, hfx', rfl⟩ : normalizedEuclideanCovector traceBasis f ∈
      normalsOn traceBasis {x})
    (⟨y, rfl, f, hfy', rfl⟩ : normalizedEuclideanCovector traceBasis f ∈
      normalsOn traceBasis {y})

/-- The actual unit ball is strictly convex in its original trace norm. -/
theorem strictConvex_traceUnitBall :
    StrictConvex ℝ (Metric.closedBall (0 : TracePlane) 1) := by
  letI := tracePlane_strictConvexSpace
  exact strictConvex_closedBall ℝ 0 1

/-- Passing to the fixed Euclidean coordinates preserves the actual
body's strict convexity; this map is not asserted to preserve its norm. -/
theorem strictConvex_traceEuclideanBall : StrictConvex ℝ traceEuclideanBall := by
  exact strictConvex_traceUnitBall.linear_image traceEuclideanCoordinates.toLinearMap
    traceEuclideanEquiv.isOpenMap

/-- A nonzero Euclidean normal has at most one supporting point in the
actual Euclidean trace ball. -/
theorem traceEuclideanBall_supporting_points_unique
    {n x y : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0)
    (hx : x ∈ traceEuclideanBall) (hy : y ∈ traceEuclideanBall)
    (hsx : ∀ z ∈ traceEuclideanBall, inner ℝ z n ≤ inner ℝ x n)
    (hsy : ∀ z ∈ traceEuclideanBall, inner ℝ z n ≤ inner ℝ y n) : x = y := by
  by_contra hxy
  let g : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ n
  have hg (z : EuclideanSpace ℝ (Fin 2)) : g z = inner ℝ z n := real_inner_comm z n
  have heq : g x = g y := by
    rw [hg x, hg y]
    exact le_antisymm (hsy x hx) (hsx y hy)
  have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ interior traceEuclideanBall :=
    strictConvex_traceEuclideanBall hx hy hxy (by norm_num) (by norm_num) (by norm_num)
  have hmax : IsMaxOn g traceEuclideanBall ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
    intro z hz
    change g z ≤ g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
    rw [map_add, map_smul, map_smul, heq]
    norm_num only [smul_eq_mul, RingHom.id_apply]
    have hz' := hsy z hz
    rw [← hg z, ← hg y] at hz'
    linarith
  have hzero : g = 0 :=
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hm)).hasFDerivAt_eq_zero g.hasFDerivAt
  have hgnorm : ‖n‖ = 0 := by
    have key := congrArg norm hzero
    simpa only [g, innerSL_apply_norm, norm_zero] using key
  exact hn (norm_eq_zero.mp hgnorm)

/-- Every nonzero Euclidean direction has one and only one point attaining
the actual body's support height. -/
theorem traceEuclideanSupportHeight_exists_unique
    (n : EuclideanSpace ℝ (Fin 2)) (hn : n ≠ 0) :
    ∃! p, p ∈ traceEuclideanBall ∧ inner ℝ p n = traceEuclideanSupportHeight n := by
  obtain ⟨p, hp, hpeq⟩ := traceEuclideanSupportHeight_exists_mem n
  refine ⟨p, ⟨hp, hpeq⟩, ?_⟩
  rintro q ⟨hq, hqeq⟩
  apply traceEuclideanBall_supporting_points_unique hn hq hp
  · intro z hz
    rw [hqeq]
    exact inner_le_traceEuclideanSupportHeight n z hz
  · intro z hz
    rw [hpeq]
    exact inner_le_traceEuclideanSupportHeight n z hz

end Markov
