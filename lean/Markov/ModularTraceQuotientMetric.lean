import Markov.ModularTraceCovering
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-! The actual hyperbolic orbit metric, with the original quotient topology.
The orbit-distance minimum is attained, projection is locally an isometry,
and the quotient metric is proper and complete. No closed-geodesic
realization or geometric-norm identification is asserted. -/
noncomputable section
open scoped MatrixGroups Pointwise
open Set Metric Topology
namespace Markov

private theorem modularTrace_orbit_nonempty (y : UpperHalfPlane) :
    (MulAction.orbit modularTraceSubgroup y).Nonempty :=
  ⟨y, MulAction.mem_orbit_self y⟩

/-- Actual orbits are closed, because they are fibers of the proved Hausdorff quotient. -/
theorem modularTrace_orbit_isClosed (y : UpperHalfPlane) :
    IsClosed (MulAction.orbit modularTraceSubgroup y) := by
  letI : T2Space ModularTraceQuotient := modularTraceQuotient_isT2
  have heq : MulAction.orbit modularTraceSubgroup y =
      modularTraceQuotientMk ⁻¹' {modularTraceQuotientMk y} := by
    ext x
    exact (modularTraceQuotientMk_eq_iff x y).symm
  rw [heq]
  exact isClosed_singleton.preimage modularTraceQuotientMk_continuous

/-- The point-to-orbit infimum in the actual hyperbolic metric. -/
def modularTraceOrbitDist (x y : UpperHalfPlane) : ℝ :=
  Metric.infDist x (MulAction.orbit modularTraceSubgroup y)

theorem modularTraceOrbitDist_nonneg (x y : UpperHalfPlane) :
    0 ≤ modularTraceOrbitDist x y := Metric.infDist_nonneg

theorem modularTraceOrbitDist_le (x y : UpperHalfPlane) (g : modularTraceSubgroup) :
    modularTraceOrbitDist x y ≤ dist x (g • y) :=
  Metric.infDist_le_dist_of_mem (MulAction.mem_orbit y g)

/-- Properness of H and closedness of the orbit make the infimum an actual minimum. -/
theorem modularTraceOrbitDist_attained (x y : UpperHalfPlane) :
    ∃ g : modularTraceSubgroup, modularTraceOrbitDist x y = dist x (g • y) := by
  obtain ⟨z, hz, heq⟩ := (modularTrace_orbit_isClosed y).exists_infDist_eq_dist
    (modularTrace_orbit_nonempty y) x
  obtain ⟨g, rfl⟩ := hz
  exact ⟨g, heq⟩

private theorem modularTraceOrbitDist_smul_left_le (g : modularTraceSubgroup)
    (x y : UpperHalfPlane) : modularTraceOrbitDist (g • x) y ≤ modularTraceOrbitDist x y := by
  obtain ⟨h, hh⟩ := modularTraceOrbitDist_attained x y
  calc
    _ ≤ dist (g • x) ((g * h) • y) := modularTraceOrbitDist_le _ _ _
    _ = dist x (h • y) := by rw [mul_smul, dist_smul]
    _ = _ := hh.symm

theorem modularTraceOrbitDist_smul_left (g : modularTraceSubgroup) (x y : UpperHalfPlane) :
    modularTraceOrbitDist (g • x) y = modularTraceOrbitDist x y := by
  apply le_antisymm (modularTraceOrbitDist_smul_left_le g x y)
  simpa only [inv_smul_smul] using modularTraceOrbitDist_smul_left_le g⁻¹ (g • x) y

private theorem modularTraceOrbitDist_smul_right_le (g : modularTraceSubgroup)
    (x y : UpperHalfPlane) : modularTraceOrbitDist x (g • y) ≤ modularTraceOrbitDist x y := by
  obtain ⟨h, hh⟩ := modularTraceOrbitDist_attained x y
  calc
    _ ≤ dist x ((h * g⁻¹) • (g • y)) := modularTraceOrbitDist_le _ _ _
    _ = dist x (h • y) := by simp only [mul_smul, inv_smul_smul]
    _ = _ := hh.symm

theorem modularTraceOrbitDist_smul_right (g : modularTraceSubgroup) (x y : UpperHalfPlane) :
    modularTraceOrbitDist x (g • y) = modularTraceOrbitDist x y := by
  apply le_antisymm (modularTraceOrbitDist_smul_right_le g x y)
  simpa only [inv_smul_smul] using modularTraceOrbitDist_smul_right_le g⁻¹ x (g • y)

private theorem modularTraceOrbitDist_comm_le (x y : UpperHalfPlane) :
    modularTraceOrbitDist x y ≤ modularTraceOrbitDist y x := by
  obtain ⟨g, hg⟩ := modularTraceOrbitDist_attained y x
  calc
    _ ≤ dist x (g⁻¹ • y) := modularTraceOrbitDist_le _ _ _
    _ = dist (g • x) y := by
      rw [← dist_smul g x (g⁻¹ • y), smul_inv_smul]
    _ = _ := (dist_comm _ _).trans hg.symm

theorem modularTraceOrbitDist_comm (x y : UpperHalfPlane) :
    modularTraceOrbitDist x y = modularTraceOrbitDist y x :=
  le_antisymm (modularTraceOrbitDist_comm_le x y) (modularTraceOrbitDist_comm_le y x)

theorem modularTraceOrbitDist_self (x : UpperHalfPlane) : modularTraceOrbitDist x x = 0 := by
  exact Metric.infDist_zero_of_mem (MulAction.mem_orbit_self x)

theorem modularTraceOrbitDist_triangle (x y z : UpperHalfPlane) :
    modularTraceOrbitDist x z ≤ modularTraceOrbitDist x y + modularTraceOrbitDist y z := by
  obtain ⟨g, hg⟩ := modularTraceOrbitDist_attained x y
  obtain ⟨h, hh⟩ := modularTraceOrbitDist_attained y z
  calc
    _ ≤ dist x ((g * h) • z) := modularTraceOrbitDist_le _ _ _
    _ ≤ dist x (g • y) + dist (g • y) ((g * h) • z) := dist_triangle _ _ _
    _ = _ := by rw [mul_smul, dist_smul, ← hg, ← hh]

theorem modularTraceOrbitDist_eq_zero_iff (x y : UpperHalfPlane) :
    modularTraceOrbitDist x y = 0 ↔ modularTraceQuotientMk x = modularTraceQuotientMk y := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := modularTraceOrbitDist_attained x y
    have heq : x = g • y := dist_eq_zero.mp (hg.symm.trans h)
    exact (modularTraceQuotientMk_eq_iff x y).mpr ⟨g, heq.symm⟩
  · intro h
    obtain ⟨g, rfl⟩ := (modularTraceQuotientMk_eq_iff x y).mp h
    rw [modularTraceOrbitDist_smul_left, modularTraceOrbitDist_self]

/-- The orbit distance, lifted to the existing actual topological orbit quotient. -/
def modularTraceQuotientDist : ModularTraceQuotient → ModularTraceQuotient → ℝ :=
  Quotient.lift₂ modularTraceOrbitDist (by
    intro x y x' y' hx hy
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := hy
    rw [modularTraceOrbitDist_smul_left, modularTraceOrbitDist_smul_right])

@[simp] theorem modularTraceQuotientDist_mk (x y : UpperHalfPlane) :
    modularTraceQuotientDist (modularTraceQuotientMk x) (modularTraceQuotientMk y) =
      modularTraceOrbitDist x y := rfl

/-- The lifted metric has exactly the original orbit-quotient topology. -/
theorem modularTraceQuotientDist_isOpen_iff (s : Set ModularTraceQuotient) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, modularTraceQuotientDist x y < ε → y ∈ s := by
  constructor
  · intro hs a ha
    obtain ⟨x, rfl⟩ := modularTraceQuotientMk_surjective a
    have hopen : IsOpen (modularTraceQuotientMk ⁻¹' s) :=
      hs.preimage modularTraceQuotientMk_continuous
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x ha
    refine ⟨ε, hε, ?_⟩
    intro b hb
    obtain ⟨y, rfl⟩ := modularTraceQuotientMk_surjective b
    obtain ⟨g, hg⟩ := modularTraceOrbitDist_attained x y
    have hnear : dist (g • y) x < ε := by
      rw [dist_comm, ← hg]
      exact hb
    have hgs : modularTraceQuotientMk (g • y) ∈ s := hball hnear
    simpa only [modularTraceQuotientMk_smul] using hgs
  · intro hs
    apply modularTraceQuotientMk_isQuotientMap.isOpen_preimage.mp
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε, hε, hball⟩ := hs (modularTraceQuotientMk x) hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    apply hball (modularTraceQuotientMk y)
    change modularTraceOrbitDist x y < ε
    exact (modularTraceOrbitDist_le x y 1).trans_lt (by simpa only [Metric.mem_ball, one_smul, dist_comm] using hy)

/-- The actual hyperbolic orbit metric, with definitionally unchanged quotient topology. -/
instance modularTraceQuotientMetricSpace : MetricSpace ModularTraceQuotient :=
  MetricSpace.ofDistTopology modularTraceQuotientDist
    (by intro x; induction x using Quotient.inductionOn with | _ x => exact modularTraceOrbitDist_self x)
    (by intro x y; induction x using Quotient.inductionOn with | _ x =>
          induction y using Quotient.inductionOn with | _ y => exact modularTraceOrbitDist_comm x y)
    (by intro x y z; induction x using Quotient.inductionOn with | _ x =>
          induction y using Quotient.inductionOn with | _ y =>
          induction z using Quotient.inductionOn with | _ z => exact modularTraceOrbitDist_triangle x y z)
    modularTraceQuotientDist_isOpen_iff
    (by intro x y; induction x using Quotient.inductionOn with | _ x =>
          induction y using Quotient.inductionOn with | _ y => exact (modularTraceOrbitDist_eq_zero_iff x y).mp)

@[simp] theorem modularTraceQuotient_dist_mk (x y : UpperHalfPlane) :
    dist (modularTraceQuotientMk x) (modularTraceQuotientMk y) = modularTraceOrbitDist x y := rfl

/-- The genuine projection never increases hyperbolic distance. -/
theorem modularTraceQuotientMk_dist_le (x y : UpperHalfPlane) :
    dist (modularTraceQuotientMk x) (modularTraceQuotientMk y) ≤ dist x y := by
  simpa only [modularTraceQuotient_dist_mk, one_smul] using modularTraceOrbitDist_le x y 1

/-- The quotient-distance minimum is represented by an actual deck transform. -/
theorem modularTraceQuotient_dist_attained (x y : UpperHalfPlane) :
    ∃ g : modularTraceSubgroup,
      dist (modularTraceQuotientMk x) (modularTraceQuotientMk y) = dist x (g • y) :=
  modularTraceOrbitDist_attained x y

/-- On a sufficiently small genuine hyperbolic ball, projection preserves
all pairwise distances. The radius comes from the proved free covering action. -/
theorem modularTraceQuotientMk_local_dist_eq (x : UpperHalfPlane) :
    ∃ r > 0, ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
      dist (modularTraceQuotientMk y) (modularTraceQuotientMk z) = dist y z := by
  obtain ⟨U, hU, hdisj⟩ := modularTraceQuotientMk_isQuotientCoveringMap.disjoint x
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 3, by positivity, ?_⟩
  intro y hy z hz
  change dist y x < ε / 3 at hy
  change dist z x < ε / 3 at hz
  obtain ⟨g, hg⟩ := modularTraceQuotient_dist_attained y z
  have hle : dist y (g • z) ≤ dist y z := by
    rw [← hg]
    exact modularTraceQuotientMk_dist_le y z
  have hzU : z ∈ U := hεU (show dist z x < ε by linarith)
  have hgzU : g • z ∈ U := by
    apply hεU
    have ht1 := dist_triangle (g • z) y x
    have ht2 := dist_triangle y x z
    rw [dist_comm (g • z) y] at ht1
    rw [dist_comm x z] at ht2
    change dist (g • z) x < ε
    linarith
  have hg1 : g = 1 := hdisj g ⟨g • z, ⟨z, hzU, rfl⟩, hgzU⟩
  simpa only [hg1, one_smul] using hg

/-- A bundled isometry on a neighborhood of each point, for the actual
quotient metric and the original quotient topology. -/
theorem modularTraceQuotientMk_local_isometry (x : UpperHalfPlane) :
    ∃ r > 0, Isometry (fun y : Metric.ball x r => modularTraceQuotientMk y.val) := by
  obtain ⟨r, hr, heq⟩ := modularTraceQuotientMk_local_dist_eq x
  exact ⟨r, hr, Isometry.of_dist_eq (fun y z => heq y.val y.property z.val z.property)⟩

/-- The literal infimum-over-deck-transformations formula. -/
theorem modularTraceQuotient_dist_eq_sInf (x y : UpperHalfPlane) :
    dist (modularTraceQuotientMk x) (modularTraceQuotientMk y) =
      sInf (Set.range (fun g : modularTraceSubgroup => dist x (g • y))) := by
  rw [modularTraceQuotient_dist_mk]
  have heq : (dist x ·) '' MulAction.orbit modularTraceSubgroup y =
      Set.range (fun g : modularTraceSubgroup => dist x (g • y)) := by
    ext r
    constructor
    · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g • y, MulAction.mem_orbit y g, rfl⟩
  have hglb := Metric.isGLB_infDist (x := x) (modularTrace_orbit_nonempty y)
  rw [heq] at hglb
  exact (hglb.csInf_eq (Set.range_nonempty _)).symm

/-- Every metric ball downstairs is exactly the projection of the ball upstairs. -/
theorem modularTraceQuotientMk_image_ball (x : UpperHalfPlane) (r : ℝ) :
    modularTraceQuotientMk '' Metric.ball x r = Metric.ball (modularTraceQuotientMk x) r := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (modularTraceQuotientMk_dist_le y x).trans_lt hy
  · intro ha
    obtain ⟨y, rfl⟩ := modularTraceQuotientMk_surjective a
    obtain ⟨g, hg⟩ := modularTraceQuotient_dist_attained x y
    refine ⟨g • y, ?_, modularTraceQuotientMk_smul g y⟩
    change dist (g • y) x < r
    rw [dist_comm, ← hg, dist_comm]
    exact ha

/-- The analogous closed-ball equality uses attainment, not merely an approximate infimum. -/
theorem modularTraceQuotientMk_image_closedBall (x : UpperHalfPlane) (r : ℝ) :
    modularTraceQuotientMk '' Metric.closedBall x r =
      Metric.closedBall (modularTraceQuotientMk x) r := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (modularTraceQuotientMk_dist_le y x).trans hy
  · intro ha
    obtain ⟨y, rfl⟩ := modularTraceQuotientMk_surjective a
    obtain ⟨g, hg⟩ := modularTraceQuotient_dist_attained x y
    refine ⟨g • y, ?_, modularTraceQuotientMk_smul g y⟩
    change dist (g • y) x ≤ r
    rw [dist_comm, ← hg, dist_comm]
    exact ha

/-- The actual quotient metric is proper, since its closed balls are
continuous images of genuine compact hyperbolic closed balls. -/
instance modularTraceQuotientProperSpace : ProperSpace ModularTraceQuotient where
  isCompact_closedBall a r := by
    obtain ⟨x, rfl⟩ := modularTraceQuotientMk_surjective a
    rw [← modularTraceQuotientMk_image_closedBall]
    exact (isCompact_closedBall x r).image modularTraceQuotientMk_continuous

instance modularTraceQuotientCompleteSpace : CompleteSpace ModularTraceQuotient := inferInstance

end Markov
