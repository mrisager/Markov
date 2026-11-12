import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! Local convex gluing for two adjacent cones of a planar fan.
The arithmetic input is the neighboring-ray inequality. This constructs a
convex extension for two pieces; no complete fan or trace-length norm is
claimed here. -/

namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The nonnegative cone spanned by two rays. -/
def twoRayCone (u v : E) : Set E :=
  {x | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v}

/-- The support plane on the opposite cone is below the first ray value
exactly when the neighboring-ray convexity inequality holds. -/
theorem fan_neighbor_inequality_iff (f g : E →ₗ[ℝ] ℝ) (u v w : E) (k : ℝ)
    (hu : f u = g u) (hrel : v + w = k • u) :
    k * f u ≤ f v + g w ↔ g v ≤ f v := by
  have hg := congrArg (fun x => g x) hrel
  simp only [map_add, map_smul, smul_eq_mul, ← hu] at hg
  constructor <;> intro h <;> linarith

/-- The same inequality controls the other neighboring ray. -/
theorem fan_neighbor_inequality_iff_other (f g : E →ₗ[ℝ] ℝ) (u v w : E) (k : ℝ)
    (hrel : v + w = k • u) :
    k * f u ≤ f v + g w ↔ f w ≤ g w := by
  have hf := congrArg (fun x => f x) hrel
  simp only [map_add, map_smul, smul_eq_mul] at hf
  constructor <;> intro h <;> linarith

/-- Ray comparison propagates throughout its nonnegative cone. -/
theorem linearMap_le_on_twoRayCone (f g : E →ₗ[ℝ] ℝ) (u v : E)
    (hu : g u = f u) (hv : g v ≤ f v) (x : E) (hx : x ∈ twoRayCone u v) :
    g x ≤ f x := by
  rcases hx with ⟨a, b, _, hb, rfl⟩
  simp only [map_add, map_smul, smul_eq_mul, hu]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hb)

/-- The convex extension used to glue two neighboring linear pieces. -/
def fanSupport (f g : E →ₗ[ℝ] ℝ) (x : E) : ℝ := max (f x) (g x)

theorem fanSupport_convexOn (f g : E →ₗ[ℝ] ℝ) :
    ConvexOn ℝ Set.univ (fanSupport f g) := by
  exact (f.convexOn convex_univ).sup (g.convexOn convex_univ)

/-- On one cone the maximum agrees exactly with its prescribed linear piece. -/
theorem fanSupport_eq_left (f g : E →ₗ[ℝ] ℝ) (u v : E)
    (hu : f u = g u) (hv : g v ≤ f v) (x : E) (hx : x ∈ twoRayCone u v) :
    fanSupport f g x = f x := by
  exact max_eq_left (linearMap_le_on_twoRayCone f g u v hu.symm hv x hx)

theorem fanSupport_eq_right (f g : E →ₗ[ℝ] ℝ) (u w : E)
    (hu : f u = g u) (hw : f w ≤ g w) (x : E) (hx : x ∈ twoRayCone u w) :
    fanSupport f g x = g x := by
  exact max_eq_right (linearMap_le_on_twoRayCone g f u w hu hw x hx)

/-- The neighboring-ray inequality gives an actual convex extension of both
homogeneous interpolants. This is the local fan convexity step. -/
theorem twoCone_convex_extension (f g : E →ₗ[ℝ] ℝ) (u v w : E) (k : ℝ)
    (hu : f u = g u) (hrel : v + w = k • u)
    (hfan : k * f u ≤ f v + g w) :
    ConvexOn ℝ Set.univ (fanSupport f g) ∧
      (∀ x ∈ twoRayCone u v, fanSupport f g x = f x) ∧
      (∀ x ∈ twoRayCone u w, fanSupport f g x = g x) := by
  refine ⟨fanSupport_convexOn f g, ?_, ?_⟩
  · intro x hx
    exact fanSupport_eq_left f g u v hu
      ((fan_neighbor_inequality_iff f g u v w k hu hrel).mp hfan) x hx
  · intro x hx
    exact fanSupport_eq_right f g u w hu
      ((fan_neighbor_inequality_iff_other f g u v w k hrel).mp hfan) x hx

/-- The local convex extension is positively homogeneous. -/
theorem fanSupport_smul (f g : E →ₗ[ℝ] ℝ) (r : ℝ) (hr : 0 ≤ r) (x : E) :
    fanSupport f g (r • x) = r * fanSupport f g x := by
  simp only [fanSupport, map_smul, smul_eq_mul]
  exact (mul_max_of_nonneg (f x) (g x) hr).symm

/-- A maximum of linear support functionals is subadditive. -/
theorem fanSupport_add_le (f g : E →ₗ[ℝ] ℝ) (x y : E) :
    fanSupport f g (x + y) ≤ fanSupport f g x + fanSupport f g y := by
  simp only [fanSupport, map_add]
  exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
    (add_le_add (le_max_right _ _) (le_max_right _ _))

end Markov
