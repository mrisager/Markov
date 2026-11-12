import Markov.FrontierDecrease
import Mathlib.Topology.Order.MonotoneConvergence

/-! The actual finite convex Farey profiles have a decreasing, nonnegative
pointwise limit on the physical section. The limit is convex and interpolates
every canonical primitive length exactly. No norm or interpolation assumption
is used in these conclusions. -/

noncomputable section
open Filter
open scoped Topology

namespace Markov

/-- Convexity is preserved by finite-valued pointwise limits on a fixed
convex domain. No topology on the domain is needed. -/
theorem convexOn_of_pointwise_tendsto_real {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ) (s : Set E)
    (hconv : ∀ n : ℕ, ConvexOn ℝ s (f n))
    (hlim : ∀ x ∈ s, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (g x))) :
    ConvexOn ℝ s g := by
  refine ⟨(hconv 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ s := (hconv 0).1 hx hy ha hb hab
  have hsum := ((hlim x hx).const_mul a).add ((hlim y hy).const_mul b)
  have h := le_of_tendsto_of_tendsto' (hlim _ hxy) hsum (fun n => by
    simpa only [smul_eq_mul] using (hconv n).2 hx hy ha hb hab)
  simpa only [smul_eq_mul] using h

/-- The actual candidate profile, as the infimum over finite refinements. -/
def frontierLimitProfile (t : ℝ) : ℝ := ⨅ n : ℕ, frontierProfile n t

theorem frontierProfile_range_bddBelow (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    BddBelow (Set.range (fun n : ℕ => frontierProfile n t)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact frontierProfile_nonneg n t ht0 ht1

theorem frontierLimitProfile_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ frontierLimitProfile t :=
  le_ciInf (fun n => frontierProfile_nonneg n t ht0 ht1)

theorem frontierLimitProfile_le (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    frontierLimitProfile t ≤ frontierProfile n t :=
  ciInf_le (frontierProfile_range_bddBelow t ht0 ht1) n

/-- The actual decreasing finite profiles converge pointwise to their real
infimum, with lower boundedness derived from their positive edge data. -/
theorem frontierProfile_tendsto_limit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun n : ℕ => frontierProfile n t) atTop (𝓝 (frontierLimitProfile t)) := by
  exact tendsto_atTop_ciInf (frontierProfile_antitone t ht0 ht1)
    (frontierProfile_range_bddBelow t ht0 ht1)

/-- The constructed limit is convex on the complete closed section. -/
theorem frontierLimitProfile_convexOn : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) frontierLimitProfile := by
  apply convexOn_of_pointwise_tendsto_real frontierProfile frontierLimitProfile (Set.Icc 0 1)
  · intro n
    exact (frontierProfile_convexOn n).subset (Set.subset_univ _) (convex_Icc _ _)
  · intro t ht
    exact frontierProfile_tendsto_limit t ht.1 ht.2

/-- Exact interpolation of every canonical primitive direction by the
constructed convex limit. This equality is proved from eventual finite
interpolation and uniqueness of pointwise limits. -/
theorem frontierLimitProfile_interpolates (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    frontierLimitProfile (profileParameter p) = primitiveFareyLength p hp / profileMass p := by
  obtain ⟨N, hN⟩ := frontierProfile_eventual_interpolation p hp
  have hc : Tendsto (fun n : ℕ => frontierProfile n (profileParameter p)) atTop
      (𝓝 (primitiveFareyLength p hp / profileMass p)) := by
    apply tendsto_const_nhds.congr'
    exact eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).symm⟩
  exact tendsto_nhds_unique
    (frontierProfile_tendsto_limit _ (profileParameter_nonneg p hp) (profileParameter_le_one p hp)) hc

/-- The limit is strictly positive at every canonical primitive parameter.
No positivity claim for all irrational parameters is made here. -/
theorem frontierLimitProfile_pos_at_primitive (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    0 < frontierLimitProfile (profileParameter p) := by
  rw [frontierLimitProfile_interpolates p hp]
  exact div_pos (primitiveFareyLength_pos p hp) (profileMass_pos p hp)

end Markov
