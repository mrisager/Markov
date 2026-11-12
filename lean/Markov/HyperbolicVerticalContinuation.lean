import Markov.HyperbolicTranslationLength
import Markov.HyperbolicVerticalTriangle
import Mathlib.Topology.Connected.Clopen

/-! Rigidity from two actual vertical points and continuation of an oriented
vertical germ along a locally unit-speed real curve. No initial verticalization,
arbitrary geodesic straightening, or simplicity result is assumed. -/

noncomputable section
open Set Metric
namespace Markov

/-- Two distances to distinct vertical points determine a prescribed point
on that vertical line uniquely in the actual hyperbolic metric. -/
theorem upperHalfPlane_eq_vertical_of_two_dist_eq
    (z : UpperHalfPlane) (s u t : ℝ) (hsu : s ≠ u)
    (hs : dist z (hyperbolicVerticalAxis s) =
      dist (hyperbolicVerticalAxis t) (hyperbolicVerticalAxis s))
    (hu : dist z (hyperbolicVerticalAxis u) =
      dist (hyperbolicVerticalAxis t) (hyperbolicVerticalAxis u)) :
    z = hyperbolicVerticalAxis t := by
  have hc (v : ℝ) (he : dist z (hyperbolicVerticalAxis v) =
      dist (hyperbolicVerticalAxis t) (hyperbolicVerticalAxis v)) :
      (z.re ^ 2 + z.im ^ 2 + (Real.exp v) ^ 2) * Real.exp t =
        ((Real.exp t) ^ 2 + (Real.exp v) ^ 2) * z.im := by
    have hh := congrArg Real.cosh he
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hh
    simp only [hyperbolicVerticalAxis, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im,
      sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at hh
    have hd1 : 2 * z.im * Real.exp v ≠ 0 := by positivity
    have hd2 : 2 * Real.exp t * Real.exp v ≠ 0 := by positivity
    have heq := (div_eq_div_iff hd1 hd2).mp hh
    apply (mul_left_inj' (show 2 * Real.exp v ≠ 0 by positivity)).mp
    calc
      ((z.re ^ 2 + z.im ^ 2 + (Real.exp v) ^ 2) * Real.exp t) *
          (2 * Real.exp v) =
        (z.re ^ 2 + z.im ^ 2 + (Real.exp v) ^ 2) *
          (2 * Real.exp t * Real.exp v) := by ring
      _ = ((Real.exp t) ^ 2 + (Real.exp v) ^ 2) *
          (2 * z.im * Real.exp v) := heq
      _ = (((Real.exp t) ^ 2 + (Real.exp v) ^ 2) * z.im) *
          (2 * Real.exp v) := by ring
  have hcs := hc s hs
  have hcu := hc u hu
  have hsq : (Real.exp s) ^ 2 ≠ (Real.exp u) ^ 2 := by
    intro h
    have he : Real.exp s = Real.exp u := by
      nlinarith [Real.exp_pos s, Real.exp_pos u]
    exact hsu (Real.exp_injective he)
  have hprod : (Real.exp t - z.im) * ((Real.exp s) ^ 2 - (Real.exp u) ^ 2) = 0 := by
    nlinarith only [hcs, hcu]
  have him : Real.exp t = z.im :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hsq))
  rw [him] at hcs
  have hreprod : z.re ^ 2 * z.im = 0 := by nlinarith only [hcs]
  have hre : z.re = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hreprod).resolve_right z.im_ne_zero)
  exact UpperHalfPlane.ext_re_im hre him.symm

/-- Agreement at two distinct parameters propagates over any set on which
the actual curve preserves all parameter distances. -/
theorem upperHalfPlane_isometryOn_vertical_eq
    (γ : ℝ → UpperHalfPlane) (S : Set ℝ) (c a b : ℝ)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hmetric : ∀ s ∈ S, ∀ t ∈ S, dist (γ s) (γ t) = dist s t)
    (haeq : γ a = hyperbolicVerticalAxis (a + c))
    (hbeq : γ b = hyperbolicVerticalAxis (b + c)) :
    ∀ t ∈ S, γ t = hyperbolicVerticalAxis (t + c) := by
  have hd (s t : ℝ) :
      dist (hyperbolicVerticalAxis (s + c)) (hyperbolicVerticalAxis (t + c)) = dist s t := by
    rw [hyperbolicVerticalAxis_isometry.dist_eq, Real.dist_eq, Real.dist_eq]
    congr 1
    ring
  intro t ht
  apply upperHalfPlane_eq_vertical_of_two_dist_eq (γ t) (a + c) (b + c) (t + c)
    (fun h => hab (add_right_cancel h))
  · rw [← haeq, hmetric t ht a ha, haeq, hd]
  · rw [← hbeq, hmetric t ht b hb, hbeq, hd]

/-- A locally unit-speed actual real curve agreeing with an oriented vertical
axis on a nonempty real neighborhood agrees with it everywhere. The local
distance hypothesis already implies continuity; no smoothness is assumed. -/
theorem upperHalfPlane_locally_unit_speed_vertical_continuation
    (γ : ℝ → UpperHalfPlane) (c : ℝ)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u)
    (hinit : ∃ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r,
      γ s = hyperbolicVerticalAxis (s + c)) :
    ∀ t : ℝ, γ t = hyperbolicVerticalAxis (t + c) := by
  let E : Set ℝ := {t | ∃ r > 0, ∀ s ∈ Metric.ball t r,
    γ s = hyperbolicVerticalAxis (s + c)}
  have hopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨r, hr, heq⟩ := ht
    refine mem_nhds_iff.mpr ⟨Metric.ball t (r / 2), ?_, isOpen_ball,
      mem_ball_self (by linarith)⟩
    intro s hs
    refine ⟨r / 2, by linarith, ?_⟩
    intro u hu
    apply heq u
    change dist u t < r
    change dist s t < r / 2 at hs
    change dist u s < r / 2 at hu
    have htri := dist_triangle u s t
    linarith
  have hclosed : IsClosed E := by
    apply isClosed_of_closure_subset
    intro t ht
    obtain ⟨r, hr, hmetric⟩ := hloc t
    obtain ⟨a, haE, hanear⟩ := (Metric.mem_closure_iff.mp ht) (r / 4) (by linarith)
    obtain ⟨δ, hδ, heq⟩ := haE
    let e : ℝ := min δ (r / 4) / 2
    have hmin : 0 < min δ (r / 4) := lt_min hδ (by linarith)
    have hepos : 0 < e := by dsimp only [e]; positivity
    have heδ : e < δ := by
      dsimp only [e]
      have hm := min_le_left δ (r / 4)
      linarith
    have her : e < r / 4 := by
      dsimp only [e]
      have hm := min_le_right δ (r / 4)
      linarith
    have hdist : dist (a + e) a = e := by
      rw [Real.dist_eq]
      have he : a + e - a = e := by ring
      rw [he, abs_of_pos hepos]
    have ha : a ∈ Metric.ball t r := by
      change dist a t < r
      rw [dist_comm]
      linarith
    have hb : a + e ∈ Metric.ball t r := by
      change dist (a + e) t < r
      have htri := dist_triangle (a + e) a t
      rw [hdist, dist_comm a t] at htri
      linarith
    have hbeq : γ (a + e) = hyperbolicVerticalAxis (a + e + c) := by
      apply heq
      change dist (a + e) a < δ
      rw [hdist]
      exact heδ
    refine ⟨r, hr, ?_⟩
    apply upperHalfPlane_isometryOn_vertical_eq γ (Metric.ball t r) c a (a + e)
      ha hb (by intro he; linarith) hmetric (heq a (mem_ball_self hδ)) hbeq
  have hnonempty : E.Nonempty := by
    obtain ⟨t, r, hr, heq⟩ := hinit
    exact ⟨t, r, hr, heq⟩
  have hwhole : E = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  intro t
  have ht : t ∈ E := by rw [hwhole]; trivial
  obtain ⟨r, hr, heq⟩ := ht
  exact heq t (mem_ball_self hr)

end Markov
