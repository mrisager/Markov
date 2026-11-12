import Markov.BirthRayConvexity
import Markov.FanSupport

/-! Actual convex gluing of the canonical trace-length interpolants around
any Farey birth direction. No norm-interpolation hypothesis is used. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pairInterpolant (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) (Lu Lv : ℝ) : E →ₗ[ℝ] ℝ :=
  (intPairBasis B u v hd).constr ℝ ![Lu, Lv]

theorem pairInterpolant_left (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) (Lu Lv : ℝ) :
    pairInterpolant B u v hd Lu Lv (intVector B u) = Lu := by
  rw [← intPairBasis_zero B u v hd]
  simp [pairInterpolant]

theorem pairInterpolant_right (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) (Lu Lv : ℝ) :
    pairInterpolant B u v hd Lu Lv (intVector B v) = Lv := by
  rw [← intPairBasis_one B u v hd]
  simp [pairInterpolant]

theorem intVector_add (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) :
    intVector B (u + v) = intVector B u + intVector B v := by
  simp only [intVector, Prod.fst_add, Prod.snd_add, Int.cast_add, add_smul]
  module

theorem intVector_nsmul (B : Module.Basis (Fin 2) ℝ E) (u : ℤ × ℤ) (n : ℕ) :
    intVector B (n • u) = (n : ℝ) • intVector B u := by
  have h := intVector_nsmul_add B u 0 n
  simpa only [add_zero, intVector, Prod.fst_zero, Prod.snd_zero, Int.cast_zero,
    zero_smul, zero_add, add_zero] using h

/-- The two actual linear interpolants around a canonical Farey corner
have a common convex, positively homogeneous extension agreeing with each
piece on its cone. This is the local convexity step for finite refinements. -/
theorem FareyHolonomy.canonical_birth_convex_extension
    (B : Module.Basis (Fin 2) ℝ E) {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (m n : ℕ)
    (hp : NonnegativePrimitiveDirection (u + v))
    (hq : NonnegativePrimitiveDirection (m • (u + v) + u))
    (hr : NonnegativePrimitiveDirection (n • (u + v) + v)) :
    ∃ f g : E →ₗ[ℝ] ℝ,
      f (intVector B (u + v)) = primitiveFareyLength (u + v) hp ∧
      f (intVector B (m • (u + v) + u)) = primitiveFareyLength (m • (u + v) + u) hq ∧
      g (intVector B (u + v)) = primitiveFareyLength (u + v) hp ∧
      g (intVector B (n • (u + v) + v)) = primitiveFareyLength (n • (u + v) + v) hr ∧
      ConvexOn ℝ Set.univ (fanSupport f g) ∧
      (∀ x ∈ twoRayCone (intVector B (u + v)) (intVector B (m • (u + v) + u)),
        fanSupport f g x = f x) ∧
      (∀ x ∈ twoRayCone (intVector B (u + v)) (intVector B (n • (u + v) + v)),
        fanSupport f g x = g x) := by
  have hl : FareyHolonomy (m • (u + v) + u) (u + v) (M * (M * N) ^ m) (M * N) := by
    simpa only [add_comm] using h.left.right_integral_ray m
  have hray := h.right.integral_ray n
  have hdl : intDet (m • (u + v) + u) (u + v) ≠ 0 := by rw [hl.det_eq_one]; norm_num
  have hdr : intDet (u + v) (n • (u + v) + v) ≠ 0 := by rw [hray.det_eq_one]; norm_num
  let f := pairInterpolant B (m • (u + v) + u) (u + v) hdl
    (primitiveFareyLength _ hq) (primitiveFareyLength _ hp)
  let g := pairInterpolant B (u + v) (n • (u + v) + v) hdr
    (primitiveFareyLength _ hp) (primitiveFareyLength _ hr)
  have hfp : f (intVector B (u + v)) = primitiveFareyLength _ hp := pairInterpolant_right _ _ _ _ _ _
  have hfq : f (intVector B (m • (u + v) + u)) = primitiveFareyLength _ hq := pairInterpolant_left _ _ _ _ _ _
  have hgp : g (intVector B (u + v)) = primitiveFareyLength _ hp := pairInterpolant_left _ _ _ _ _ _
  have hgr : g (intVector B (n • (u + v) + v)) = primitiveFareyLength _ hr := pairInterpolant_right _ _ _ _ _ _
  have hv : (m • (u + v) + u) + (n • (u + v) + v) = (m + n + 1) • (u + v) := by
    simp only [add_nsmul, one_nsmul]
    abel
  have hrel : intVector B (m • (u + v) + u) + intVector B (n • (u + v) + v) =
      ((m + n + 1 : ℕ) : ℝ) • intVector B (u + v) := by
    rw [← intVector_add, hv, intVector_nsmul]
  have hfan : ((m + n + 1 : ℕ) : ℝ) * f (intVector B (u + v)) ≤
      f (intVector B (m • (u + v) + u)) + g (intVector B (n • (u + v) + v)) := by
    rw [hfp, hfq, hgr]
    exact (h.canonical_birth_corner m n hp hq hr).le
  have he := twoCone_convex_extension f g (intVector B (u + v))
    (intVector B (m • (u + v) + u)) (intVector B (n • (u + v) + v))
    ((m + n + 1 : ℕ) : ℝ) (hfp.trans hgp.symm) hrel hfan
  exact ⟨f, g, hfp, hfq, hgp, hgr, he⟩

end Markov
