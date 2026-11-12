import Markov.FareyRefinement
import Markov.BirthRayConvexity

/-! Affine profiles of the actual finite Farey frontiers on the section
x+y=1. Endpoint interpolation and increasing consecutive slopes follow from
the checked birth-corner inequalities, with no norm assumption. -/

noncomputable section

namespace Markov

/-- Positive coordinate mass on the nonnegative primitive quadrant. -/
def profileMass (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) + (p.2 : ℝ)

/-- The affine coordinate of a direction on the section x+y=1. -/
def profileParameter (p : ℤ × ℤ) : ℝ := (p.2 : ℝ) / profileMass p

theorem profileMass_add (p q : ℤ × ℤ) :
    profileMass (p + q) = profileMass p + profileMass q := by
  simp [profileMass]
  ring

theorem profileMass_nsmul (p : ℤ × ℤ) (n : ℕ) :
    profileMass (n • p) = (n : ℝ) * profileMass p := by
  simp [profileMass, nsmul_eq_mul]
  ring

theorem profileMass_pos (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    0 < profileMass p := by
  rcases hp with ⟨hp1, hp2, hcop⟩
  have hs : 0 < p.1 + p.2 := by
    by_contra hn
    have h1 : p.1 = 0 := by omega
    have h2 : p.2 = 0 := by omega
    obtain ⟨a, b, hab⟩ := hcop
    simp [h1, h2] at hab
  dsimp [profileMass]
  exact_mod_cast hs

theorem profileParameter_nonneg (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    0 ≤ profileParameter p := by
  exact div_nonneg (by exact_mod_cast hp.2.1) (profileMass_pos p hp).le

theorem profileParameter_le_one (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    profileParameter p ≤ 1 := by
  apply (div_le_one (profileMass_pos p hp)).mpr
  dsimp [profileMass]
  have h1 : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  linarith

/-- The determinant-one condition gives the strict ordering of the two
section parameters. -/
theorem profileParameter_lt_of_det_one (u v : ℤ × ℤ)
    (hu : NonnegativePrimitiveDirection u) (hv : NonnegativePrimitiveDirection v)
    (hd : intDet u v = 1) : profileParameter u < profileParameter v := by
  apply (div_lt_div_iff₀ (profileMass_pos u hu) (profileMass_pos v hv)).mpr
  have hdR : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 1 := by
    exact_mod_cast hd
  dsimp [profileMass]
  nlinarith

/-- Slope and offset of the line interpolating normalized candidate lengths. -/
def profileSlope (u v : ℤ × ℤ) (Lu Lv : ℝ) : ℝ :=
  Lv * profileMass u - Lu * profileMass v

def profileOffset (u v : ℤ × ℤ) (Lu Lv : ℝ) : ℝ :=
  Lu * (v.2 : ℝ) - Lv * (u.2 : ℝ)

def profileLine (u v : ℤ × ℤ) (Lu Lv t : ℝ) : ℝ :=
  profileSlope u v Lu Lv * t + profileOffset u v Lu Lv

theorem profileLine_left (u v : ℤ × ℤ) (Lu Lv : ℝ)
    (hu : profileMass u ≠ 0) (hd : intDet u v = 1) :
    profileLine u v Lu Lv (profileParameter u) = Lu / profileMass u := by
  have hdR : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 1 := by
    exact_mod_cast hd
  simp only [profileLine, profileSlope, profileOffset, profileParameter, profileMass] at *
  field_simp
  linear_combination Lu * hdR

theorem profileLine_right (u v : ℤ × ℤ) (Lu Lv : ℝ)
    (hv : profileMass v ≠ 0) (hd : intDet u v = 1) :
    profileLine u v Lu Lv (profileParameter v) = Lv / profileMass v := by
  have hdR : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 1 := by
    exact_mod_cast hd
  simp only [profileLine, profileSlope, profileOffset, profileParameter, profileMass] at *
  field_simp
  linear_combination Lv * hdR

/-- The slope jump is precisely the positive coordinate mass times the
corner surplus. -/
theorem profileSlope_difference (q p r : ℤ × ℤ) (k : ℕ) (Lq Lp Lr : ℝ)
    (hsum : q + r = k • p) :
    profileSlope p r Lp Lr - profileSlope q p Lq Lp =
      profileMass p * (Lq + Lr - (k : ℝ) * Lp) := by
  have hm := congrArg profileMass hsum
  rw [profileMass_add, profileMass_nsmul] at hm
  dsimp [profileSlope]
  linear_combination -Lp * hm

def FareyEdge.lengthU (e : FareyEdge) : ℝ :=
  primitiveFareyLength e.u e.holonomy.left_nonnegativePrimitive

def FareyEdge.lengthV (e : FareyEdge) : ℝ :=
  primitiveFareyLength e.v e.holonomy.right_nonnegativePrimitive

def FareyEdge.profileSlope (e : FareyEdge) : ℝ :=
  Markov.profileSlope e.u e.v e.lengthU e.lengthV

def FareyEdge.profileOffset (e : FareyEdge) : ℝ :=
  Markov.profileOffset e.u e.v e.lengthU e.lengthV

def FareyEdge.profile (e : FareyEdge) (t : ℝ) : ℝ := e.profileSlope * t + e.profileOffset

theorem FareyEdge.lengthU_pos (e : FareyEdge) : 0 < e.lengthU :=
  primitiveFareyLength_pos _ _

theorem FareyEdge.lengthV_pos (e : FareyEdge) : 0 < e.lengthV :=
  primitiveFareyLength_pos _ _

theorem FareyEdge.profileParameter_lt (e : FareyEdge) :
    profileParameter e.u < profileParameter e.v :=
  profileParameter_lt_of_det_one e.u e.v e.holonomy.left_nonnegativePrimitive
    e.holonomy.right_nonnegativePrimitive e.holonomy.det_eq_one

theorem FareyEdge.profile_left (e : FareyEdge) :
    e.profile (profileParameter e.u) = e.lengthU / profileMass e.u :=
  profileLine_left e.u e.v e.lengthU e.lengthV
    (profileMass_pos e.u e.holonomy.left_nonnegativePrimitive).ne' e.holonomy.det_eq_one

theorem FareyEdge.profile_right (e : FareyEdge) :
    e.profile (profileParameter e.v) = e.lengthV / profileMass e.v :=
  profileLine_right e.u e.v e.lengthU e.lengthV
    (profileMass_pos e.v e.holonomy.right_nonnegativePrimitive).ne' e.holonomy.det_eq_one

/-- Actual adjacent frontier edges share precisely the same primitive
corner direction. -/
theorem fareyFrontier_adjacent_endpoint (n : ℕ) (a b : FareyEdge)
    (h : FareyAdjacent a b (fareyFrontier n)) : a.v = b.u := by
  obtain ⟨u, v, M, N, k, _, ha, hb, _, _⟩ := fareyFrontier_adjacent_birth n a b h
  exact ha.trans hb.symm

/-- The affine functions match at every actual frontier join. -/
theorem fareyFrontier_adjacent_profile_match (n : ℕ) (a b : FareyEdge)
    (h : FareyAdjacent a b (fareyFrontier n)) :
    a.profile (profileParameter a.v) = b.profile (profileParameter a.v) := by
  have he := fareyFrontier_adjacent_endpoint n a b h
  rw [a.profile_right, he, b.profile_left]
  simp only [FareyEdge.lengthV, FareyEdge.lengthU, he]

/-- Every old and new corner of the finite Farey frontier has a strict
positive jump in affine profile slope. -/
theorem fareyFrontier_adjacent_slope_lt (n : ℕ) (a b : FareyEdge)
    (h : FareyAdjacent a b (fareyFrontier n)) : a.profileSlope < b.profileSlope := by
  obtain ⟨u, v, M, N, k, hh, hav, hbu, hau, hbv⟩ := fareyFrontier_adjacent_birth n a b h
  let p := u + v
  let q := k • p + u
  let r := k • p + v
  have hp : NonnegativePrimitiveDirection p := by
    simpa only [p, hav] using a.holonomy.right_nonnegativePrimitive
  have hq : NonnegativePrimitiveDirection q := by
    simpa only [q, p, hau] using a.holonomy.left_nonnegativePrimitive
  have hr : NonnegativePrimitiveDirection r := by
    simpa only [r, p, hbv] using b.holonomy.right_nonnegativePrimitive
  have hc := hh.canonical_birth_corner k k hp hq hr
  have hsum : q + r = (k + k + 1) • p := by
    dsimp [q, r, p]
    rw [add_nsmul, add_nsmul, one_nsmul]
    module
  have hs := profileSlope_difference q p r (k + k + 1)
    (primitiveFareyLength q hq) (primitiveFareyLength p hp) (primitiveFareyLength r hr) hsum
  have hgap : 0 < primitiveFareyLength q hq + primitiveFareyLength r hr -
      ((k + k + 1 : ℕ) : ℝ) * primitiveFareyLength p hp := by linarith
  have hm := mul_pos (profileMass_pos p hp) hgap
  have hlt : profileSlope q p (primitiveFareyLength q hq) (primitiveFareyLength p hp) <
      profileSlope p r (primitiveFareyLength p hp) (primitiveFareyLength r hr) := by linarith
  simpa only [FareyEdge.profileSlope, FareyEdge.lengthU, FareyEdge.lengthV, hau, hav, hbu, hbv, p, q, r]
    using hlt

/-- Cone membership on the affine section identifies the parameter interval
of the actual edge. Thus the checked cone tiling also gives interval coverage. -/
theorem FareyEdge.profileParameter_bounds_of_cone (e : FareyEdge) (t : ℝ)
    (hcone : InFareyCone e.u e.v (1 - t, t)) :
    profileParameter e.u ≤ t ∧ t ≤ profileParameter e.v := by
  obtain ⟨a, b, ha, hb, hx⟩ := hcone
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  change 1 - t = a * (e.u.1 : ℝ) + b * (e.v.1 : ℝ) at h1
  change t = a * (e.u.2 : ℝ) + b * (e.v.2 : ℝ) at h2
  have hdR : (e.u.1 : ℝ) * (e.v.2 : ℝ) - (e.u.2 : ℝ) * (e.v.1 : ℝ) = 1 := by
    exact_mod_cast e.holonomy.det_eq_one
  have hl : t * profileMass e.u - (e.u.2 : ℝ) = b := by
    dsimp [profileMass]
    linear_combination (e.u.1 : ℝ) * h2 - (e.u.2 : ℝ) * h1 + b * hdR
  have hr : (e.v.2 : ℝ) - t * profileMass e.v = a := by
    dsimp [profileMass]
    linear_combination (e.v.2 : ℝ) * h1 - (e.v.1 : ℝ) * h2 + a * hdR
  constructor
  · apply (div_le_iff₀ (profileMass_pos e.u e.holonomy.left_nonnegativePrimitive)).mpr
    linarith
  · apply (le_div_iff₀ (profileMass_pos e.v e.holonomy.right_nonnegativePrimitive)).mpr
    linarith

/-- The old affine piece takes the arithmetic sum of endpoint lengths at
its new mediant, divided by that direction's coordinate mass. -/
theorem FareyEdge.profile_mediant (e : FareyEdge) :
    e.profile (profileParameter (e.u + e.v)) =
      (e.lengthU + e.lengthV) / profileMass (e.u + e.v) := by
  have hm : profileMass (e.u + e.v) ≠ 0 :=
    (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive).ne'
  have hdR : (e.u.1 : ℝ) * (e.v.2 : ℝ) - (e.u.2 : ℝ) * (e.v.1 : ℝ) = 1 := by
    exact_mod_cast e.holonomy.det_eq_one
  change profileLine e.u e.v e.lengthU e.lengthV (profileParameter (e.u + e.v)) = _
  simp only [profileLine, Markov.profileSlope, Markov.profileOffset, profileParameter, profileMass,
    Prod.fst_add, Prod.snd_add, Int.cast_add] at *
  field_simp
  linear_combination (e.lengthU + e.lengthV) * hdR

/-- Two affine functions ordered at the ends are ordered throughout the
closed interval. This uses no differentiability or convexity hypothesis. -/
theorem affine_profile_le_on_interval (a b c d l r t : ℝ)
    (hlt : l ≤ t) (htr : t ≤ r) (hl : a * l + b ≤ c * l + d)
    (hr : a * r + b ≤ c * r + d) : a * t + b ≤ c * t + d := by
  by_cases hs : 0 ≤ a - c
  · have hm := mul_le_mul_of_nonneg_left htr hs
    nlinarith
  · have hm := mul_le_mul_of_nonpos_left hlt (le_of_not_ge hs)
    nlinarith

/-- Refinement retains the original left endpoint value. -/
theorem FareyEdge.left_profile_left (e : FareyEdge) :
    e.left.profile (profileParameter e.u) = e.profile (profileParameter e.u) := by
  change e.left.profile (profileParameter e.left.u) = e.profile (profileParameter e.u)
  rw [e.left.profile_left, e.profile_left]
  rfl

/-- Refinement retains the original right endpoint value. -/
theorem FareyEdge.right_profile_right (e : FareyEdge) :
    e.right.profile (profileParameter e.v) = e.profile (profileParameter e.v) := by
  change e.right.profile (profileParameter e.right.v) = e.profile (profileParameter e.v)
  rw [e.right.profile_right, e.profile_right]
  rfl

/-- The new mediant length lies strictly below the old affine interpolation. -/
theorem FareyEdge.left_profile_mediant_lt (e : FareyEdge) :
    e.left.profile (profileParameter (e.u + e.v)) <
      e.profile (profileParameter (e.u + e.v)) := by
  change e.left.profile (profileParameter e.left.v) < e.profile (profileParameter (e.u + e.v))
  rw [e.left.profile_right, e.profile_mediant]
  have hl := e.holonomy.canonicalLength_strict_triangle
    e.holonomy.left_nonnegativePrimitive e.holonomy.right_nonnegativePrimitive
    e.holonomy.left.right_nonnegativePrimitive
  apply div_lt_div_of_pos_right _ (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive)
  exact hl

/-- The two children use the same canonical length at the new mediant. -/
theorem FareyEdge.right_profile_mediant_lt (e : FareyEdge) :
    e.right.profile (profileParameter (e.u + e.v)) <
      e.profile (profileParameter (e.u + e.v)) := by
  change e.right.profile (profileParameter e.right.u) < e.profile (profileParameter (e.u + e.v))
  rw [e.right.profile_left, e.profile_mediant]
  have hl := e.holonomy.canonicalLength_strict_triangle
    e.holonomy.left_nonnegativePrimitive e.holonomy.right_nonnegativePrimitive
    e.holonomy.left.right_nonnegativePrimitive
  apply div_lt_div_of_pos_right _ (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive)
  exact hl

/-- The entire left-child piece lies below the old piece on its actual
parameter interval. -/
theorem FareyEdge.left_profile_le (e : FareyEdge) (t : ℝ)
    (hl : profileParameter e.left.u ≤ t) (hr : t ≤ profileParameter e.left.v) :
    e.left.profile t ≤ e.profile t := by
  apply affine_profile_le_on_interval _ _ _ _ (profileParameter e.left.u)
    (profileParameter e.left.v) t hl hr
  · exact e.left_profile_left.le
  · exact e.left_profile_mediant_lt.le

/-- The entire right-child piece lies below the old piece on its actual
parameter interval. -/
theorem FareyEdge.right_profile_le (e : FareyEdge) (t : ℝ)
    (hl : profileParameter e.right.u ≤ t) (hr : t ≤ profileParameter e.right.v) :
    e.right.profile t ≤ e.profile t := by
  apply affine_profile_le_on_interval _ _ _ _ (profileParameter e.right.u)
    (profileParameter e.right.v) t hl hr
  · exact e.right_profile_mediant_lt.le
  · exact e.right_profile_right.le

end Markov
