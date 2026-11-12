import Markov.SeedEvaluation
import Markov.SeedBirthConvexity
import Markov.FareyProfile

/-! Actual affine profiles for any positive Fricke seed on the existing
Farey combinatorics, including the mixed-sign seed with product trace 6. -/

noncomputable section
namespace Markov

def seedEdgeLengthU (M0 N0 : IntMatrixTwo) (e : FareyEdge) : ℝ :=
  primitiveSeedLength M0 N0 e.u e.holonomy.left_nonnegativePrimitive

def seedEdgeLengthV (M0 N0 : IntMatrixTwo) (e : FareyEdge) : ℝ :=
  primitiveSeedLength M0 N0 e.v e.holonomy.right_nonnegativePrimitive

def seedEdgeSlope (M0 N0 : IntMatrixTwo) (e : FareyEdge) : ℝ :=
  profileSlope e.u e.v (seedEdgeLengthU M0 N0 e) (seedEdgeLengthV M0 N0 e)

def seedEdgeOffset (M0 N0 : IntMatrixTwo) (e : FareyEdge) : ℝ :=
  profileOffset e.u e.v (seedEdgeLengthU M0 N0 e) (seedEdgeLengthV M0 N0 e)

def seedEdgeProfile (M0 N0 : IntMatrixTwo) (e : FareyEdge) (t : ℝ) : ℝ :=
  seedEdgeSlope M0 N0 e * t + seedEdgeOffset M0 N0 e

theorem seedEdge_profile_left (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e (profileParameter e.u) = seedEdgeLengthU M0 N0 e / profileMass e.u :=
  profileLine_left e.u e.v _ _
    (profileMass_pos e.u e.holonomy.left_nonnegativePrimitive).ne' e.holonomy.det_eq_one

theorem seedEdge_profile_right (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e (profileParameter e.v) = seedEdgeLengthV M0 N0 e / profileMass e.v :=
  profileLine_right e.u e.v _ _
    (profileMass_pos e.v e.holonomy.right_nonnegativePrimitive).ne' e.holonomy.det_eq_one

theorem seedEdgeLengthU_pos (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) (e : FareyEdge) :
    0 < seedEdgeLengthU M0 N0 e := primitiveSeedLength_pos M0 N0 h0 _ _

theorem seedEdgeLengthV_pos (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) (e : FareyEdge) :
    0 < seedEdgeLengthV M0 N0 e := primitiveSeedLength_pos M0 N0 h0 _ _

theorem seedEdge_profile_pos (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (e : FareyEdge) (t : ℝ) (hl : profileParameter e.u ≤ t) (hr : t ≤ profileParameter e.v) :
    0 < seedEdgeProfile M0 N0 e t := by
  have hu : 0 < seedEdgeProfile M0 N0 e (profileParameter e.u) := by
    rw [seedEdge_profile_left]
    exact div_pos (seedEdgeLengthU_pos M0 N0 h0 e) (profileMass_pos _ e.holonomy.left_nonnegativePrimitive)
  have hv : 0 < seedEdgeProfile M0 N0 e (profileParameter e.v) := by
    rw [seedEdge_profile_right]
    exact div_pos (seedEdgeLengthV_pos M0 N0 h0 e) (profileMass_pos _ e.holonomy.right_nonnegativePrimitive)
  by_cases hm : 0 ≤ seedEdgeSlope M0 N0 e
  · have hp := mul_nonneg hm (sub_nonneg.mpr hl)
    dsimp [seedEdgeProfile] at *
    nlinarith
  · have hp := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hm) (sub_nonpos.mpr hr)
    dsimp [seedEdgeProfile] at *
    nlinarith

theorem seedProfile_adjacent_match (M0 N0 : IntMatrixTwo) (n : ℕ) (a b : FareyEdge)
    (h : FareyAdjacent a b (fareyFrontier n)) :
    seedEdgeProfile M0 N0 a (profileParameter a.v) = seedEdgeProfile M0 N0 b (profileParameter a.v) := by
  have he := fareyFrontier_adjacent_endpoint n a b h
  rw [seedEdge_profile_right, he, seedEdge_profile_left]
  simp only [seedEdgeLengthV, seedEdgeLengthU, he]

theorem seedProfile_adjacent_slope_lt (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n : ℕ) (a b : FareyEdge) (h : FareyAdjacent a b (fareyFrontier n)) :
    seedEdgeSlope M0 N0 a < seedEdgeSlope M0 N0 b := by
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
  have hseed := seedEvaluation_spec M0 N0 (⟨u,v,M,N,hh⟩ : FareyEdge)
  have hc := hseed.canonical_seed_birth_corner h0 k k hp hq hr
  have hsum : q + r = (k + k + 1) • p := by
    dsimp [q, r, p]
    rw [add_nsmul, add_nsmul, one_nsmul]
    module
  have hs := profileSlope_difference q p r (k + k + 1)
    (primitiveSeedLength M0 N0 q hq) (primitiveSeedLength M0 N0 p hp)
    (primitiveSeedLength M0 N0 r hr) hsum
  have hgap : 0 < primitiveSeedLength M0 N0 q hq + primitiveSeedLength M0 N0 r hr -
      ((k + k + 1 : ℕ) : ℝ) * primitiveSeedLength M0 N0 p hp := by linarith
  have hm := mul_pos (profileMass_pos p hp) hgap
  have hlt : profileSlope q p (primitiveSeedLength M0 N0 q hq) (primitiveSeedLength M0 N0 p hp) <
      profileSlope p r (primitiveSeedLength M0 N0 p hp) (primitiveSeedLength M0 N0 r hr) := by linarith
  simpa only [seedEdgeSlope, seedEdgeLengthU, seedEdgeLengthV, hau, hav, hbu, hbv, p, q, r] using hlt

/-- Evaluation of the old affine piece at its mediant. -/
theorem seedEdge_profile_mediant (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e (profileParameter (e.u + e.v)) =
      (seedEdgeLengthU M0 N0 e + seedEdgeLengthV M0 N0 e) / profileMass (e.u + e.v) := by
  have hm : profileMass (e.u + e.v) ≠ 0 :=
    (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive).ne'
  have hdR : (e.u.1 : ℝ) * (e.v.2 : ℝ) - (e.u.2 : ℝ) * (e.v.1 : ℝ) = 1 := by
    exact_mod_cast e.holonomy.det_eq_one
  change profileLine e.u e.v _ _ (profileParameter (e.u + e.v)) = _
  simp only [profileLine, profileSlope, profileOffset, profileParameter, profileMass,
    Prod.fst_add, Prod.snd_add, Int.cast_add] at *
  field_simp
  linear_combination (seedEdgeLengthU M0 N0 e + seedEdgeLengthV M0 N0 e) * hdR

theorem seedEdge_left_profile_left (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e.left (profileParameter e.u) = seedEdgeProfile M0 N0 e (profileParameter e.u) := by
  change seedEdgeProfile M0 N0 e.left (profileParameter e.left.u) = _
  rw [seedEdge_profile_left, seedEdge_profile_left]
  rfl

theorem seedEdge_right_profile_right (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e.right (profileParameter e.v) = seedEdgeProfile M0 N0 e (profileParameter e.v) := by
  change seedEdgeProfile M0 N0 e.right (profileParameter e.right.v) = _
  rw [seedEdge_profile_right, seedEdge_profile_right]
  rfl

theorem seedEdge_left_profile_mediant_lt (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e.left (profileParameter (e.u + e.v)) <
      seedEdgeProfile M0 N0 e (profileParameter (e.u + e.v)) := by
  change seedEdgeProfile M0 N0 e.left (profileParameter e.left.v) < _
  rw [seedEdge_profile_right, seedEdge_profile_mediant]
  have hseed := seedEvaluation_spec M0 N0 e
  have hl := hseed.canonicalSeedLength_strict_triangle h0
    e.holonomy.left_nonnegativePrimitive e.holonomy.right_nonnegativePrimitive
    e.holonomy.left.right_nonnegativePrimitive
  exact div_lt_div_of_pos_right hl (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive)

theorem seedEdge_right_profile_mediant_lt (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) (e : FareyEdge) :
    seedEdgeProfile M0 N0 e.right (profileParameter (e.u + e.v)) <
      seedEdgeProfile M0 N0 e (profileParameter (e.u + e.v)) := by
  change seedEdgeProfile M0 N0 e.right (profileParameter e.right.u) < _
  rw [seedEdge_profile_left, seedEdge_profile_mediant]
  have hseed := seedEvaluation_spec M0 N0 e
  have hl := hseed.canonicalSeedLength_strict_triangle h0
    e.holonomy.left_nonnegativePrimitive e.holonomy.right_nonnegativePrimitive
    e.holonomy.left.right_nonnegativePrimitive
  exact div_lt_div_of_pos_right hl (profileMass_pos _ e.holonomy.left.right_nonnegativePrimitive)

theorem seedEdge_left_profile_le (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (e : FareyEdge) (t : ℝ)
    (hl : profileParameter e.left.u ≤ t) (hr : t ≤ profileParameter e.left.v) :
    seedEdgeProfile M0 N0 e.left t ≤ seedEdgeProfile M0 N0 e t := by
  apply affine_profile_le_on_interval _ _ _ _ (profileParameter e.left.u) (profileParameter e.left.v) t hl hr
  · exact (seedEdge_left_profile_left M0 N0 e).le
  · exact (seedEdge_left_profile_mediant_lt M0 N0 h0 e).le

theorem seedEdge_right_profile_le (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (e : FareyEdge) (t : ℝ)
    (hl : profileParameter e.right.u ≤ t) (hr : t ≤ profileParameter e.right.v) :
    seedEdgeProfile M0 N0 e.right t ≤ seedEdgeProfile M0 N0 e t := by
  apply affine_profile_le_on_interval _ _ _ _ (profileParameter e.right.u) (profileParameter e.right.v) t hl hr
  · exact (seedEdge_right_profile_mediant_lt M0 N0 h0 e).le
  · exact (seedEdge_right_profile_right M0 N0 e).le

end Markov
