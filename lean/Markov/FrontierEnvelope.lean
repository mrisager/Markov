import Markov.FrontierIndex
import Markov.FareyProfile
import Markov.FiniteAffineEnvelope

/-! Actual finite convex profiles of the canonical Farey length data.
The envelope is constructed from the checked frontier; interpolation and
convexity are proved, rather than taken as norm-construction assumptions. -/

noncomputable section

namespace Markov

def frontierSlopes (n i : ℕ) : ℝ := (indexedFareyEdge n i).profileSlope

def frontierOffsets (n i : ℕ) : ℝ := (indexedFareyEdge n i).profileOffset

def frontierBreakpoints (n i : ℕ) : ℝ := profileParameter (indexedFareyEdge n i).v

def frontierProfile (n : ℕ) : ℝ → ℝ :=
  prefixEnvelope (affinePiece (frontierSlopes n) (frontierOffsets n)) (2 ^ n - 1)

theorem frontierProfile_convexOn (n : ℕ) : ConvexOn ℝ Set.univ (frontierProfile n) :=
  prefixEnvelope_convexOn _ _ (fun i _ => affinePiece_convexOn _ _ i)

theorem frontierSlopes_adjacent (n j : ℕ) (hj : j < 2 ^ n - 1) :
    frontierSlopes n j ≤ frontierSlopes n (j + 1) := by
  have ha := indexedFareyEdge_adjacent n j (by have := Nat.two_pow_pos n; omega)
  exact (fareyFrontier_adjacent_slope_lt n _ _ ha).le

theorem frontierProfiles_match (n j : ℕ) (hj : j < 2 ^ n - 1) :
    affinePiece (frontierSlopes n) (frontierOffsets n) j (frontierBreakpoints n j) =
      affinePiece (frontierSlopes n) (frontierOffsets n) (j + 1) (frontierBreakpoints n j) := by
  have ha := indexedFareyEdge_adjacent n j (by have := Nat.two_pow_pos n; omega)
  exact fareyFrontier_adjacent_profile_match n _ _ ha

theorem frontierBreakpoints_adjacent (n j : ℕ) (hj : j + 1 < 2 ^ n) :
    frontierBreakpoints n j < frontierBreakpoints n (j + 1) := by
  change profileParameter (indexedFareyEdge n j).v < profileParameter (indexedFareyEdge n (j + 1)).v
  rw [indexedFareyEdge_shared_endpoint n j hj]
  exact (indexedFareyEdge n (j + 1)).profileParameter_lt

theorem frontierBreakpoints_mono (n i j : ℕ) (hij : i ≤ j) (hj : j < 2 ^ n) :
    frontierBreakpoints n i ≤ frontierBreakpoints n j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (frontierBreakpoints_adjacent n j hj).le

/-- The actual convex envelope equals the prescribed edge line throughout
that edge's parameter interval. All adjacent-slope inputs are derived. -/
theorem frontierProfile_eq_on_interval (n i : ℕ) (t : ℝ) (hi : i < 2 ^ n)
    (hleft : profileParameter (indexedFareyEdge n i).u ≤ t)
    (hright : t ≤ profileParameter (indexedFareyEdge n i).v) :
    frontierProfile n t = (indexedFareyEdge n i).profile t := by
  change prefixEnvelope (affinePiece (frontierSlopes n) (frontierOffsets n)) (2 ^ n - 1) t =
    affinePiece (frontierSlopes n) (frontierOffsets n) i t
  apply affineEnvelope_eq_on_cell _ _ (frontierBreakpoints n) _ _ _ (by omega)
    (frontierSlopes_adjacent n) (frontierProfiles_match n)
  · intro j hj
    have hip : 0 < i := by omega
    have hshare := indexedFareyEdge_shared_endpoint n (i - 1) (by omega)
    have hei : i - 1 + 1 = i := by omega
    rw [hei] at hshare
    have hp : frontierBreakpoints n (i - 1) = profileParameter (indexedFareyEdge n i).u :=
      congrArg profileParameter hshare
    exact (frontierBreakpoints_mono n j (i - 1) (by omega) (by omega)).trans (hp ▸ hleft)
  · intro j hij hj
    exact hright.trans (frontierBreakpoints_mono n i j hij (by omega))

theorem frontierProfile_interpolates_left (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    frontierProfile n (profileParameter e.u) = e.lengthU / profileMass e.u := by
  obtain ⟨i, hi, hei⟩ := fareyFrontier_mem_exists_index n e he
  have h := frontierProfile_eq_on_interval n i (profileParameter e.u) hi
    (by rw [hei]) (by rw [hei]; exact e.profileParameter_lt.le)
  rw [hei, e.profile_left] at h
  exact h

theorem frontierProfile_interpolates_right (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    frontierProfile n (profileParameter e.v) = e.lengthV / profileMass e.v := by
  obtain ⟨i, hi, hei⟩ := fareyFrontier_mem_exists_index n e he
  have h := frontierProfile_eq_on_interval n i (profileParameter e.v) hi
    (by rw [hei]; exact e.profileParameter_lt.le) (by rw [hei])
  rw [hei, e.profile_right] at h
  exact h

/-- The finite profiles eventually interpolate every primitive direction
exactly and preserve that value at every later refinement. -/
theorem frontierProfile_eventual_interpolation (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → frontierProfile n (profileParameter p) =
      primitiveFareyLength p hp / profileMass p := by
  obtain ⟨N, hN⟩ := primitive_eventually_frontier_direction p hp.1 hp.2.1 hp.2.2
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.mp (hN n hn)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl
  · simpa only [FareyEdge.lengthU] using frontierProfile_interpolates_left n e he
  · simpa only [FareyEdge.lengthV] using frontierProfile_interpolates_right n e he

/-- Every point of the physical profile interval lies in an actual frontier
cell; the envelope equals that cell's prescribed affine interpolant. -/
theorem frontierProfile_piece_exists (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ e ∈ fareyFrontier n, frontierProfile n t = e.profile t ∧
      profileParameter e.u ≤ t ∧ t ≤ profileParameter e.v := by
  obtain ⟨e, he, hcone⟩ := (fareyFrontier_covers_quadrant n (1 - t, t)).mpr ⟨by linarith, ht0⟩
  have hb := e.profileParameter_bounds_of_cone t hcone
  obtain ⟨i, hi, hei⟩ := fareyFrontier_mem_exists_index n e he
  refine ⟨e, he, ?_, hb⟩
  simpa only [hei] using frontierProfile_eq_on_interval n i t hi (by simpa only [hei] using hb.1)
    (by simpa only [hei] using hb.2)

theorem FareyEdge.profile_pos_on_interval (e : FareyEdge) (t : ℝ)
    (hl : profileParameter e.u ≤ t) (hr : t ≤ profileParameter e.v) : 0 < e.profile t := by
  have hu : 0 < e.profile (profileParameter e.u) := by
    rw [e.profile_left]
    exact div_pos e.lengthU_pos (profileMass_pos e.u e.holonomy.left_nonnegativePrimitive)
  have hv : 0 < e.profile (profileParameter e.v) := by
    rw [e.profile_right]
    exact div_pos e.lengthV_pos (profileMass_pos e.v e.holonomy.right_nonnegativePrimitive)
  by_cases hm : 0 ≤ e.profileSlope
  · have hp := mul_nonneg hm (sub_nonneg.mpr hl)
    dsimp [FareyEdge.profile] at *
    nlinarith
  · have hp := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hm) (sub_nonpos.mpr hr)
    dsimp [FareyEdge.profile] at *
    nlinarith

/-- Each finite profile is positive on the complete physical section. -/
theorem frontierProfile_pos (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < frontierProfile n t := by
  obtain ⟨e, _, he, hl, hr⟩ := frontierProfile_piece_exists n t ht0 ht1
  rw [he]
  exact e.profile_pos_on_interval t hl hr

theorem frontierProfile_nonneg (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ frontierProfile n t := (frontierProfile_pos n t ht0 ht1).le

end Markov
