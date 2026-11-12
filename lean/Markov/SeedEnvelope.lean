import Markov.SeedProfiles
import Markov.QuadrantSeeds
import Markov.FrontierLimit

/-! Actual finite convex profiles and exact convex limits for every positive
Fricke seed. In particular this constructs the mixed-sign (3,3,6) profile.
The original Farey frontier is reused as the coordinate mesh. -/

noncomputable section
open Filter
open scoped Topology

namespace Markov

def seedFrontierSlopes (M0 N0 : IntMatrixTwo) (n i : ℕ) : ℝ :=
  seedEdgeSlope M0 N0 (indexedFareyEdge n i)

def seedFrontierOffsets (M0 N0 : IntMatrixTwo) (n i : ℕ) : ℝ :=
  seedEdgeOffset M0 N0 (indexedFareyEdge n i)

def seedFrontierProfile (M0 N0 : IntMatrixTwo) (n : ℕ) : ℝ → ℝ :=
  prefixEnvelope (affinePiece (seedFrontierSlopes M0 N0 n) (seedFrontierOffsets M0 N0 n)) (2 ^ n - 1)

theorem seedFrontierProfile_convexOn (M0 N0 : IntMatrixTwo) (n : ℕ) :
    ConvexOn ℝ Set.univ (seedFrontierProfile M0 N0 n) :=
  prefixEnvelope_convexOn _ _ (fun i _ => affinePiece_convexOn _ _ i)

theorem seedFrontierSlopes_adjacent (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n j : ℕ) (hj : j < 2 ^ n - 1) :
    seedFrontierSlopes M0 N0 n j ≤ seedFrontierSlopes M0 N0 n (j + 1) := by
  have ha := indexedFareyEdge_adjacent n j (by have := Nat.two_pow_pos n; omega)
  exact (seedProfile_adjacent_slope_lt M0 N0 h0 n _ _ ha).le

theorem seedFrontierProfiles_match (M0 N0 : IntMatrixTwo) (n j : ℕ)
    (hj : j < 2 ^ n - 1) :
    affinePiece (seedFrontierSlopes M0 N0 n) (seedFrontierOffsets M0 N0 n) j (frontierBreakpoints n j) =
      affinePiece (seedFrontierSlopes M0 N0 n) (seedFrontierOffsets M0 N0 n) (j + 1)
        (frontierBreakpoints n j) := by
  exact seedProfile_adjacent_match M0 N0 n _ _
    (indexedFareyEdge_adjacent n j (by have := Nat.two_pow_pos n; omega))

theorem seedFrontierProfile_eq_on_interval (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (n i : ℕ) (t : ℝ) (hi : i < 2 ^ n)
    (hl : profileParameter (indexedFareyEdge n i).u ≤ t)
    (hr : t ≤ profileParameter (indexedFareyEdge n i).v) :
    seedFrontierProfile M0 N0 n t = seedEdgeProfile M0 N0 (indexedFareyEdge n i) t := by
  change prefixEnvelope (affinePiece (seedFrontierSlopes M0 N0 n) (seedFrontierOffsets M0 N0 n))
      (2 ^ n - 1) t = affinePiece (seedFrontierSlopes M0 N0 n) (seedFrontierOffsets M0 N0 n) i t
  apply affineEnvelope_eq_on_cell _ _ (frontierBreakpoints n) _ _ _ (by omega)
    (seedFrontierSlopes_adjacent M0 N0 h0 n) (seedFrontierProfiles_match M0 N0 n)
  · intro j hj
    have hshare := indexedFareyEdge_shared_endpoint n (i - 1) (by omega)
    have hei : i - 1 + 1 = i := by omega
    rw [hei] at hshare
    have hp : frontierBreakpoints n (i - 1) = profileParameter (indexedFareyEdge n i).u :=
      congrArg profileParameter hshare
    exact (frontierBreakpoints_mono n j (i - 1) (by omega) (by omega)).trans (hp ▸ hl)
  · intro j hij hj
    exact hr.trans (frontierBreakpoints_mono n i j hij (by omega))

theorem seedFrontierProfile_eq_of_mem_interval (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) (t : ℝ)
    (hl : profileParameter e.u ≤ t) (hr : t ≤ profileParameter e.v) :
    seedFrontierProfile M0 N0 n t = seedEdgeProfile M0 N0 e t := by
  obtain ⟨i, hi, hei⟩ := fareyFrontier_mem_exists_index n e he
  simpa only [hei] using seedFrontierProfile_eq_on_interval M0 N0 h0 n i t hi
    (by simpa only [hei] using hl) (by simpa only [hei] using hr)

theorem seedFrontierProfile_interpolates_left (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    seedFrontierProfile M0 N0 n (profileParameter e.u) = seedEdgeLengthU M0 N0 e / profileMass e.u := by
  rw [seedFrontierProfile_eq_of_mem_interval M0 N0 h0 n e he _ le_rfl e.profileParameter_lt.le]
  exact seedEdge_profile_left M0 N0 e

theorem seedFrontierProfile_interpolates_right (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    seedFrontierProfile M0 N0 n (profileParameter e.v) = seedEdgeLengthV M0 N0 e / profileMass e.v := by
  rw [seedFrontierProfile_eq_of_mem_interval M0 N0 h0 n e he _ e.profileParameter_lt.le le_rfl]
  exact seedEdge_profile_right M0 N0 e

theorem seedFrontierProfile_eventual_interpolation (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → seedFrontierProfile M0 N0 n (profileParameter p) =
      primitiveSeedLength M0 N0 p hp / profileMass p := by
  obtain ⟨N, hN⟩ := primitive_eventually_frontier_direction p hp.1 hp.2.1 hp.2.2
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.mp (hN n hn)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl
  · simpa only [seedEdgeLengthU] using seedFrontierProfile_interpolates_left M0 N0 h0 n e he
  · simpa only [seedEdgeLengthV] using seedFrontierProfile_interpolates_right M0 N0 h0 n e he

theorem seedFrontierProfile_piece_exists (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ e ∈ fareyFrontier n, seedFrontierProfile M0 N0 n t = seedEdgeProfile M0 N0 e t ∧
      profileParameter e.u ≤ t ∧ t ≤ profileParameter e.v := by
  obtain ⟨e, he, hcone⟩ := (fareyFrontier_covers_quadrant n (1 - t, t)).mpr ⟨by linarith, ht0⟩
  have hb := e.profileParameter_bounds_of_cone t hcone
  exact ⟨e, he, seedFrontierProfile_eq_of_mem_interval M0 N0 h0 n e he t hb.1 hb.2, hb⟩

theorem seedFrontierProfile_pos (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < seedFrontierProfile M0 N0 n t := by
  obtain ⟨e, _, he, hl, hr⟩ := seedFrontierProfile_piece_exists M0 N0 h0 n t ht0 ht1
  rw [he]
  exact seedEdge_profile_pos M0 N0 h0 e t hl hr

theorem seedFrontierProfile_succ_le (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    seedFrontierProfile M0 N0 (n + 1) t ≤ seedFrontierProfile M0 N0 n t := by
  obtain ⟨child, hchild, hval, hl, hr⟩ := seedFrontierProfile_piece_exists M0 N0 h0 (n + 1) t ht0 ht1
  change child ∈ (fareyFrontier n).flatMap FareyEdge.refine at hchild
  obtain ⟨parent, hp, hpc⟩ := List.mem_flatMap.mp hchild
  simp only [FareyEdge.refine, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · have hpr : t ≤ profileParameter parent.v := hr.trans parent.right.profileParameter_lt.le
    rw [hval, seedFrontierProfile_eq_of_mem_interval M0 N0 h0 n parent hp t hl hpr]
    exact seedEdge_left_profile_le M0 N0 h0 parent t hl hr
  · have hpl : profileParameter parent.u ≤ t := parent.left.profileParameter_lt.le.trans hl
    rw [hval, seedFrontierProfile_eq_of_mem_interval M0 N0 h0 n parent hp t hpl hr]
    exact seedEdge_right_profile_le M0 N0 h0 parent t hl hr

theorem seedFrontierProfile_antitone (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Antitone (fun n : ℕ => seedFrontierProfile M0 N0 n t) :=
  antitone_nat_of_succ_le (fun n => seedFrontierProfile_succ_le M0 N0 h0 n t ht0 ht1)

def seedFrontierLimitProfile (M0 N0 : IntMatrixTwo) (t : ℝ) : ℝ :=
  ⨅ n : ℕ, seedFrontierProfile M0 N0 n t

theorem seedFrontierProfile_tendsto_limit (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun n : ℕ => seedFrontierProfile M0 N0 n t) atTop (𝓝 (seedFrontierLimitProfile M0 N0 t)) := by
  apply tendsto_atTop_ciInf (seedFrontierProfile_antitone M0 N0 h0 t ht0 ht1)
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (seedFrontierProfile_pos M0 N0 h0 n t ht0 ht1).le

theorem seedFrontierLimitProfile_convexOn (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (seedFrontierLimitProfile M0 N0) := by
  apply convexOn_of_pointwise_tendsto_real (seedFrontierProfile M0 N0) _ (Set.Icc 0 1)
  · intro n
    exact (seedFrontierProfile_convexOn M0 N0 n).subset (Set.subset_univ _) (convex_Icc _ _)
  · intro t ht
    exact seedFrontierProfile_tendsto_limit M0 N0 h0 t ht.1 ht.2

theorem seedFrontierLimitProfile_nonneg (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ seedFrontierLimitProfile M0 N0 t :=
  le_ciInf (fun n => (seedFrontierProfile_pos M0 N0 h0 n t ht0 ht1).le)

theorem seedFrontierLimitProfile_interpolates (M0 N0 : IntMatrixTwo)
    (h0 : PositiveFrickePair M0 N0) (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    seedFrontierLimitProfile M0 N0 (profileParameter p) =
      primitiveSeedLength M0 N0 p hp / profileMass p := by
  obtain ⟨N, hN⟩ := seedFrontierProfile_eventual_interpolation M0 N0 h0 p hp
  have hc : Tendsto (fun n : ℕ => seedFrontierProfile M0 N0 n (profileParameter p)) atTop
      (𝓝 (primitiveSeedLength M0 N0 p hp / profileMass p)) := by
    apply tendsto_const_nhds.congr'
    exact eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).symm⟩
  exact tendsto_nhds_unique (seedFrontierProfile_tendsto_limit M0 N0 h0 _
    (profileParameter_nonneg p hp) (profileParameter_le_one p hp)) hc

/-- The mixed-sign quadrant has an actual constructed convex interpolating
profile, rather than a symmetry assumption on the original positive seed. -/
def mixedFrontierLimitProfile : ℝ → ℝ :=
  seedFrontierLimitProfile modularGeneratorB modularGeneratorA.adjugate

theorem mixedFrontierLimitProfile_convexOn : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) mixedFrontierLimitProfile := by
  exact seedFrontierLimitProfile_convexOn _ _ (quadrantSeed_positiveFrickePair 1)

theorem mixedFrontierLimitProfile_interpolates (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    mixedFrontierLimitProfile (profileParameter p) =
      primitiveSeedLength modularGeneratorB modularGeneratorA.adjugate p hp / profileMass p :=
  seedFrontierLimitProfile_interpolates _ _ (quadrantSeed_positiveFrickePair 1) p hp

end Markov
