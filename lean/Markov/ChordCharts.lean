import Markov.AffineSupport
import Markov.ChordHalfPlane
import Markov.HalfPlaneAngleOrder
import Markov.SupportShear
import Mathlib.Topology.Order.LeftRight

/-! Actual selected supports on the chord between the two vectors of a basis.
The increasing chord direction supplies the selection, including at the
endpoints. Consecutive quarter-turn charts select exactly the same functional
at their common endpoint. Equal endpoint lengths and a strict difference
bound give monotone, right-continuous real support angles on a whole chord. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The next positively oriented quarter-turn frame. -/
def quarterTurnBasis (B : Module.Basis (Fin 2) ℝ E) : Module.Basis (Fin 2) ℝ E :=
  intPairBasis B (0, 1) (-1, 0) (by norm_num [intDet])

@[simp] theorem quarterTurnBasis_zero (B : Module.Basis (Fin 2) ℝ E) :
    quarterTurnBasis B 0 = B 1 := by
  simp [quarterTurnBasis, intPairBasis_zero, intVector]

@[simp] theorem quarterTurnBasis_one (B : Module.Basis (Fin 2) ℝ E) :
    quarterTurnBasis B 1 = -B 0 := by
  simp [quarterTurnBasis, intPairBasis_one, intVector]

/-- The basis whose affine section is the chord from `B 0` to `B 1`. -/
def chordBasis (B : Module.Basis (Fin 2) ℝ E) : Module.Basis (Fin 2) ℝ E :=
  intPairBasis B (1, 0) (-1, 1) (by norm_num [intDet])

@[simp] theorem chordBasis_zero (B : Module.Basis (Fin 2) ℝ E) :
    chordBasis B 0 = B 0 := by
  simp [chordBasis, intPairBasis_zero, intVector]

@[simp] theorem chordBasis_one (B : Module.Basis (Fin 2) ℝ E) :
    chordBasis B 1 = B 1 - B 0 := by
  simp [chordBasis, intPairBasis_one, intVector, sub_eq_add_neg, add_comm]

theorem chordBasis_affinePoint (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordBasis B 0 + s • chordBasis B 1 = (1 - s) • B 0 + s • B 1 := by
  rw [chordBasis_zero, chordBasis_one]
  module

/-- The actual norming functional selected by increasing chord parameter. -/
def chordSelectedSupport (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) : StrongDual ℝ E :=
  selectedAffineSupport (chordBasis B) s

/-- The principal support angle in the endpoint frame. -/
def chordSelectedAngle (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) : ℝ :=
  supportAngle B (chordSelectedSupport B s)

theorem chordSelectedSupport_spec (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    IsSelectedSupport ((1 - s) • B 0 + s • B 1) (B 1 - B 0)
      (chordSelectedSupport B s) := by
  have h := selectedAffineSupport_spec (chordBasis B) s
  rw [chordBasis_affinePoint, chordBasis_one] at h
  exact h

theorem chordSelectedSupport_mem_normingFunctionals
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordSelectedSupport B s ∈ normingFunctionals ((1 - s) • B 0 + s • B 1) :=
  (chordSelectedSupport_spec B s).1

/-- Both adjacent chord selections agree at their common ray. Their
selection directions differ only by a multiple of that ray. -/
theorem chordSelectedSupport_seam (B : Module.Basis (Fin 2) ℝ E) :
    chordSelectedSupport B 1 = chordSelectedSupport (quarterTurnBasis B) 0 := by
  have hs : IsSelectedSupport (B 1) (B 1 - B 0) (chordSelectedSupport B 1) := by
    simpa only [sub_self, zero_smul, one_smul, zero_add] using
      chordSelectedSupport_spec B 1
  have ht : IsSelectedSupport (B 1) (-B 0 - B 1)
      (chordSelectedSupport (quarterTurnBasis B) 0) := by
    simpa only [sub_zero, one_smul, zero_smul, add_zero,
      quarterTurnBasis_zero, quarterTurnBasis_one] using
      chordSelectedSupport_spec (quarterTurnBasis B) 0
  have hdir : (B 1 - B 0) + (-2 : ℝ) • B 1 = -B 0 - B 1 := by module
  have ht' : IsSelectedSupport (B 1) (B 1 - B 0)
      (chordSelectedSupport (quarterTurnBasis B) 0) := by
    apply (isSelectedSupport_shear_iff (B 1) (B 1 - B 0) (-2) _).mp
    rwa [hdir]
  apply (exists_unique_selectedSupport (affinePairBasis (chordBasis B) 1)).unique
  · simpa only [affinePairBasis_zero, affinePairBasis_one, chordBasis_zero,
      chordBasis_one, one_smul, add_sub_cancel] using hs
  · simpa only [affinePairBasis_zero, affinePairBasis_one, chordBasis_zero,
      chordBasis_one, one_smul, add_sub_cancel] using ht'

/-- Supports increase in determinant order along the actual chord. -/
theorem normingSupport_chord_det_nonneg
    (B : Module.Basis (Fin 2) ℝ E) (s t : ℝ) (hst : s < t)
    (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hft : ft ∈ normingFunctionals ((1 - t) • B 0 + t • B 1)) :
    0 ≤ fs (B 0) * ft (B 1) - fs (B 1) * ft (B 0) := by
  have hfs' : fs ∈ normingFunctionals (chordBasis B 0 + s • chordBasis B 1) := by
    rwa [chordBasis_affinePoint]
  have hft' : ft ∈ normingFunctionals (chordBasis B 0 + t • chordBasis B 1) := by
    rwa [chordBasis_affinePoint]
  have h := normingSupport_affineLine_det_nonneg (chordBasis B 0) (chordBasis B 1)
    s t hst fs ft hfs' hft'
  simp only [chordBasis_zero, chordBasis_one, map_sub] at h
  nlinarith only [h]

theorem chordSelectedSupport_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L)
    (hdiff : ‖B 0 - B 1‖ < 2 * L) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < chordSelectedSupport B s (B 0) + chordSelectedSupport B s (B 1) := by
  simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
    (B 0) (B 1) L s h0 h1 hdiff hs (chordSelectedSupport B s)
    (chordSelectedSupport_mem_normingFunctionals B s)

/-- The endpoint-frame angle of the actual selected support is monotone
on the whole closed chord. -/
theorem chordSelectedAngle_monotoneOn
    (B : Module.Basis (Fin 2) ℝ E) (L : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L)
    (hdiff : ‖B 0 - B 1‖ < 2 * L) :
    MonotoneOn (chordSelectedAngle B) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  · apply (supportAngle_le_iff_det_nonneg_of_sum_pos B _ _
      (chordSelectedSupport_sum_pos B L s h0 h1 hdiff hs)
      (chordSelectedSupport_sum_pos B L t h0 h1 hdiff ht)).mpr
    exact normingSupport_chord_det_nonneg B s t hst _ _
      (chordSelectedSupport_mem_normingFunctionals B s)
      (chordSelectedSupport_mem_normingFunctionals B t)

/-- The selected functional is right-continuous for every chord parameter. -/
theorem chordSelectedSupport_tendsto_right
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    Tendsto (chordSelectedSupport B) (𝓝[>] s) (𝓝 (chordSelectedSupport B s)) :=
  selectedAffineSupport_tendsto_right (chordBasis B) s

/-- The actual chord angle has the proved right-continuity at every
point of the closed chord, using its strict common half-plane. -/
theorem chordSelectedAngle_continuousWithinAt_right
    (B : Module.Basis (Fin 2) ℝ E) (L : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L)
    (hdiff : ‖B 0 - B 1‖ < 2 * L) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (chordSelectedAngle B) (Ici s) s := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  exact supportAngle_selectedAffineSupport_continuousWithinAt_right (chordBasis B) B s
    (chordSelectedSupport_sum_pos B L s h0 h1 hdiff hs)

end Markov
