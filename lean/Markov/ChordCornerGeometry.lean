import Markov.ChordCharts
import Markov.LeftAffineSupport
import Markov.SupportAngleConnected

/-! Complete support fibres on a whole equal-length chord. Incoming and
outgoing selected supports are the actual minimum and maximum angles in
the endpoint frame, and every intermediate angle is attained. These
statements do not assume a corner mass formula or quantitative estimate. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def chordLeftSelectedSupport (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) : StrongDual ℝ E :=
  leftSelectedAffineSupport (chordBasis B) s

def chordLeftSelectedAngle (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) : ℝ :=
  supportAngle B (chordLeftSelectedSupport B s)

theorem chordLeftSelectedSupport_mem_normingFunctionals
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordLeftSelectedSupport B s ∈ normingFunctionals ((1 - s) • B 0 + s • B 1) := by
  rw [← chordBasis_affinePoint]
  exact leftSelectedAffineSupport_mem_normingFunctionals (chordBasis B) s

theorem normingSupport_chord_sameParameter_supportAngle_le_iff
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hg : g ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hfpos : 0 < f (B 0) + f (B 1)) (hgpos : 0 < g (B 0) + g (B 1)) :
    supportAngle B f ≤ supportAngle B g ↔ f (B 1 - B 0) ≤ g (B 1 - B 0) := by
  rw [supportAngle_le_iff_det_nonneg_of_sum_pos B f g hfpos hgpos]
  have h := normingSupport_basisLine_sameParameter_det_nonneg_iff (chordBasis B) s f g
    (by rwa [chordBasis_affinePoint]) (by rwa [chordBasis_affinePoint])
  simp only [chordBasis_zero, chordBasis_one, map_sub] at h ⊢
  ring_nf at h ⊢
  exact h

theorem chord_supportAngle_le_selected
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Icc (0 : ℝ) 1) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1)) :
    supportAngle B f ≤ chordSelectedAngle B s := by
  apply (normingSupport_chord_sameParameter_supportAngle_le_iff B s f
    (chordSelectedSupport B s) hf (chordSelectedSupport_mem_normingFunctionals B s) ?_
    (chordSelectedSupport_sum_pos B L s h0 h1 hdiff hs)).mpr
  · exact (chordSelectedSupport_spec B s).2 f hf
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord _ _ L s
      h0 h1 hdiff hs f hf

theorem chord_leftSelectedAngle_le_supportAngle
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Icc (0 : ℝ) 1) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1)) :
    chordLeftSelectedAngle B s ≤ supportAngle B f := by
  have hleft := chordLeftSelectedSupport_mem_normingFunctionals B s
  apply (normingSupport_chord_sameParameter_supportAngle_le_iff B s
    (chordLeftSelectedSupport B s) f hleft hf ?_ ?_).mpr
  · have h := leftSelectedAffineSupport_eval_le (chordBasis B) s f
      (by rwa [chordBasis_affinePoint])
    simpa only [chordBasis_one] using h
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord _ _ L s
      h0 h1 hdiff hs _ hleft
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord _ _ L s
      h0 h1 hdiff hs f hf

theorem chord_leftSelectedAngle_le_selected
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    chordLeftSelectedAngle B s ≤ chordSelectedAngle B s :=
  chord_leftSelectedAngle_le_supportAngle B L s h0 h1 hdiff hs _
    (chordSelectedSupport_mem_normingFunctionals B s)

theorem chord_supportAngles_eq_Icc
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    supportAngle B '' normingFunctionals ((1 - s) • B 0 + s • B 1) =
      Icc (chordLeftSelectedAngle B s) (chordSelectedAngle B s) := by
  have hc : ContinuousOn (supportAngle B)
      (normingFunctionals ((1 - s) • B 0 + s • B 1)) := by
    intro f hf
    apply (supportAngle_continuousAt_of_sum_pos B f ?_).continuousWithinAt
    simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord _ _ L s
      h0 h1 hdiff hs f hf
  have hconn := (normingFunctionals_isConnected ((1 - s) • B 0 + s • B 1)).image
    (supportAngle B) hc
  have hlo : chordLeftSelectedAngle B s ∈ supportAngle B ''
      normingFunctionals ((1 - s) • B 0 + s • B 1) :=
    ⟨_, chordLeftSelectedSupport_mem_normingFunctionals B s, rfl⟩
  have hhi : chordSelectedAngle B s ∈ supportAngle B ''
      normingFunctionals ((1 - s) • B 0 + s • B 1) :=
    ⟨_, chordSelectedSupport_mem_normingFunctionals B s, rfl⟩
  ext θ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨chord_leftSelectedAngle_le_supportAngle B L s h0 h1 hdiff hs f hf,
      chord_supportAngle_le_selected B L s h0 h1 hdiff hs f hf⟩
  · exact fun hθ => hconn.isPreconnected.ordConnected.out hlo hhi hθ

theorem chordSelectedAngle_tendsto_left
    (B : Module.Basis (Fin 2) ℝ E) (L s : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (chordSelectedAngle B) (𝓝[<] s) (𝓝 (chordLeftSelectedAngle B s)) := by
  apply supportAngle_selectedAffineSupport_tendsto_left (chordBasis B) B s
  simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord _ _ L s
    h0 h1 hdiff hs _ (chordLeftSelectedSupport_mem_normingFunctionals B s)

end Markov
