import Markov.TraceBoundaryNormalTurn
import Markov.StieltjesCompletedGraph

/-! The complete lifted normal angles of an actual open boundary arc.
Their set contains the entire open endpoint-angle interval and is contained
in the closed endpoint-angle interval. Endpoint inclusion is not assumed. Consequently its angular
length is exactly the actual boundary turn mass, even at quadrant seams. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

def traceBoundaryNormalAngles (a b : ℝ) : Set ℝ :=
  {θ | ∃ t ∈ Ioo a b,
    θ ∈ Icc (Function.leftLim traceCyclicAngleLift t) (traceCyclicAngleLift t)}

/-- The angle set describes all actual support normals of the arc. -/
theorem traceBoundaryOpenArc_normals_eq_circle_angles (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) :
    normalsOn traceBasis (traceBoundaryOpenArc a b) =
      circleNormal '' traceBoundaryNormalAngles a b := by
  ext n
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
    have hn : normalizedEuclideanCovector traceBasis f ∈
        normalsOn traceBasis {traceBoundaryPath t} :=
      ⟨traceBoundaryPath t, rfl, f, hf, rfl⟩
    rw [traceBoundaryPath_normals_eq_lift_arc t
      ⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩] at hn
    obtain ⟨θ, hθ, heq⟩ := hn
    exact ⟨θ, ⟨t, ht, hθ⟩, heq⟩
  · rintro ⟨θ, ⟨t, ht, hθ⟩, rfl⟩
    have hn : circleNormal θ ∈ normalsOn traceBasis {traceBoundaryPath t} := by
      rw [traceBoundaryPath_normals_eq_lift_arc t
        ⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩]
      exact ⟨θ, hθ, rfl⟩
    have hsub : ({traceBoundaryPath t} : Set TracePlane) ⊆ traceBoundaryOpenArc a b := by
      intro x hx
      rcases hx with rfl
      exact ⟨t, ht, rfl⟩
    exact normalsOn_mono traceBasis hsub hn

theorem traceBoundaryNormalAngles_subset_Icc (a b : ℝ) :
    traceBoundaryNormalAngles a b ⊆
      Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) := by
  rintro θ ⟨t, ht, hθ⟩
  exact ⟨(traceCyclicAngleLift.mono.le_leftLim ht.1).trans hθ.1,
    hθ.2.trans (traceCyclicAngleLift.mono.le_leftLim ht.2)⟩

/-- Every strictly intermediate normal angle occurs at an actual point
inside the arc, including angles lying in a corner's full normal fibre. -/
theorem Ioo_subset_traceBoundaryNormalAngles (a b : ℝ) (hab : a < b) :
    Ioo (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) ⊆
      traceBoundaryNormalAngles a b := by
  intro θ hθ
  obtain ⟨t, ht, hf⟩ := stieltjes_completedGraph_intermediate traceCyclicAngleLift
    hab hθ.1 hθ.2
  exact ⟨t, ht, hf⟩

theorem traceBoundaryNormalAngles_ordConnected (a b : ℝ) (hab : a < b) :
    OrdConnected (traceBoundaryNormalAngles a b) := by
  constructor
  intro x hx y hy z hz
  by_cases hzx : z = x
  · exact hzx ▸ hx
  by_cases hzy : z = y
  · exact hzy ▸ hy
  apply Ioo_subset_traceBoundaryNormalAngles a b hab
  have hxI := traceBoundaryNormalAngles_subset_Icc a b hx
  have hyI := traceBoundaryNormalAngles_subset_Icc a b hy
  have hxz : x < z := lt_of_le_of_ne hz.1 (Ne.symm hzx)
  have hzy' : z < y := lt_of_le_of_ne hz.2 hzy
  exact ⟨hxI.1.trans_lt hxz, hzy'.trans_le hyI.2⟩

theorem traceBoundaryNormalAngles_isConnected (a b : ℝ) (hab : a < b) :
    IsConnected (traceBoundaryNormalAngles a b) := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact ⟨⟨traceCyclicAngleLift ((a + b) / 2), (a + b) / 2, hm,
    traceCyclicAngleLift.mono.leftLim_le le_rfl, le_rfl⟩,
    (traceBoundaryNormalAngles_ordConnected a b hab).isPreconnected⟩

theorem measurableSet_traceBoundaryNormalAngles (a b : ℝ) (hab : a < b) :
    MeasurableSet (traceBoundaryNormalAngles a b) :=
  (traceBoundaryNormalAngles_ordConnected a b hab).measurableSet

theorem traceBoundaryOpenArc_normals_isConnected (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    IsConnected (normalsOn traceBasis (traceBoundaryOpenArc a b)) := by
  rw [traceBoundaryOpenArc_normals_eq_circle_angles a b ha hb]
  exact (traceBoundaryNormalAngles_isConnected a b hab).image circleNormal
    circleNormal_lipschitz.continuous.continuousOn

/-- The complete actual angle set has the endpoint interval's angular
length; no assertion about its two individual endpoint memberships is used. -/
theorem volume_traceBoundaryNormalAngles (a b : ℝ) (hab : a < b) :
    volume (traceBoundaryNormalAngles a b) =
      ENNReal.ofReal (Function.leftLim traceCyclicAngleLift b - traceCyclicAngleLift a) := by
  have hlo := measure_mono (μ := (volume : Measure ℝ))
    (Ioo_subset_traceBoundaryNormalAngles a b hab)
  have hhi := measure_mono (μ := (volume : Measure ℝ))
    (traceBoundaryNormalAngles_subset_Icc a b)
  rw [Real.volume_Ioo] at hlo
  rw [Real.volume_Icc] at hhi
  exact le_antisymm hhi hlo

/-- Genuine boundary turn equals angular length of all genuine support
normals along the open boundary arc, with both endpoint atoms omitted. -/
theorem traceBoundaryTurn_openArc_eq_angular_length (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    traceBoundaryTurn (traceBoundaryOpenArc a b) = volume (traceBoundaryNormalAngles a b) := by
  rw [traceBoundaryTurn_openArc_eq a b ha hb, volume_traceBoundaryNormalAngles a b hab]

theorem traceBoundaryNormalAngles_width_le_two_pi (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) :
    Function.leftLim traceCyclicAngleLift b - traceCyclicAngleLift a ≤ 2 * Real.pi := by
  have h0 := traceCyclicAngleLift.mono ha
  have h4 := traceCyclicAngleLift.mono hb
  have hleft := traceCyclicAngleLift.mono.leftLim_le (le_refl b)
  linarith [traceCyclicAngleLift_period_increment]

end Markov
