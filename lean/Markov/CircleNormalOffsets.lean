import Markov.CircleAngularLift
import Markov.SupportQuarterRotation

/-! The two angle offsets used in the cap argument are expressed in
the fixed original Euclidean coordinates. -/

noncomputable section
namespace Markov

theorem inner_quarterTurnNormal_self (z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ z (quarterTurnNormal z) = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, quarterTurnNormal_zero_apply,
    quarterTurnNormal_one_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem circleNormal_add_eq_offset (α η : ℝ) :
    circleNormal (α + η) = Real.cos η • circleNormal α +
      Real.sin η • quarterTurnNormal (circleNormal α) := by
  ext i
  fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

theorem circleNormal_sub_eq_offset (α η : ℝ) :
    circleNormal (α - η) = Real.cos η • circleNormal α -
      Real.sin η • quarterTurnNormal (circleNormal α) := by
  ext i
  fin_cases i <;> simp [Real.cos_sub, Real.sin_sub] <;> ring

theorem norm_normal_offset_plus (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (η : ℝ) :
    ‖Real.cos η • z + Real.sin η • quarterTurnNormal z‖ = 1 := by
  obtain ⟨α, rfl⟩ := exists_circleNormal_eq_of_norm_eq_one z hz
  rw [← circleNormal_add_eq_offset, norm_circleNormal]

theorem norm_normal_offset_minus (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (η : ℝ) :
    ‖Real.cos η • z - Real.sin η • quarterTurnNormal z‖ = 1 := by
  obtain ⟨α, rfl⟩ := exists_circleNormal_eq_of_norm_eq_one z hz
  rw [← circleNormal_sub_eq_offset, norm_circleNormal]

end Markov
