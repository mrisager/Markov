import Markov.NormalizedCircleWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Convex

/-! A finite disk-extension obstruction from the actual once-around loop.
The contraction is based at the literal complex boundary point 1. No planar
separation, disk-crossing, Jordan or fixed-point assertion is used. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual closed complex unit disk, with its subtype topology. -/
abbrev ComplexClosedUnitDisk := ↥(Metric.closedBall (0 : ℂ) 1)

/-- The literal inclusion of the actual complex unit circle into its closed disk. -/
def complexUnitCircleClosedDisk (z : Circle) : ComplexClosedUnitDisk :=
  ⟨(z : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]⟩

/-- This is the continuous subtype inclusion. -/
theorem continuous_complexUnitCircleClosedDisk : Continuous complexUnitCircleClosedDisk := by
  exact continuous_subtype_val.subtype_mk _

private def circleHomeo : NormalizedCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)

private theorem circleHomeo_zero : circleHomeo (0 : NormalizedCircle) = 1 := by
  simp [circleHomeo, AddCircle.homeomorphCircle_apply]

private def boundaryContraction (s t : unitInterval) : ComplexClosedUnitDisk :=
  ⟨(1 - (s : ℝ)) • (circleHomeo (normalizedCircleStandardLoop t) : ℂ) + (s : ℝ) • (1 : ℂ), by
    apply (convex_closedBall (0 : ℂ) (1 : ℝ))
      (complexUnitCircleClosedDisk (circleHomeo (normalizedCircleStandardLoop t))).property
      (by simp) (sub_nonneg.mpr s.property.2) s.property.1
    ring⟩

private theorem boundaryContraction_continuous :
    Continuous (fun st : unitInterval × unitInterval => boundaryContraction st.1 st.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun st : unitInterval × unitInterval =>
    (1 - (st.1 : ℝ)) • (circleHomeo (normalizedCircleStandardLoop st.2) : ℂ) +
      (st.1 : ℝ) • (1 : ℂ))
  fun_prop

private theorem boundaryContraction_zero (t : unitInterval) :
    boundaryContraction 0 t = complexUnitCircleClosedDisk (circleHomeo (normalizedCircleStandardLoop t)) := by
  apply Subtype.ext
  simp [boundaryContraction, complexUnitCircleClosedDisk]

private theorem boundaryContraction_one (t : unitInterval) :
    boundaryContraction 1 t = complexUnitCircleClosedDisk 1 := by
  apply Subtype.ext
  simp [boundaryContraction, complexUnitCircleClosedDisk]

private theorem boundaryContraction_base (s : unitInterval) (t : unitInterval)
    (ht : t = 0 ∨ t = 1) : boundaryContraction s t = complexUnitCircleClosedDisk 1 := by
  have hloop : normalizedCircleStandardLoop t = 0 := by
    rcases ht with rfl | rfl
    · exact normalizedCircleStandardLoop.source
    · exact normalizedCircleStandardLoop.target
  apply Subtype.ext
  simp only [boundaryContraction, hloop, circleHomeo_zero, complexUnitCircleClosedDisk,
    Circle.coe_one]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- An actual continuous extension of the inverse boundary homeomorphism would
contract the actual positive once-around loop by an actual based path homotopy. -/
def normalizedCircleDiskBoundaryExtension_homotopy
    (r : ComplexClosedUnitDisk → NormalizedCircle) (hr : Continuous r)
    (hboundary : ∀ z : Circle, r (complexUnitCircleClosedDisk z) =
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm z) :
    Path.Homotopy normalizedCircleStandardLoop (Path.refl (0 : NormalizedCircle)) where
  toFun st := r (boundaryContraction st.1 st.2)
  continuous_toFun := hr.comp boundaryContraction_continuous
  map_zero_left t := by
    rw [boundaryContraction_zero, hboundary]
    exact circleHomeo.symm_apply_apply _
  map_one_left t := by
    rw [boundaryContraction_one, hboundary]
    change circleHomeo.symm 1 = 0
    rw [← circleHomeo_zero, circleHomeo.symm_apply_apply]
  prop' s t ht := by
    change r (boundaryContraction s t) = normalizedCircleStandardLoop t
    rw [boundaryContraction_base s t ht, hboundary]
    change circleHomeo.symm 1 = normalizedCircleStandardLoop t
    rw [← circleHomeo_zero, circleHomeo.symm_apply_apply]
    rcases ht with rfl | rfl
    · exact normalizedCircleStandardLoop.source.symm
    · exact normalizedCircleStandardLoop.target.symm

/-- There is no actual continuous disk extension of the actual inverse circle
homeomorphism. This is a based winding obstruction, with all maps explicit. -/
theorem normalizedCircle_no_continuous_disk_boundary_extension
    (r : ComplexClosedUnitDisk → NormalizedCircle) (hr : Continuous r)
    (hboundary : ∀ z : Circle, r (complexUnitCircleClosedDisk z) =
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm z) : False :=
  normalizedCircleStandardLoop_not_homotopic_refl
    ⟨normalizedCircleDiskBoundaryExtension_homotopy r hr hboundary⟩

end Markov
