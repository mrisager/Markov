import Markov.RadialLipschitz
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual norm-ball boundary in a slope wedge is the normalized
basis section. The norm is arbitrary; cutoff and surface identifications
are separate from this elementary boundary parametrization. -/

noncomputable section
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def basisSlope (B : Module.Basis (Fin 2) ℝ E) (x : E) : ℝ :=
  B.coord 1 x / B.coord 0 x

def slopeBoundaryArc (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) : Set E :=
  {x | ‖x‖ = 1 ∧ 0 < B.coord 0 x ∧ a < basisSlope B x ∧ basisSlope B x < b}

theorem radialBasisSection_coord_zero (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    B.coord 0 (radialBasisSection B t) = ‖B 0 + t • B 1‖⁻¹ := by
  simp [radialBasisSection, NormedSpace.normalize, Module.Basis.coord_apply,
    Module.Basis.repr_self]

theorem radialBasisSection_coord_one (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    B.coord 1 (radialBasisSection B t) = ‖B 0 + t • B 1‖⁻¹ * t := by
  simp [radialBasisSection, NormedSpace.normalize, Module.Basis.coord_apply,
    Module.Basis.repr_self]

theorem radialBasisSection_coord_zero_pos (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    0 < B.coord 0 (radialBasisSection B t) := by
  rw [radialBasisSection_coord_zero]
  exact inv_pos.mpr (norm_pos_iff.mpr (basis_affineLine_ne_zero B t))

@[simp] theorem basisSlope_radialBasisSection (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    basisSlope B (radialBasisSection B t) = t := by
  rw [basisSlope, radialBasisSection_coord_one, radialBasisSection_coord_zero]
  exact mul_div_cancel_left₀ t (inv_ne_zero (norm_ne_zero_iff.mpr (basis_affineLine_ne_zero B t)))

theorem radialBasisSection_basisSlope (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hx : ‖x‖ = 1) (hp : 0 < B.coord 0 x) :
    radialBasisSection B (basisSlope B x) = x := by
  have hrep : x = (B.coord 0 x) • B 0 + (B.coord 1 x) • B 1 := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two] using (B.sum_repr x).symm
  have he : B 0 + basisSlope B x • B 1 = (B.coord 0 x)⁻¹ • x := by
    calc
      B 0 + basisSlope B x • B 1 =
          (B.coord 0 x)⁻¹ • ((B.coord 0 x) • B 0 + (B.coord 1 x) • B 1) := by
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
        simp only [basisSlope, div_eq_mul_inv, mul_comm]
      _ = (B.coord 0 x)⁻¹ • x := congrArg (fun y => (B.coord 0 x)⁻¹ • y) hrep.symm
  rw [radialBasisSection, he, NormedSpace.normalize_smul_of_pos (inv_pos.mpr hp)]
  simp [NormedSpace.normalize, hx]

theorem radialBasisSection_image_Ioo (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    radialBasisSection B '' Set.Ioo a b = slopeBoundaryArc B a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨norm_radialBasisSection B t, radialBasisSection_coord_zero_pos B t,
      by simpa using ht.1, by simpa using ht.2⟩
  · rintro ⟨hx, hp, hs, ht⟩
    exact ⟨basisSlope B x, ⟨hs, ht⟩, radialBasisSection_basisSlope B x hx hp⟩

theorem slopeBoundaryArc_eq_frontier_wedge (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    slopeBoundaryArc B a b = frontier (Metric.closedBall (0 : E) 1) ∩
      {x | 0 < B.coord 0 x ∧ a < basisSlope B x ∧ basisSlope B x < b} := by
  rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]
  ext x
  simp [slopeBoundaryArc]

theorem radialBasisSection_injective (B : Module.Basis (Fin 2) ℝ E) :
    Function.Injective (radialBasisSection B) := by
  intro s t h
  simpa only [basisSlope_radialBasisSection] using congrArg (basisSlope B) h

theorem radialBasisSection_continuous (B : Module.Basis (Fin 2) ℝ E) :
    Continuous (radialBasisSection B) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hcont : Continuous (fun s : ℝ => B 0 + s • B 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact (hcont.norm.continuousAt.inv₀
    (norm_ne_zero_iff.mpr (basis_affineLine_ne_zero B t))).smul hcont.continuousAt

theorem slopeBoundaryArc_isPreconnected (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    IsPreconnected (slopeBoundaryArc B a b) := by
  rw [← radialBasisSection_image_Ioo]
  exact isPreconnected_Ioo.image _ (radialBasisSection_continuous B).continuousOn

end Markov
