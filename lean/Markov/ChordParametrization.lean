import Markov.ChordCharts
import Markov.BoundaryArc

/-! A normalized chord of an arbitrary normed plane has explicit endpoint
coordinates. Its positive quadrant is parametrized by the coordinate ratio;
the construction uses only the given norm and basis. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual unit-boundary section obtained by normalizing a basis chord. -/
def chordBoundarySection (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) : E :=
  radialBasisSection (chordBasis B) s

theorem chordBoundarySection_eq_normalize (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordBoundarySection B s = NormedSpace.normalize ((1 - s) • B 0 + s • B 1) := by
  rw [chordBoundarySection, radialBasisSection, chordBasis_affinePoint]

@[simp] theorem norm_chordBoundarySection (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    ‖chordBoundarySection B s‖ = 1 :=
  norm_radialBasisSection (chordBasis B) s

theorem chordBoundarySection_coord_zero (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    B.coord 0 (chordBoundarySection B s) =
      ‖(1 - s) • B 0 + s • B 1‖⁻¹ * (1 - s) := by
  rw [chordBoundarySection_eq_normalize]
  simp [NormedSpace.normalize, Module.Basis.coord_apply, Module.Basis.repr_self]

theorem chordBoundarySection_coord_one (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    B.coord 1 (chordBoundarySection B s) =
      ‖(1 - s) • B 0 + s • B 1‖⁻¹ * s := by
  rw [chordBoundarySection_eq_normalize]
  simp [NormedSpace.normalize, Module.Basis.coord_apply, Module.Basis.repr_self]

theorem chordBoundarySection_injective (B : Module.Basis (Fin 2) ℝ E) :
    Function.Injective (chordBoundarySection B) :=
  radialBasisSection_injective (chordBasis B)

theorem chordBoundarySection_continuous (B : Module.Basis (Fin 2) ℝ E) :
    Continuous (chordBoundarySection B) :=
  radialBasisSection_continuous (chordBasis B)

@[simp] theorem chordBoundarySection_zero (B : Module.Basis (Fin 2) ℝ E) :
    chordBoundarySection B 0 = NormedSpace.normalize (B 0) := by
  simp [chordBoundarySection_eq_normalize]

@[simp] theorem chordBoundarySection_one (B : Module.Basis (Fin 2) ℝ E) :
    chordBoundarySection B 1 = NormedSpace.normalize (B 1) := by
  simp [chordBoundarySection_eq_normalize]

/-- Adjacent normalized chords have exactly the same actual seam point. -/
theorem chordBoundarySection_seam (B : Module.Basis (Fin 2) ℝ E) :
    chordBoundarySection B 1 = chordBoundarySection (quarterTurnBasis B) 0 := by
  simp

@[simp] theorem quarterTurnBasis_coord_zero (B : Module.Basis (Fin 2) ℝ E) (x : E) :
    (quarterTurnBasis B).coord 0 x = B.coord 1 x := by
  have hrep : x = (quarterTurnBasis B).coord 0 x • B 1 +
      (quarterTurnBasis B).coord 1 x • -B 0 := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two,
      quarterTurnBasis_zero, quarterTurnBasis_one] using
      ((quarterTurnBasis B).sum_repr x).symm
  have h := congrArg (B.coord 1) hrep
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self] using h.symm

@[simp] theorem quarterTurnBasis_coord_one (B : Module.Basis (Fin 2) ℝ E) (x : E) :
    (quarterTurnBasis B).coord 1 x = -B.coord 0 x := by
  have hrep : x = (quarterTurnBasis B).coord 0 x • B 1 +
      (quarterTurnBasis B).coord 1 x • -B 0 := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two,
      quarterTurnBasis_zero, quarterTurnBasis_one] using
      ((quarterTurnBasis B).sum_repr x).symm
  have h := congrArg (B.coord 0) hrep
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self] using
    (congrArg Neg.neg h).symm

/-- The normalized chord recovers a unit vector from the ratio of its
positive quadrant coordinates, including the second endpoint. -/
theorem chordBoundarySection_coordRatio (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hx : ‖x‖ = 1) (h0 : 0 ≤ B.coord 0 x) (h1 : 0 < B.coord 1 x) :
    chordBoundarySection B (B.coord 1 x / (B.coord 0 x + B.coord 1 x)) = x := by
  have hsum : 0 < B.coord 0 x + B.coord 1 x := add_pos_of_nonneg_of_pos h0 h1
  have hrep : x = (B.coord 0 x) • B 0 + (B.coord 1 x) • B 1 := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two] using (B.sum_repr x).symm
  have hcoef : 1 - B.coord 1 x / (B.coord 0 x + B.coord 1 x) =
      (B.coord 0 x + B.coord 1 x)⁻¹ * B.coord 0 x := by
    field_simp
    ring
  have he : (1 - B.coord 1 x / (B.coord 0 x + B.coord 1 x)) • B 0 +
      (B.coord 1 x / (B.coord 0 x + B.coord 1 x)) • B 1 =
      (B.coord 0 x + B.coord 1 x)⁻¹ • x := by
    calc
      _ = (B.coord 0 x + B.coord 1 x)⁻¹ •
          ((B.coord 0 x) • B 0 + (B.coord 1 x) • B 1) := by
        rw [smul_add, smul_smul, smul_smul, hcoef]
        simp only [div_eq_mul_inv, mul_comm]
      _ = (B.coord 0 x + B.coord 1 x)⁻¹ • x :=
        congrArg (fun y => (B.coord 0 x + B.coord 1 x)⁻¹ • y) hrep.symm
  rw [chordBoundarySection_eq_normalize, he,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hsum)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hx

/-- Every unit vector with nonnegative first and positive second coordinate
has a chord parameter in the interval with the initial endpoint removed. -/
theorem chordBoundarySection_exists_Ioc (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hx : ‖x‖ = 1) (h0 : 0 ≤ B.coord 0 x) (h1 : 0 < B.coord 1 x) :
    ∃ s ∈ Ioc (0 : ℝ) 1, chordBoundarySection B s = x := by
  have hsum : 0 < B.coord 0 x + B.coord 1 x := add_pos_of_nonneg_of_pos h0 h1
  refine ⟨B.coord 1 x / (B.coord 0 x + B.coord 1 x), ⟨div_pos h1 hsum, ?_⟩,
    chordBoundarySection_coordRatio B x hx h0 h1⟩
  apply (div_le_one hsum).mpr
  linarith

end Markov
