import Markov.SingularOneChains

/-! Actual oriented paths extracted from actual singular one-simplices.
The maps and paths are inverse under the existing oriented simplex/interval
homeomorphism. No homology generation or Hurewicz inverse is assumed. -/

noncomputable section
open CategoryTheory Opposite Simplicial
namespace Markov

variable (X : Type) [TopologicalSpace X]

/-- The continuous standard-simplex map represented by an actual singular simplex. -/
def singularSimplexMap {n : ℕ} (σ : IntegralSingularSimplex X n) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ

@[simp] theorem singularSimplexMap_ofMap {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularSimplexMap X (singularSimplexOfMap X σ) = σ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).apply_symm_apply σ

@[simp] theorem singularSimplexOfMap_map {n : ℕ} (σ : IntegralSingularSimplex X n) :
    singularSimplexOfMap X (singularSimplexMap X σ) = σ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm_apply_apply σ

/-- The literal ordered vertex values of an actual singular simplex. -/
def singularSimplexVertex {n : ℕ} (σ : IntegralSingularSimplex X n) (i : Fin (n + 1)) : X :=
  singularSimplexMap X σ (stdSimplex.vertex (S := ℝ) i)

/-- The actual oriented path from vertex zero to vertex one in the standard edge. -/
def standardOneSimplexPath :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) where
  toContinuousMap := ⟨stdSimplexHomeomorphUnitInterval.symm,
    stdSimplexHomeomorphUnitInterval.symm.continuous⟩
  source' := by
    apply stdSimplexHomeomorphUnitInterval.injective
    rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]
    exact stdSimplexHomeomorphUnitInterval_zero.symm
  target' := by
    apply stdSimplexHomeomorphUnitInterval.injective
    rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]
    exact stdSimplexHomeomorphUnitInterval_one.symm

/-- The oriented path represented by an actual singular one-simplex,
with its exact original ordered vertex values as endpoints. -/
def singularEdgePath (σ : IntegralSingularSimplex X 1) :
    Path (singularSimplexVertex X σ 0) (singularSimplexVertex X σ 1) :=
  standardOneSimplexPath.map (singularSimplexMap X σ).continuous

@[simp] theorem singularEdgePath_apply (σ : IntegralSingularSimplex X 1)
    (t : unitInterval) :
    singularEdgePath X σ t = singularSimplexMap X σ
      (stdSimplexHomeomorphUnitInterval.symm t) := rfl

/-- Extracting the path and inserting its oriented simplex returns the
same actual singular simplex, not merely a homotopic representative. -/
@[simp] theorem singularPathSimplex_edgePath (σ : IntegralSingularSimplex X 1) :
    singularPathSimplex X (singularEdgePath X σ) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋1⦌)).injective
  change singularSimplexMap X (singularPathSimplex X (singularEdgePath X σ)) =
    singularSimplexMap X σ
  rw [singularPathSimplex, singularSimplexMap_ofMap]
  ext u
  change singularSimplexMap X σ (stdSimplexHomeomorphUnitInterval.symm
    (stdSimplexHomeomorphUnitInterval u)) = singularSimplexMap X σ u
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

/-- The actual path chain of the extracted path is exactly the original
singular coproduct generator. -/
@[simp] theorem singularPathChain_edgePath (σ : IntegralSingularSimplex X 1) :
    singularPathChain X (singularEdgePath X σ) = singularSimplexChain X σ := by
  rw [singularPathChain, singularPathSimplex_edgePath]

@[simp] theorem singularSimplexVertex_path_zero {a b : X} (γ : Path a b) :
    singularSimplexVertex X (singularPathSimplex X γ) 0 = a := by
  unfold singularSimplexVertex singularPathSimplex
  rw [singularSimplexMap_ofMap]
  change γ (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) = a
  exact γ.source

@[simp] theorem singularSimplexVertex_path_one {a b : X} (γ : Path a b) :
    singularSimplexVertex X (singularPathSimplex X γ) 1 = b := by
  unfold singularSimplexVertex singularPathSimplex
  rw [singularSimplexMap_ofMap]
  change γ (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) = b
  exact γ.target

/-- In the other direction the continuous path itself is recovered literally.
This avoids obscuring the endpoint equalities in dependent path casts. -/
theorem singularEdgePath_path_toContinuousMap {a b : X} (γ : Path a b) :
    (singularEdgePath X (singularPathSimplex X γ)).toContinuousMap = γ.toContinuousMap := by
  ext t
  change singularSimplexMap X (singularPathSimplex X γ)
    (stdSimplexHomeomorphUnitInterval.symm t) = γ t
  rw [singularPathSimplex, singularSimplexMap_ofMap]
  change γ (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t)) = γ t
  rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]

/-- Every actual singular edge has the expected target-minus-source boundary. -/
theorem singularSimplexChain_boundary_edge (σ : IntegralSingularSimplex X 1) :
    (integralSingularChainComplex X).d 1 0 (singularSimplexChain X σ) =
      singularPointChain X (singularSimplexVertex X σ 1) -
        singularPointChain X (singularSimplexVertex X σ 0) := by
  rw [← singularPathChain_edgePath X σ, singularPathChain_boundary]

/-- Every actual singular zero-simplex is literally the point simplex at
its unique vertex value. -/
@[simp] theorem singularPointSimplex_vertex (σ : IntegralSingularSimplex X 0) :
    singularPointSimplex X (singularSimplexVertex X σ 0) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋0⦌)).injective
  change singularSimplexMap X (singularPointSimplex X (singularSimplexVertex X σ 0)) =
    singularSimplexMap X σ
  rw [singularPointSimplex, singularSimplexMap_ofMap]
  ext t
  change singularSimplexMap X σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)) = singularSimplexMap X σ t
  congr 1
  exact @Subsingleton.elim (stdSimplex ℝ (Fin 1)) inferInstance _ _

end Markov
