import Markov.SingularEdges
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Actual oriented edges and the triangle path relation of a singular
two-simplex. Contractibility is proved for the real standard simplex; the
relation is then mapped through the actual continuous singular simplex.
No homology generation or Hurewicz equivalence is assumed. -/

noncomputable section
open CategoryTheory Opposite Simplicial
namespace Markov

variable (X : Type) [TopologicalSpace X]

/-- The actual singular face map corresponds to restriction of its continuous map. -/
theorem singularSimplexMap_face {n : ℕ} (σ : IntegralSingularSimplex X (n + 1))
    (i : Fin (n + 2)) :
    singularSimplexMap X
      ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ) =
      (singularSimplexMap X σ).comp
        ⟨stdSimplex.map (SimplexCategory.δ i), stdSimplex.continuous_map _⟩ := by
  calc
    _ = singularSimplexMap X
        ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op
          (singularSimplexOfMap X (singularSimplexMap X σ))) := by
            rw [singularSimplexOfMap_map]
    _ = _ := by rw [singularSimplexOfMap_face, singularSimplexMap_ofMap]

/-- The vertices of an actual triangular face have their literal ordered values. -/
theorem singularSimplexVertex_face (σ : IntegralSingularSimplex X 2)
    (i : Fin 3) (j : Fin 2) :
    singularSimplexVertex X
      ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ) j =
        singularSimplexVertex X σ (i.succAbove j) := by
  unfold singularSimplexVertex
  rw [singularSimplexMap_face]
  change singularSimplexMap X σ
    (stdSimplex.map (SimplexCategory.δ i) (stdSimplex.vertex (S := ℝ) j)) = _
  rw [stdSimplex.map_vertex]
  rfl

/-- The actual standard triangular edge, in its increasing vertex orientation. -/
def standardTriangleEdgePath (i : Fin 3) :
    Path (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2)))
      (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2))) :=
  (standardOneSimplexPath.map (triangleFaceMap i).continuous).cast
    (stdSimplex.map_vertex (S := ℝ) i.succAbove (0 : Fin 2)).symm
    (stdSimplex.map_vertex (S := ℝ) i.succAbove (1 : Fin 2)).symm

private theorem standardTriangleContractible :
    ContractibleSpace (stdSimplex ℝ (Fin 3)) :=
  (convex_stdSimplex ℝ (Fin 3)).contractibleSpace
    ⟨Pi.single (0 : Fin 3) (1 : ℝ), single_mem_stdSimplex ℝ (0 : Fin 3)⟩

/-- The two successive standard edges are genuinely homotopic, with fixed
endpoints, to the remaining edge inside the actual standard triangle. -/
theorem standardTriangleEdgePath_concat_homotopic :
    Path.Homotopic ((standardTriangleEdgePath 2).trans (standardTriangleEdgePath 0))
      (standardTriangleEdgePath 1) := by
  letI := standardTriangleContractible
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- Ordered edge paths of the actual singular triangle, with exact original vertices. -/
def singularTriangleEdgePath (σ : IntegralSingularSimplex X 2) (i : Fin 3) :
    Path (singularSimplexVertex X σ (i.succAbove (0 : Fin 2)))
      (singularSimplexVertex X σ (i.succAbove (1 : Fin 2))) :=
  (standardTriangleEdgePath i).map (singularSimplexMap X σ).continuous

/-- The actual singular triangle carries the genuine relative-endpoint edge relation. -/
theorem singularTriangleEdgePath_concat_homotopic (σ : IntegralSingularSimplex X 2) :
    Path.Homotopic ((singularTriangleEdgePath X σ 2).trans (singularTriangleEdgePath X σ 0))
      (singularTriangleEdgePath X σ 1) := by
  simpa only [singularTriangleEdgePath, Path.map_trans] using
    standardTriangleEdgePath_concat_homotopic.map (singularSimplexMap X σ)

/-- Extracting the path of the actual singular face agrees literally with
the ordered edge path on underlying continuous maps. -/
theorem singularEdgePath_face_toContinuousMap (σ : IntegralSingularSimplex X 2) (i : Fin 3) :
    (singularEdgePath X
      ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ)).toContinuousMap =
        (singularTriangleEdgePath X σ i).toContinuousMap := by
  ext t
  change singularSimplexMap X
    ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ)
      (stdSimplexHomeomorphUnitInterval.symm t) =
    singularSimplexMap X σ
      (stdSimplex.map i.succAbove (stdSimplexHomeomorphUnitInterval.symm t))
  rw [singularSimplexMap_face]
  rfl

/-- The path of the literal singular face, with the proved endpoint
identifications explicitly cast to the original triangle vertices. -/
def singularOrientedFacePath (σ : IntegralSingularSimplex X 2) (i : Fin 3) :
    Path (singularSimplexVertex X σ (i.succAbove (0 : Fin 2)))
      (singularSimplexVertex X σ (i.succAbove (1 : Fin 2))) :=
  (singularEdgePath X
    ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ)).cast
      (singularSimplexVertex_face X σ i 0).symm
      (singularSimplexVertex_face X σ i 1).symm

theorem singularOrientedFacePath_eq (σ : IntegralSingularSimplex X 2) (i : Fin 3) :
    singularOrientedFacePath X σ i = singularTriangleEdgePath X σ i := by
  ext t
  exact congrArg (fun f : C(unitInterval, X) => f t)
    (singularEdgePath_face_toContinuousMap X σ i)

/-- In terms of the actual three singular faces, edge01 followed by edge12
is genuinely homotopic to edge02, with all endpoint casts proved above. -/
theorem singularOrientedFacePath_concat_homotopic (σ : IntegralSingularSimplex X 2) :
    Path.Homotopic ((singularOrientedFacePath X σ 2).trans (singularOrientedFacePath X σ 0))
      (singularOrientedFacePath X σ 1) := by
  rw [singularOrientedFacePath_eq, singularOrientedFacePath_eq, singularOrientedFacePath_eq]
  exact singularTriangleEdgePath_concat_homotopic X σ

end Markov
