import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Path

/-! Oriented topological singular simplices of paths and their concatenation.
The triangle uses the actual standard simplex and actual face inclusions;
no homology relation is assumed. -/

noncomputable section
namespace Markov

variable {X : Type*} [TopologicalSpace X] {a b c : X}

def pathSimplexMap (γ : Path a b) : C(stdSimplex ℝ (Fin 2), X) :=
  γ.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

@[simp] theorem pathSimplexMap_apply (γ : Path a b) (u : stdSimplex ℝ (Fin 2)) :
    pathSimplexMap γ u = γ (stdSimplexHomeomorphUnitInterval u) := rfl

def triangleFaceMap (i : Fin 3) :
    C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3)) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩

theorem triangleFaceMap_zero_coordinates (u : stdSimplex ℝ (Fin 2)) :
    (triangleFaceMap 0 u).val = ![0, u.val 0, u.val 1] := by
  ext i
  change FunOnFinite.linearMap ℝ ℝ ((0 : Fin 3).succAbove) u.val i = _
  fin_cases i <;>
    simp [FunOnFinite.linearMap_apply_apply,
      Fin.sum_univ_two, Finset.sum_filter]

theorem triangleFaceMap_one_coordinates (u : stdSimplex ℝ (Fin 2)) :
    (triangleFaceMap 1 u).val = ![u.val 0, 0, u.val 1] := by
  ext i
  change FunOnFinite.linearMap ℝ ℝ ((1 : Fin 3).succAbove) u.val i = _
  fin_cases i <;>
    simp [FunOnFinite.linearMap_apply_apply,
      Fin.sum_univ_two, Finset.sum_filter]

theorem triangleFaceMap_two_coordinates (u : stdSimplex ℝ (Fin 2)) :
    (triangleFaceMap 2 u).val = ![u.val 0, u.val 1, 0] := by
  ext i
  change FunOnFinite.linearMap ℝ ℝ ((2 : Fin 3).succAbove) u.val i = _
  have hf : (2 : Fin 3).succAbove = ![(0 : Fin 3), 1] := by
    funext j
    fin_cases j <;> decide
  rw [hf]
  fin_cases i <;>
    simp [FunOnFinite.linearMap_apply_apply, Fin.sum_univ_two, Finset.sum_filter]

/-- A genuine continuous two-simplex whose three oriented faces are the
second path, concatenation, and first path, respectively. -/
def pathConcatTriangleMap (γ : Path a b) (δ : Path b c) :
    C(stdSimplex ℝ (Fin 3), X) where
  toFun u := (γ.trans δ).extend (u.val 1 / 2 + u.val 2)
  continuous_toFun := (γ.trans δ).continuous_extend.comp
    (((continuous_apply 1).comp continuous_subtype_val).div_const 2 |>.add
      ((continuous_apply 2).comp continuous_subtype_val))

theorem pathConcatTriangleMap_face_zero (γ : Path a b) (δ : Path b c) :
    (pathConcatTriangleMap γ δ).comp (triangleFaceMap 0) = pathSimplexMap δ := by
  ext u
  change (γ.trans δ).extend ((triangleFaceMap 0 u).val 1 / 2 +
    (triangleFaceMap 0 u).val 2) = δ (stdSimplexHomeomorphUnitInterval u)
  have hc := triangleFaceMap_zero_coordinates u
  have h1 : (triangleFaceMap 0 u).val 1 = u.val 0 := congr_fun hc 1
  have h2 : (triangleFaceMap 0 u).val 2 = u.val 1 := congr_fun hc 2
  rw [h1, h2, Path.extend_trans_of_half_le]
  · have ht : 2 * (u.val 0 / 2 + u.val 1) - 1 = u.val 1 := by
      have hs : u.val 0 + u.val 1 = 1 := by simpa only [Fin.sum_univ_two] using u.property.2
      linarith
    rw [ht, Path.extend_apply _ (mem_Icc_of_mem_stdSimplex u.property 1)]
    rfl
  · have hs : u.val 0 + u.val 1 = 1 := by simpa only [Fin.sum_univ_two] using u.property.2
    linarith [u.property.1 1]

theorem pathConcatTriangleMap_face_one (γ : Path a b) (δ : Path b c) :
    (pathConcatTriangleMap γ δ).comp (triangleFaceMap 1) = pathSimplexMap (γ.trans δ) := by
  ext u
  change (γ.trans δ).extend ((triangleFaceMap 1 u).val 1 / 2 +
    (triangleFaceMap 1 u).val 2) = (γ.trans δ) (stdSimplexHomeomorphUnitInterval u)
  have hc := triangleFaceMap_one_coordinates u
  have h1 : (triangleFaceMap 1 u).val 1 = 0 := congr_fun hc 1
  have h2 : (triangleFaceMap 1 u).val 2 = u.val 1 := congr_fun hc 2
  rw [h1, h2, zero_div, zero_add, Path.extend_apply _ (mem_Icc_of_mem_stdSimplex u.property 1)]
  rfl

theorem pathConcatTriangleMap_face_two (γ : Path a b) (δ : Path b c) :
    (pathConcatTriangleMap γ δ).comp (triangleFaceMap 2) = pathSimplexMap γ := by
  ext u
  change (γ.trans δ).extend ((triangleFaceMap 2 u).val 1 / 2 +
    (triangleFaceMap 2 u).val 2) = γ (stdSimplexHomeomorphUnitInterval u)
  have hc := triangleFaceMap_two_coordinates u
  have h1 : (triangleFaceMap 2 u).val 1 = u.val 1 := congr_fun hc 1
  have h2 : (triangleFaceMap 2 u).val 2 = 0 := congr_fun hc 2
  rw [h1, h2, add_zero, Path.extend_trans_of_le_half]
  · have ht : 2 * (u.val 1 / 2) = u.val 1 := by ring
    rw [ht, Path.extend_apply _ (mem_Icc_of_mem_stdSimplex u.property 1)]
    rfl
  · linarith [(mem_Icc_of_mem_stdSimplex u.property 1).2]

end Markov
