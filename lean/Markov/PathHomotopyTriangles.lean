import Markov.PathTriangle

/-! The two actual singular triangles of a relative path homotopy square.
Their common diagonal agrees literally. No chain or homology relation is
assumed by these topological constructions. -/

noncomputable section
namespace Markov

variable {X : Type*} [TopologicalSpace X] {a b : X} {γ δ : Path a b}

def simplexTailTime : C(stdSimplex ℝ (Fin 3), unitInterval) where
  toFun u := ⟨u.val 1 + u.val 2, add_nonneg (u.property.1 1) (u.property.1 2), by
    have hs := u.property.2
    simp only [Fin.sum_univ_three] at hs
    have h0 := u.property.1 0
    linarith⟩
  continuous_toFun := Continuous.subtype_mk
    (((continuous_apply 1).comp continuous_subtype_val).add
      ((continuous_apply 2).comp continuous_subtype_val)) _

def simplexLastTime : C(stdSimplex ℝ (Fin 3), unitInterval) where
  toFun u := ⟨u.val 2, mem_Icc_of_mem_stdSimplex u.property 2⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_apply 2).comp continuous_subtype_val) _

def triangleLowerSquare : C(stdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  simplexTailTime.prodMk simplexLastTime

def triangleUpperSquare : C(stdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  ⟨fun u => (triangleLowerSquare u).swap,
    (triangleLowerSquare.continuous.snd.prodMk triangleLowerSquare.continuous.fst)⟩

theorem triangleLowerSquare_face_zero (u : stdSimplex ℝ (Fin 2)) :
    triangleLowerSquare (triangleFaceMap 0 u) = (1, stdSimplexHomeomorphUnitInterval u) := by
  have hc := triangleFaceMap_zero_coordinates u
  apply Prod.ext <;> apply Subtype.ext
  · change (triangleFaceMap 0 u).val 1 + (triangleFaceMap 0 u).val 2 = 1
    rw [show (triangleFaceMap 0 u).val 1 = u.val 0 from congr_fun hc 1,
      show (triangleFaceMap 0 u).val 2 = u.val 1 from congr_fun hc 2]
    simpa only [Fin.sum_univ_two] using u.property.2
  · exact congr_fun hc 2

theorem triangleLowerSquare_face_one (u : stdSimplex ℝ (Fin 2)) :
    triangleLowerSquare (triangleFaceMap 1 u) =
      (stdSimplexHomeomorphUnitInterval u, stdSimplexHomeomorphUnitInterval u) := by
  have hc := triangleFaceMap_one_coordinates u
  apply Prod.ext <;> apply Subtype.ext
  · change (triangleFaceMap 1 u).val 1 + (triangleFaceMap 1 u).val 2 = u.val 1
    rw [show (triangleFaceMap 1 u).val 1 = 0 from congr_fun hc 1,
      show (triangleFaceMap 1 u).val 2 = u.val 1 from congr_fun hc 2, zero_add]
  · exact congr_fun hc 2

theorem triangleLowerSquare_face_two (u : stdSimplex ℝ (Fin 2)) :
    triangleLowerSquare (triangleFaceMap 2 u) = (stdSimplexHomeomorphUnitInterval u, 0) := by
  have hc := triangleFaceMap_two_coordinates u
  apply Prod.ext <;> apply Subtype.ext
  · change (triangleFaceMap 2 u).val 1 + (triangleFaceMap 2 u).val 2 = u.val 1
    rw [show (triangleFaceMap 2 u).val 1 = u.val 1 from congr_fun hc 1,
      show (triangleFaceMap 2 u).val 2 = 0 from congr_fun hc 2, add_zero]
  · exact congr_fun hc 2

def pathHomotopyDiagonal (F : Path.Homotopy γ δ) : Path a b where
  toFun t := F (t, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_id)
  source' := F.source 0
  target' := F.target 1

def pathHomotopyLowerTriangle (F : Path.Homotopy γ δ) : C(stdSimplex ℝ (Fin 3), X) :=
  (⟨F, F.continuous⟩ : C(unitInterval × unitInterval, X)).comp triangleLowerSquare

def pathHomotopyUpperTriangle (F : Path.Homotopy γ δ) : C(stdSimplex ℝ (Fin 3), X) :=
  (⟨F, F.continuous⟩ : C(unitInterval × unitInterval, X)).comp triangleUpperSquare

theorem pathHomotopyLowerTriangle_face_zero (F : Path.Homotopy γ δ) :
    (pathHomotopyLowerTriangle F).comp (triangleFaceMap 0) = pathSimplexMap δ := by
  ext u
  change F (triangleLowerSquare (triangleFaceMap 0 u)) = _
  rw [triangleLowerSquare_face_zero]
  exact F.apply_one _

theorem pathHomotopyLowerTriangle_face_one (F : Path.Homotopy γ δ) :
    (pathHomotopyLowerTriangle F).comp (triangleFaceMap 1) =
      pathSimplexMap (pathHomotopyDiagonal F) := by
  ext u
  change F (triangleLowerSquare (triangleFaceMap 1 u)) = _
  rw [triangleLowerSquare_face_one]
  rfl

theorem pathHomotopyLowerTriangle_face_two (F : Path.Homotopy γ δ) :
    (pathHomotopyLowerTriangle F).comp (triangleFaceMap 2) = pathSimplexMap (Path.refl a) := by
  ext u
  change F (triangleLowerSquare (triangleFaceMap 2 u)) = _
  rw [triangleLowerSquare_face_two]
  exact F.source _

theorem pathHomotopyUpperTriangle_face_zero (F : Path.Homotopy γ δ) :
    (pathHomotopyUpperTriangle F).comp (triangleFaceMap 0) = pathSimplexMap (Path.refl b) := by
  ext u
  change F ((triangleLowerSquare (triangleFaceMap 0 u)).swap) = _
  rw [triangleLowerSquare_face_zero]
  exact F.target _

theorem pathHomotopyUpperTriangle_face_one (F : Path.Homotopy γ δ) :
    (pathHomotopyUpperTriangle F).comp (triangleFaceMap 1) =
      pathSimplexMap (pathHomotopyDiagonal F) := by
  ext u
  change F ((triangleLowerSquare (triangleFaceMap 1 u)).swap) = _
  rw [triangleLowerSquare_face_one]
  rfl

theorem pathHomotopyUpperTriangle_face_two (F : Path.Homotopy γ δ) :
    (pathHomotopyUpperTriangle F).comp (triangleFaceMap 2) = pathSimplexMap γ := by
  ext u
  change F ((triangleLowerSquare (triangleFaceMap 2 u)).swap) = _
  rw [triangleLowerSquare_face_two]
  exact F.apply_zero _

end Markov
