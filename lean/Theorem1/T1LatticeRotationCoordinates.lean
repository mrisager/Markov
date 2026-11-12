import T1AmbientConjugation
import Markov.ModularMarkedLoops

/-! The exact marked homology action of the genuine ambient modular T.
It is the integral order-six rotation (p,q) ↦ (p-q,p). -/
noncomputable section
open scoped MatrixGroups
namespace Markov

def t1_latticeRotation (p : ℤ × ℤ) : ℤ × ℤ := (p.1-p.2,p.1)

def t1_latticeRotationHom : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ) where
  toFun p := Multiplicative.ofAdd (t1_latticeRotation p.toAdd)
  map_one' := rfl
  map_mul' p q := by
    change Multiplicative.ofAdd (t1_latticeRotation (p.toAdd+q.toAdd)) =
      Multiplicative.ofAdd (t1_latticeRotation p.toAdd+t1_latticeRotation q.toAdd)
    congr 1
    apply Prod.ext
    · dsimp [t1_latticeRotation]
      ring
    · rfl

theorem t1_latticeRotation_coprime (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    IsCoprime (t1_latticeRotation p).1 (t1_latticeRotation p).2 := by
  obtain ⟨a,b,hab⟩ := hp
  refine ⟨-b,a+b,?_⟩
  dsimp [t1_latticeRotation]
  linear_combination hab

theorem t1_ambient_T_basis_zero :
    t1_ambientConjugation ModularGroup.T (paperTraceFreeGroupBasis 0) =
      paperTraceFreeGroupBasis 1 * paperTraceFreeGroupBasis 0 := by
  apply Subtype.ext
  change ModularGroup.T * (paperTraceFreeGroupBasis 0).val * ModularGroup.T⁻¹ =
    (paperTraceFreeGroupBasis 1).val * (paperTraceFreeGroupBasis 0).val
  rw [paperTraceFreeGroupBasis_zero,paperTraceFreeGroupBasis_one,T_conjugates_paperA]

theorem t1_ambient_T_basis_one :
    t1_ambientConjugation ModularGroup.T (paperTraceFreeGroupBasis 1) =
      (paperTraceFreeGroupBasis 0)⁻¹ := by
  apply Subtype.ext
  change ModularGroup.T * (paperTraceFreeGroupBasis 1).val * ModularGroup.T⁻¹ =
    (paperTraceFreeGroupBasis 0).val⁻¹
  rw [paperTraceFreeGroupBasis_one,paperTraceFreeGroupBasis_zero,T_conjugates_paperB]

theorem t1_ambient_T_marked_coordinates (g : modularTraceSubgroup) :
    paperTraceAbelianizationCoordinates (t1_ambientConjugation ModularGroup.T g) =
      Multiplicative.ofAdd (t1_latticeRotation (paperTraceAbelianizationCoordinates g).toAdd) := by
  have hh : paperTraceAbelianizationCoordinates.comp
      (t1_ambientConjugation ModularGroup.T).toMonoidHom =
      t1_latticeRotationHom.comp paperTraceAbelianizationCoordinates := by
    apply paperTraceFreeGroupBasis.ext_hom
    intro i
    fin_cases i
    · change paperTraceAbelianizationCoordinates
          (t1_ambientConjugation ModularGroup.T (paperTraceFreeGroupBasis 0)) =
        t1_latticeRotationHom (paperTraceAbelianizationCoordinates (paperTraceFreeGroupBasis 0))
      rw [t1_ambient_T_basis_zero,map_mul,paperTraceAbelianizationCoordinates_basis_one,
        paperTraceAbelianizationCoordinates_basis_zero]
      rfl
    · change paperTraceAbelianizationCoordinates
          (t1_ambientConjugation ModularGroup.T (paperTraceFreeGroupBasis 1)) =
        t1_latticeRotationHom (paperTraceAbelianizationCoordinates (paperTraceFreeGroupBasis 1))
      rw [t1_ambient_T_basis_one,map_inv,paperTraceAbelianizationCoordinates_basis_zero,
        paperTraceAbelianizationCoordinates_basis_one]
      rfl
  exact DFunLike.congr_fun hh g

end Markov
