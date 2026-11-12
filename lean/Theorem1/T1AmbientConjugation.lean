import Markov.PaperModularCommutators
import Markov.ModularAxisUniqueness

/-! Actual ambient SL(2,Z) normalizer conjugation. It preserves the quotient
point relation, metric periods, and simplicity of projected selected axes. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

def t1_ambientConjugation (h : SL(2,ℤ)) : modularTraceSubgroup ≃* modularTraceSubgroup where
  toFun g := ⟨h*g.val*h⁻¹,
    (inferInstance : modularTraceSubgroup.Normal).conj_mem g.val g.property h⟩
  invFun g := ⟨h⁻¹*g.val*(h⁻¹)⁻¹,
    (inferInstance : modularTraceSubgroup.Normal).conj_mem g.val g.property h⁻¹⟩
  left_inv g := by apply Subtype.ext; simp [mul_assoc]
  right_inv g := by apply Subtype.ext; simp [mul_assoc]
  map_mul' g k := by apply Subtype.ext; simp [mul_assoc]

theorem t1_ambientConjugation_val (h : SL(2,ℤ)) (g : modularTraceSubgroup) :
    (t1_ambientConjugation h g).val = h*g.val*h⁻¹ := rfl

theorem t1_ambient_quotient_eq_iff (h : SL(2,ℤ)) (z w : UpperHalfPlane) :
    modularTraceQuotientMk (h • z) = modularTraceQuotientMk (h • w) ↔
      modularTraceQuotientMk z = modularTraceQuotientMk w := by
  constructor
  · intro he
    obtain ⟨g,hg⟩ := (modularTraceQuotientMk_eq_iff _ _).mp he
    apply (modularTraceQuotientMk_eq_iff _ _).mpr
    refine ⟨t1_ambientConjugation h⁻¹ g,?_⟩
    have ht := congrArg (fun v : UpperHalfPlane => h⁻¹ • v) hg
    change (h⁻¹*g.val*(h⁻¹)⁻¹) • w = z
    simpa only [mul_smul,inv_inv,smul_inv_smul,inv_smul_smul] using ht
  · intro he
    obtain ⟨g,hg⟩ := (modularTraceQuotientMk_eq_iff _ _).mp he
    apply (modularTraceQuotientMk_eq_iff _ _).mpr
    refine ⟨t1_ambientConjugation h g,?_⟩
    have ht := congrArg (fun v : UpperHalfPlane => h • v) hg
    change (h*g.val*h⁻¹) • (h • w) = h • z
    simpa only [mul_smul,inv_smul_smul] using ht

theorem t1_ambientConjugation_trace (h : SL(2,ℤ)) (g : modularTraceSubgroup) :
    ((t1_ambientConjugation h g).val : IntMatrixTwo).trace = (g.val : IntMatrixTwo).trace := by
  change Matrix.trace ((h : IntMatrixTwo)*(g.val : IntMatrixTwo)*
    ((h⁻¹ : SL(2,ℤ)) : IntMatrixTwo)) = _
  rw [Matrix.trace_mul_cycle,← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul]

private def t1_ambientRealHom : SL(2,ℤ) →* SL(2,ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

theorem t1_ambientConjugation_period (h : SL(2,ℤ)) (g : modularTraceSubgroup) :
    modularClosedGeodesicPeriod (t1_ambientConjugation h g) = modularClosedGeodesicPeriod g := by
  change hyperbolicTranslationLength (t1_ambientRealHom (h*g.val*h⁻¹)) =
    hyperbolicTranslationLength (t1_ambientRealHom g.val)
  rw [map_mul,map_mul,map_inv,hyperbolicTranslationLength_conjugate]

theorem t1_ambientConjugation_axis (h : SL(2,ℤ)) (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hcg : 2 < |((t1_ambientConjugation h g).val : IntMatrixTwo).trace|) :
    ∃ c : ℝ, ∀ t : ℝ, modularHyperbolicAxis (t1_ambientConjugation h g) hcg t =
      h • modularHyperbolicAxis g hg (t+c) := by
  apply modularHyperbolicAxis_eq_of_isometry_equivariant (t1_ambientConjugation h g) hcg
    (fun t => h • modularHyperbolicAxis g hg t)
    ((modularInteger_isometry h).comp (modularHyperbolicAxis_isometry g hg))
  intro t
  rw [t1_ambientConjugation_period]
  change (h*g.val*h⁻¹) • (h • modularHyperbolicAxis g hg t) =
    h • modularHyperbolicAxis g hg (t+modularClosedGeodesicPeriod g)
  simp only [mul_smul,inv_smul_smul]
  rw [← modularHyperbolicAxis_action g hg t]
  rfl

end Markov
