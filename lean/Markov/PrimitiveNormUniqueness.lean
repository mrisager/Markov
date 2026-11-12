import Markov.PrimitiveRayDecomposition
import Markov.EuclideanPairCoordinates
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Separation.Hausdorff

/-! Uniqueness of a continuous homogeneous extension of primitive integer
values. Agreement with actual geometric lengths remains an explicit premise;
this lemma does not supply the quotient or geodesic dictionary. -/

noncomputable section
open Set
namespace Markov

/-- Every rational coordinate pair is a real multiple of an integer pair. -/
theorem rational_pair_eq_smul_integer (q : ℚ × ℚ) :
    ∃ a : ℝ, ∃ d : ℤ × ℤ,
      ((q.1 : ℝ), (q.2 : ℝ)) = a • ((d.1 : ℝ), (d.2 : ℝ)) := by
  refine ⟨1 / ((q.1.den : ℝ) * (q.2.den : ℝ)),
    (q.1.num * (q.2.den : ℤ), q.2.num * (q.1.den : ℤ)), ?_⟩
  have h1 : (q.1.den : ℝ) ≠ 0 := by exact_mod_cast q.1.den_ne_zero
  have h2 : (q.2.den : ℝ) ≠ 0 := by exact_mod_cast q.2.den_ne_zero
  apply Prod.ext <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
      Rat.cast_def] <;> field_simp

/-- Homogeneity extends agreement on primitive integer vectors to all
integer vectors, including zero. -/
theorem homogeneous_pair_eq_on_integer_of_primitive
    (f g : ℝ × ℝ → ℝ)
    (hf : ∀ a : ℝ, ∀ x, f (a • x) = |a| * f x)
    (hg : ∀ a : ℝ, ∀ x, g (a • x) = |a| * g x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      f ((d.1 : ℝ), (d.2 : ℝ)) = g ((d.1 : ℝ), (d.2 : ℝ)))
    (d : ℤ × ℤ) : f ((d.1 : ℝ), (d.2 : ℝ)) = g ((d.1 : ℝ), (d.2 : ℝ)) := by
  by_cases hd : d = (0, 0)
  · subst d
    have hf0 := hf 0 (0, 0)
    have hg0 := hg 0 (0, 0)
    simp only [zero_smul, abs_zero, zero_mul] at hf0 hg0
    simpa using hf0.trans hg0.symm
  · let p := primitiveRayEquiv ⟨d, hd⟩
    have hfactor : (p.1 : ℕ) • p.2.1 = d := primitiveRayEquiv_factorization ⟨d, hd⟩
    have hcoord : ((d.1 : ℝ), (d.2 : ℝ)) = (p.1 : ℝ) •
        ((p.2.1.1 : ℝ), (p.2.1.2 : ℝ)) := by
      have hx := congrArg Prod.fst hfactor
      have hy := congrArg Prod.snd hfactor
      apply Prod.ext
      · change (d.1 : ℝ) = (p.1 : ℝ) * (p.2.1.1 : ℝ)
        exact_mod_cast hx.symm
      · change (d.2 : ℝ) = (p.1 : ℝ) * (p.2.1.2 : ℝ)
        exact_mod_cast hy.symm
    rw [hcoord, hf, hg, hp p.2.1 p.2.2]

/-- Continuity and real homogeneity determine a plane function from its
values on the full signed primitive integer lattice. -/
theorem continuous_homogeneous_pair_ext_of_primitive
    (f g : ℝ × ℝ → ℝ) (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ a : ℝ, ∀ x, f (a • x) = |a| * f x)
    (hg : ∀ a : ℝ, ∀ x, g (a • x) = |a| * g x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      f ((d.1 : ℝ), (d.2 : ℝ)) = g ((d.1 : ℝ), (d.2 : ℝ))) : f = g := by
  have hdense : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  apply Continuous.ext_on hdense hfc hgc
  rintro x ⟨q, rfl⟩
  obtain ⟨a, d, heq⟩ := rational_pair_eq_smul_integer q
  change f ((q.1 : ℝ), (q.2 : ℝ)) = g ((q.1 : ℝ), (q.2 : ℝ))
  rw [heq, hf, hg, homogeneous_pair_eq_on_integer_of_primitive f g hf hg hp d]

/-- The corresponding uniqueness result in the actual Euclidean lattice
coordinates used for the count and area. The primitive agreement is explicit. -/
theorem continuous_homogeneous_euclidean_ext_of_primitive
    (f g : EuclideanSpace ℝ (Fin 2) → ℝ) (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ a : ℝ, ∀ x, f (a • x) = |a| * f x)
    (hg : ∀ a : ℝ, ∀ x, g (a • x) = |a| * g x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      f (euclideanIntDirection d) = g (euclideanIntDirection d)) : f = g := by
  have hpair := continuous_homogeneous_pair_ext_of_primitive
    (f ∘ euclideanPairContinuousLinearEquiv) (g ∘ euclideanPairContinuousLinearEquiv)
    (hfc.comp euclideanPairContinuousLinearEquiv.continuous)
    (hgc.comp euclideanPairContinuousLinearEquiv.continuous)
    (by intro a x; simp only [Function.comp_apply, map_smul]; exact hf a _)
    (by intro a x; simp only [Function.comp_apply, map_smul]; exact hg a _)
    (by intro d hd; simpa using hp d hd)
  funext x
  obtain ⟨p, rfl⟩ := euclideanPairContinuousLinearEquiv.surjective x
  exact congrFun hpair p

end Markov
