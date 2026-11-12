import Markov.PunctureChartWindingObstruction
import Markov.CircleHomotopyLoopConjugacy
import Markov.CanonicalEssentialClassObstruction
import Markov.CanonicalSimpleGeodesicCircle

/-! Canonical actual geodesic circles cannot be explicitly homotoped into the
actual deleted quarter-square puncture neighborhood. This is a literal geometric
obstruction, not a definition of peripheral classes by their H1 values. -/

noncomputable section
namespace Markov

/-- An actual supplied map homotopy preserves the genuine singular-H1 class
of every actual mapped loop, by actual based conjugacy and singular chain laws. -/
theorem singularLoopClass_map_eq_of_explicit_homotopy
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {q0 q1 : C(A,X)} (H : q0.Homotopy q1) {x : A} (γ : Path x x) :
    singularLoopClass X (γ.map q0.continuous)=singularLoopClass X (γ.map q1.continuous) := by
  obtain ⟨K⟩ := continuousMapHomotopy_loop_conjugate H γ
  exact (singularLoopClass_homotopy X K).trans
    (singularLoopClass_conjugate X (H.evalAt x) (γ.map q1.continuous))

private def actualPeriodCircleLoop (L : ℝ) : Path (0 : AddCircle L) 0 :=
  ((Path.segment (0 : ℝ) L).map (AddCircle.continuous_mk' L)).cast
    rfl (AddCircle.coe_period L).symm

/-- No actual circle map contained in the explicit deleted puncture chart is
homotopic to the actual canonical embedded metric geodesic circle. -/
theorem paperPrimitiveSimpleGeodesicCircle_not_homotopic_into_punctureNeighborhood
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (q : C(AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp)),ModularTraceQuotient))
    (hq : ∀ u, q u∈modularPunctureNeighborhood) :
    ¬(paperPrimitiveSimpleGeodesicCircle k p hp).Homotopic q := by
  rintro ⟨H⟩
  let γ := actualPeriodCircleLoop (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))
  have hne : singularLoopClass ModularTraceQuotient
      (γ.map (paperPrimitiveSimpleGeodesicCircle k p hp).continuous)≠0 := by
    change singularLoopClass ModularTraceQuotient (paperPrimitiveSimpleGeodesicCircleLoop k p hp)≠0
    rw [paperPrimitiveSimpleGeodesicCircleLoop_eq]
    exact paperPrimitiveClosedGeodesicLoop_singularClass_ne_zero k p hp
  have hz := modularPunctureNeighborhood_loop_singularClass_zero (γ.map q.continuous)
    (fun t => hq (γ t))
  exact hne ((singularLoopClass_map_eq_of_explicit_homotopy H γ).trans hz)

/-- In particular, the actual canonical embedded geodesic circle is not
contained in that literal puncture-chart neighborhood. -/
theorem paperPrimitiveSimpleGeodesicCircle_not_contained_in_punctureNeighborhood
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ¬(∀ u, paperPrimitiveSimpleGeodesicCircle k p hp u∈modularPunctureNeighborhood) := by
  intro hq
  exact paperPrimitiveSimpleGeodesicCircle_not_homotopic_into_punctureNeighborhood k p hp
    (paperPrimitiveSimpleGeodesicCircle k p hp) hq ⟨ContinuousMap.Homotopy.refl _⟩

end Markov
