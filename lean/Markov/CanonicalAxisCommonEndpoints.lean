import Markov.EquivariantCurveCayleyEndpoints

noncomputable section
open Filter Set Topology
open scoped MatrixGroups
namespace Markov

/-- An actual invariant isometric line is literally a shifted vertical line
in the supplied diagonalizing coordinate, retaining that exact SL matrix. -/
theorem hyperbolicInvariantAxis_normalized_vertical_of_diagonal_action
    (g : SL(2, ℝ)) (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, g • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (hlen : hyperbolicTranslationLength g = 2*Real.log a)
    (α : ℝ → UpperHalfPlane) (hα : Isometry α)
    (hαact : ∀ t, g • α t = α (t+hyperbolicTranslationLength g)) :
    ∃ c : ℝ, ∀ t, h⁻¹ • α t = hyperbolicVerticalAxis (t+c) := by
  obtain ⟨c, hc⟩ := hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    g a ha h hact hlen α hα hαact
  exact ⟨c, fun t => by rw [hc t, inv_smul_smul]⟩

/-- The actual supplied diagonalizing chart gives both literal complex
Cayley limits for every positively invariant isometric line. -/
theorem hyperbolicInvariantAxis_normalized_cayley_endpoints_of_diagonal_action
    (g : SL(2, ℝ)) (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, g • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (hlen : hyperbolicTranslationLength g = 2*Real.log a)
    (α : ℝ → UpperHalfPlane) (hα : Isometry α)
    (hαact : ∀ t, g • α t = α (t+hyperbolicTranslationLength g)) :
    Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • α t)) atBot (𝓝 (-1 : ℂ)) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • α t)) atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨c, hc⟩ := hyperbolicInvariantAxis_normalized_vertical_of_diagonal_action
    g a ha h hact hlen α hα hαact
  have hbound (t : ℝ) :
      dist (h⁻¹ • α t) (hyperbolicVerticalAxis (1*t)) ≤ |c| := by
    rw [hc t, one_mul, hyperbolicVerticalAxis_isometry.dist_eq, Real.dist_eq]
    have he : (t+c)-t = c := by ring
    rw [he]
  exact ⟨upperHalfPlaneCayley_tendsto_atBot_of_dist_vertical
      (fun t => h⁻¹ • α t) 1 |c| (by norm_num) hbound,
    upperHalfPlaneCayley_tendsto_atTop_of_dist_vertical
      (fun t => h⁻¹ • α t) 1 |c| (by norm_num) hbound⟩

/-- The selected actual modular axis has the same normalized endpoints in
any supplied actual diagonalizing chart of its actual holonomy. -/
theorem modularHyperbolicAxis_normalized_cayley_endpoints
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, (g.val : SL(2, ℝ)) • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (hlen : modularClosedGeodesicPeriod g = 2*Real.log a) :
    Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • modularHyperbolicAxis g hg t))
        atBot (𝓝 (-1 : ℂ)) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • modularHyperbolicAxis g hg t))
        atTop (𝓝 (1 : ℂ)) := by
  apply hyperbolicInvariantAxis_normalized_cayley_endpoints_of_diagonal_action
    (g.val : SL(2, ℝ)) a ha h hact hlen (modularHyperbolicAxis g hg)
    (modularHyperbolicAxis_isometry g hg)
  intro t
  simpa only [← modularInteger_smul_eq_real] using modularHyperbolicAxis_action g hg t

/-- The actual canonical proper embedded lift and the actual selected axis
have their two literal Cayley limits in one and the same actual SL coordinate. -/
theorem paperPrimitiveHolonomy_has_properEmbeddedLift_common_axis_endpoints
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      ∃ a : ℝ, ∃ ha : 1 < a, ∃ h : SL(2, ℝ),
        embeddedCircleConnectorDeck q hq d = paperPrimitiveHolonomy k p hp ∧
        IsProperMap (embeddedCircleConnectorRealLift q hq d) ∧
        IsClosedEmbedding (embeddedCircleConnectorRealLift q hq d) ∧
        (∀ z : UpperHalfPlane, ((paperPrimitiveHolonomy k p hp).val : SL(2, ℝ)) • z =
          h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))) ∧
        modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) = 2*Real.log a ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • embeddedCircleConnectorRealLift q hq d t)) atBot (𝓝 (-1 : ℂ)) ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • embeddedCircleConnectorRealLift q hq d t)) atTop (𝓝 (1 : ℂ)) ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
            (paperPrimitiveHolonomy_hyperbolic k p hp) t)) atBot (𝓝 (-1 : ℂ)) ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
            (paperPrimitiveHolonomy_hyperbolic k p hp) t)) atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨q, hq, d, hD, hproper, hemb, _hunit, a, ha, h, _B,
      hact, hlen, _hB, _hbound, hbotF, htopF⟩ :=
    paperPrimitiveHolonomy_has_properEmbeddedLift_cayley_endpoints k p hp
  obtain ⟨hbotAxis, htopAxis⟩ := modularHyperbolicAxis_normalized_cayley_endpoints
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)
    a ha h hact hlen
  exact ⟨q, hq, d, a, ha, h, hD, hproper, hemb, hact, hlen,
    hbotF, htopF, hbotAxis, htopAxis⟩

end Markov
