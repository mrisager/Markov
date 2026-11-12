import Markov.ModularClosedGeodesic
import Markov.HyperbolicAxisMinset

/-! Exact uniqueness, deck conjugation, and inverse orientation of actual
invariant modular axes. This concerns global isometric lifts only: no arbitrary
local-geodesic straightening, simplicity, or simple-class classification. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

private theorem modularAxis_real_hyperbolic (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    2 < |((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  have ht : ((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      ((g.val : IntMatrixTwo).trace : ℝ) := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [ht]
  exact_mod_cast hg

private def modularAxis_realHom : modularTraceSubgroup →* SL(2, ℝ) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp modularTraceSubgroup.subtype

/-- Any actual globally isometric invariant lift agrees with the selected
modular axis after a real parameter shift. -/
theorem modularHyperbolicAxis_eq_of_isometry_equivariant
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (hact : ∀ t : ℝ, g • γ t = γ (t + modularClosedGeodesicPeriod g)) :
    ∃ c : ℝ, ∀ t : ℝ, modularHyperbolicAxis g hg t = γ (t + c) := by
  apply hyperbolicTranslationLength_invariantAxis_eq (g.val : SL(2, ℝ))
    (modularAxis_real_hyperbolic g hg) (modularHyperbolicAxis g hg) γ
    (modularHyperbolicAxis_isometry g hg) hγ
  · intro t
    simpa only [← modularInteger_smul_eq_real] using modularHyperbolicAxis_action g hg t
  · intro t
    simpa only [← modularInteger_smul_eq_real] using hact t

/-- Actual subgroup conjugation preserves the literal integral matrix trace. -/
theorem modularTraceSubgroup_trace_conjugate (g h : modularTraceSubgroup) :
    (((h * g * h⁻¹).val : IntMatrixTwo).trace) = (g.val : IntMatrixTwo).trace := by
  change Matrix.trace ((h.val : IntMatrixTwo) * (g.val : IntMatrixTwo) *
    ((h.val⁻¹ : SL(2, ℤ)) : IntMatrixTwo)) = _
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

/-- The actual conjugate deck matrix remains hyperbolic. -/
theorem modularTraceSubgroup_hyperbolic_conjugate
    (g h : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    2 < |((h * g * h⁻¹).val : IntMatrixTwo).trace| := by
  rw [modularTraceSubgroup_trace_conjugate]
  exact hg

/-- Conjugate actual deck elements have equal metric translation periods. -/
theorem modularClosedGeodesicPeriod_conjugate (g h : modularTraceSubgroup) :
    modularClosedGeodesicPeriod (h * g * h⁻¹) = modularClosedGeodesicPeriod g := by
  change hyperbolicTranslationLength (modularAxis_realHom (h * g * h⁻¹)) =
    hyperbolicTranslationLength (modularAxis_realHom g)
  rw [map_mul, map_mul, map_inv, hyperbolicTranslationLength_conjugate]

/-- The selected axis of an actual conjugate deck element is the conjugated
selected axis with an explicit real parameter shift. -/
theorem modularHyperbolicAxis_conjugate
    (g h : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgh : 2 < |((h * g * h⁻¹).val : IntMatrixTwo).trace|) :
    ∃ c : ℝ, ∀ t : ℝ, modularHyperbolicAxis (h * g * h⁻¹) hgh t =
      h • modularHyperbolicAxis g hg (t + c) := by
  apply modularHyperbolicAxis_eq_of_isometry_equivariant (h * g * h⁻¹) hgh
    (fun t => h • modularHyperbolicAxis g hg t)
    ((modularTraceSubgroup_isometry h).comp (modularHyperbolicAxis_isometry g hg))
  intro t
  rw [modularClosedGeodesicPeriod_conjugate]
  simp only [mul_smul, inv_smul_smul, modularHyperbolicAxis_action]

/-- Actual Γ-conjugate closed-axis curves agree after a parameter shift in
the existing orbit quotient. -/
theorem modularClosedGeodesic_conjugate
    (g h : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgh : 2 < |((h * g * h⁻¹).val : IntMatrixTwo).trace|) :
    ∃ c : ℝ, ∀ t : ℝ, modularClosedGeodesic (h * g * h⁻¹) hgh t =
      modularClosedGeodesic g hg (t + c) := by
  obtain ⟨c, hc⟩ := modularHyperbolicAxis_conjugate g h hg hgh
  refine ⟨c, ?_⟩
  intro t
  change modularTraceQuotientMk _ = modularTraceQuotientMk _
  rw [hc, modularTraceQuotientMk_smul]

/-- Hence actual conjugate deck elements have exactly the same
unparameterized projected closed-axis image. -/
theorem modularClosedGeodesic_range_conjugate
    (g h : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgh : 2 < |((h * g * h⁻¹).val : IntMatrixTwo).trace|) :
    Set.range (modularClosedGeodesic (h * g * h⁻¹) hgh) =
      Set.range (modularClosedGeodesic g hg) := by
  obtain ⟨c, hc⟩ := modularClosedGeodesic_conjugate g h hg hgh
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + c, (hc t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - c, by simpa using hc (t - c)⟩

/-- Inverting an actual two-by-two determinant-one deck matrix preserves its
literal integral trace. -/
theorem modularTraceSubgroup_trace_inv (g : modularTraceSubgroup) :
    ((g⁻¹).val : IntMatrixTwo).trace = (g.val : IntMatrixTwo).trace := by
  change Matrix.trace ((g.val⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = _
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, add_comm]

/-- The actual inverse deck matrix remains hyperbolic. -/
theorem modularTraceSubgroup_hyperbolic_inv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    2 < |((g⁻¹).val : IntMatrixTwo).trace| := by
  rw [modularTraceSubgroup_trace_inv]
  exact hg

private theorem modularAxis_real_translationLength_inv (g : SL(2, ℝ)) :
    hyperbolicTranslationLength g⁻¹ = hyperbolicTranslationLength g := by
  unfold hyperbolicTranslationLength
  congr 1
  ext d
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨g⁻¹ • z, ?_⟩
    dsimp only
    rw [smul_inv_smul, dist_comm]
  · rintro ⟨z, rfl⟩
    refine ⟨g • z, ?_⟩
    dsimp only
    rw [inv_smul_smul, dist_comm]

/-- Actual metric translation period is unchanged under deck inversion. -/
theorem modularClosedGeodesicPeriod_inv (g : modularTraceSubgroup) :
    modularClosedGeodesicPeriod g⁻¹ = modularClosedGeodesicPeriod g := by
  change hyperbolicTranslationLength (modularAxis_realHom g⁻¹) =
    hyperbolicTranslationLength (modularAxis_realHom g)
  rw [map_inv, modularAxis_real_translationLength_inv]

/-- The selected inverse axis is the original selected axis with reversed
orientation and a real parameter shift. -/
theorem modularHyperbolicAxis_inv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgi : 2 < |((g⁻¹).val : IntMatrixTwo).trace|) :
    ∃ c : ℝ, ∀ t : ℝ, modularHyperbolicAxis g⁻¹ hgi t =
      modularHyperbolicAxis g hg (-(t + c)) := by
  apply modularHyperbolicAxis_eq_of_isometry_equivariant g⁻¹ hgi
    (fun t => modularHyperbolicAxis g hg (-t))
    ((modularHyperbolicAxis_isometry g hg).comp isometry_neg)
  intro t
  rw [modularClosedGeodesicPeriod_inv]
  have he := modularHyperbolicAxis_action g hg (-t - modularClosedGeodesicPeriod g)
  have ht : -t - modularClosedGeodesicPeriod g + modularClosedGeodesicPeriod g = -t := by ring
  rw [ht] at he
  calc
    g⁻¹ • modularHyperbolicAxis g hg (-t) =
        modularHyperbolicAxis g hg (-t - modularClosedGeodesicPeriod g) := by
      rw [← he, inv_smul_smul]
    _ = modularHyperbolicAxis g hg (-(t + modularClosedGeodesicPeriod g)) := by
      congr 1
      ring

/-- Actual inverse-deck projected curves agree after orientation reversal
and a parameter shift in the existing orbit quotient. -/
theorem modularClosedGeodesic_inv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgi : 2 < |((g⁻¹).val : IntMatrixTwo).trace|) :
    ∃ c : ℝ, ∀ t : ℝ, modularClosedGeodesic g⁻¹ hgi t =
      modularClosedGeodesic g hg (-(t + c)) := by
  obtain ⟨c, hc⟩ := modularHyperbolicAxis_inv g hg hgi
  exact ⟨c, fun t => congrArg modularTraceQuotientMk (hc t)⟩

/-- Actual inverse deck elements have exactly the same unparameterized
projected closed-axis image. -/
theorem modularClosedGeodesic_range_inv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hgi : 2 < |((g⁻¹).val : IntMatrixTwo).trace|) :
    Set.range (modularClosedGeodesic g⁻¹ hgi) = Set.range (modularClosedGeodesic g hg) := by
  obtain ⟨c, hc⟩ := modularClosedGeodesic_inv g hg hgi
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-(t + c), (hc t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨-t - c, ?_⟩
    rw [hc]
    congr 1
    ring

end Markov
