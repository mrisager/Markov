import Markov.NormalizedCurveAxisSeparation
import Markov.HyperbolicAxisRangeTransport
import Markov.EquivariantCurveCayleyEndpoints
import Markov.CanonicalAxisRangeStabilizer

noncomputable section
open Filter Set Topology
open scoped MatrixGroups
namespace Markov

/-- The actual canonical invariant axis is disjoint from every deck translate
outside the powers of its actual holonomy. The proof uses the actual embedded
lift, actual disk crossing, and the checked axis-range stabilizer. -/
theorem paperPrimitiveHyperbolicAxis_translate_disjoint_of_not_mem
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (δ : modularTraceSubgroup)
    (hδ : δ ∉ Subgroup.zpowers (paperPrimitiveHolonomy k p hp)) :
    Disjoint
      (range (fun t : ℝ => δ • modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp) t))
      (range (modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp))) := by
  let g := paperPrimitiveHolonomy k p hp
  have hg : 2 < |(g.val : IntMatrixTwo).trace| := paperPrimitiveHolonomy_hyperbolic k p hp
  obtain ⟨q, hq, d, _hD, _hproper, _hemb, hunit, _hpoint, _hstabil, hcosets⟩ :=
    paperPrimitiveHolonomy_has_properEmbeddedLift k p hp
  let F : ℝ → UpperHalfPlane := embeddedCircleConnectorRealLift q hq d
  have hcF : Continuous F := (embeddedCircleConnectorRealLift q hq d).continuous
  obtain ⟨a, ha, A, B, hact, hlen, _hB, hbound, _hbot, _htop⟩ :=
    modularEquivariantCurve_has_normalized_cayley_endpoints g hg F hcF hunit
  let α := modularHyperbolicAxis g hg
  have hαact : ∀ t, (g.val : SL(2, ℝ)) • α t =
      α (t+hyperbolicTranslationLength (g.val : SL(2, ℝ))) := by
    intro t
    simpa only [α, ← modularInteger_smul_eq_real] using modularHyperbolicAxis_action g hg t
  obtain ⟨c, hα⟩ := hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    (g.val : SL(2, ℝ)) a ha A hact hlen α (modularHyperbolicAxis_isometry g hg) hαact
  let D : SL(2, ℝ) := δ.val
  let K : SL(2, ℝ) := A⁻¹*D*A
  let γ : ℝ → UpperHalfPlane := fun t => A⁻¹ • F t
  have hcγ : Continuous γ := (isometry_smul UpperHalfPlane A⁻¹).continuous.comp hcF
  have hdisjF : Disjoint (range (fun t : ℝ => δ • F t)) (range F) := by
    have hd := hcosets δ 1 (by simpa only [inv_one, one_mul] using hδ)
    simpa only [one_smul] using hd
  have hdisjγ : Disjoint (range γ) (range (fun t : ℝ => K • γ t)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s, hs⟩ ⟨t, ht⟩
    have he := congrArg (fun w : UpperHalfPlane => A • w) (hs.trans ht.symm)
    have hf : F s = D • F t := by
      simpa only [γ, K, mul_smul, smul_inv_smul, inv_smul_smul] using he
    have hfd : F s = δ • F t := by
      change F s = δ.val • F t
      rw [modularInteger_smul_eq_real]
      exact hf
    exact Set.disjoint_left.mp hdisjF ⟨t, hfd.symm⟩ ⟨s, rfl⟩
  have hκ : 0 < 2*Real.log a := mul_pos (by norm_num) (Real.log_pos ha)
  rcases normalizedCurve_axes_disjoint_or_eq γ hcγ (2*Real.log a) B hκ hbound K hdisjγ
      with hdisj | heq
  · have hd : Disjoint (range (fun t : ℝ => D • α t)) (range α) :=
      (hyperbolicAxis_chart_ranges_disjoint_iff A D α c hα).mpr hdisj
    simpa only [α, D, ← modularInteger_smul_eq_real] using hd
  · have he : range (fun t : ℝ => D • α t) = range α :=
      (hyperbolicAxis_chart_range_eq_iff A D α c hα).mpr heq
    have he' : range (fun t : ℝ => δ • modularHyperbolicAxis g hg t) =
        range (modularHyperbolicAxis g hg) := by
      simpa only [α, D, ← modularInteger_smul_eq_real] using he
    exact (hδ ((paperPrimitiveHyperbolicAxis_range_translate_eq_iff k p hp δ).mp he')).elim

/-- Separation of actual deck-translated axes gives the exact pointwise
identification relation of the projected axis, including its integer period. -/
theorem modularClosedGeodesic_eq_iff_int_period_of_axis_separation
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hsep : ∀ h : modularTraceSubgroup, h ∉ Subgroup.zpowers g →
      Disjoint (range (fun t : ℝ => h • modularHyperbolicAxis g hg t))
        (range (modularHyperbolicAxis g hg))) (s t : ℝ) :
    modularClosedGeodesic g hg s = modularClosedGeodesic g hg t ↔
      ∃ n : ℤ, s-t = (n : ℝ)*modularClosedGeodesicPeriod g := by
  constructor
  · intro he
    obtain ⟨δ, hδ⟩ := (modularTraceQuotientMk_eq_iff
      (modularHyperbolicAxis g hg s) (modularHyperbolicAxis g hg t)).mp he
    have hmem : δ ∈ Subgroup.zpowers g := by
      by_contra hn
      exact Set.disjoint_left.mp (hsep δ hn) ⟨t, hδ⟩ ⟨s, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hp : modularHyperbolicAxis g hg (t+(n : ℝ)*modularClosedGeodesicPeriod g) =
        modularHyperbolicAxis g hg s := by
      rw [modularHyperbolicAxis_add_int_period, hn]
      exact hδ
    have ht := (modularHyperbolicAxis_isometry g hg).injective hp
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    change modularTraceQuotientMk (modularHyperbolicAxis g hg s) =
      modularTraceQuotientMk (modularHyperbolicAxis g hg t)
    have hs : s = t+(n : ℝ)*modularClosedGeodesicPeriod g := by linarith
    rw [hs, modularHyperbolicAxis_add_int_period, modularTraceQuotientMk_smul]

/-- The actual canonical projected axis identifies exactly the integer-period
parameter pairs. No simple-curve premise remains. -/
theorem paperPrimitiveClosedGeodesic_eq_iff_int_period
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (s t : ℝ) :
    paperPrimitiveClosedGeodesic k p hp s = paperPrimitiveClosedGeodesic k p hp t ↔
      ∃ n : ℤ, s-t = (n : ℝ)*modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) := by
  exact modularClosedGeodesic_eq_iff_int_period_of_axis_separation
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)
    (paperPrimitiveHyperbolicAxis_translate_disjoint_of_not_mem k p hp) s t

/-- The same actual pointwise relation in the original numerical primitive
length normalization, using the previously checked period identity. -/
theorem paperPrimitiveClosedGeodesic_eq_iff_int_length
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (s t : ℝ) :
    paperPrimitiveClosedGeodesic k p hp s = paperPrimitiveClosedGeodesic k p hp t ↔
      ∃ n : ℤ, s-t = (n : ℝ)*
        primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
          (quadrantCoordinates k p) hp := by
  simpa only [paperPrimitiveHolonomy_period] using
    paperPrimitiveClosedGeodesic_eq_iff_int_period k p hp s t

end Markov
