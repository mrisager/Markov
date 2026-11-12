import Markov.BoundaryArc

/-! The boundary slope chart and its actual inverse are continuous.
This upgrades the radial boundary parametrization to a homeomorphism,
without assuming any identification of cutoff connected components. -/

noncomputable section
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_basisCoord (B : Module.Basis (Fin 2) ℝ E) (i : Fin 2) :
    Continuous (B.coord i) := by
  letI : FiniteDimensional ℝ E := Module.Finite.of_basis B
  exact (B.coord i).continuous_of_finiteDimensional

theorem basisSlope_continuousAt (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hx : B.coord 0 x ≠ 0) : ContinuousAt (basisSlope B) x :=
  (continuous_basisCoord B 1).continuousAt.div
    (continuous_basisCoord B 0).continuousAt hx

theorem basisSlope_continuousOn_arc (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    ContinuousOn (basisSlope B) (slopeBoundaryArc B a b) := by
  intro x hx
  exact (basisSlope_continuousAt B x hx.2.1.ne').continuousWithinAt

/-- Each actual open unit-boundary slope arc is homeomorphic to its
parameter interval, with inverse given by the coordinate slope. -/
def slopeBoundaryArcHomeomorph (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    Set.Ioo a b ≃ₜ slopeBoundaryArc B a b where
  toFun t := ⟨radialBasisSection B t, norm_radialBasisSection B t,
    radialBasisSection_coord_zero_pos B t, by simpa using t.property.1,
    by simpa using t.property.2⟩
  invFun x := ⟨basisSlope B x, x.property.2.2⟩
  left_inv t := Subtype.ext (basisSlope_radialBasisSection B t)
  right_inv x := Subtype.ext (radialBasisSection_basisSlope B x x.property.1 x.property.2.1)
  continuous_toFun := ((radialBasisSection_continuous B).continuousOn.restrict).subtype_mk _
  continuous_invFun := ((basisSlope_continuousOn_arc B a b).restrict).subtype_mk _

/-- The closed radial subinterval gives the closure of the open arc when
the endpoints are distinct. This is a statement about the actual boundary. -/
theorem closure_slopeBoundaryArc (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) (hab : a < b) :
    closure (slopeBoundaryArc B a b) = radialBasisSection B '' Set.Icc a b := by
  rw [← radialBasisSection_image_Ioo]
  have hc : IsCompact (radialBasisSection B '' Set.Icc a b) :=
    isCompact_Icc.image (radialBasisSection_continuous B)
  apply le_antisymm
  · apply closure_minimal (Set.image_mono Set.Ioo_subset_Icc_self) hc.isClosed
  · rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image (radialBasisSection_continuous B)

end Markov
