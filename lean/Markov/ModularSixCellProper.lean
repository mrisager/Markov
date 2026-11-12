import Markov.ModularTraceQuotientMetric
import Markov.ModularSixCellBoundary
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.ContinuousMap.Basic

/-! Properness of the actual six closed-cell projection. The kernel quotient
is homeomorphic to the actual hyperbolic orbit quotient; no ideal polygon
or punctured-torus identification is asserted. -/

noncomputable section
open scoped MatrixGroups
open Set Topology
namespace Markov

theorem modular_I_mem_fd : UpperHalfPlane.I ∈ ModularGroup.fd := by
  constructor <;> norm_num [UpperHalfPlane.I]

/-- Every actual integral modular translate of `I` has height at most one. -/
theorem modularIntegral_smul_I_im_le_one (g : SL(2, ℤ)) :
    (g • UpperHalfPlane.I).im ≤ 1 := by
  simpa [UpperHalfPlane.I] using
    modularClosedDomain_im_smul_le g UpperHalfPlane.I modular_I_mem_fd

/-- Height is controlled by distance in the actual trace orbit quotient. -/
theorem modularTrace_im_le_exp_quotient_dist (z : UpperHalfPlane) :
    z.im ≤ Real.exp (dist (modularTraceQuotientMk z)
      (modularTraceQuotientMk UpperHalfPlane.I)) := by
  obtain ⟨g, hg⟩ := modularTraceQuotient_dist_attained z UpperHalfPlane.I
  rw [hg]
  calc
    z.im ≤ (g • UpperHalfPlane.I).im * Real.exp (dist z (g • UpperHalfPlane.I)) :=
      UpperHalfPlane.im_le_im_mul_exp_dist z (g • UpperHalfPlane.I)
    _ ≤ 1 * Real.exp (dist z (g • UpperHalfPlane.I)) :=
      mul_le_mul_of_nonneg_right (modularIntegral_smul_I_im_le_one g.val)
        (Real.exp_pos _).le
    _ = Real.exp (dist z (g • UpperHalfPlane.I)) := one_mul _

/-- The logarithmic version uses the positive height of an upper-half-plane point. -/
theorem modularTrace_log_im_le_quotient_dist (z : UpperHalfPlane) :
    Real.log z.im ≤ dist (modularTraceQuotientMk z)
      (modularTraceQuotientMk UpperHalfPlane.I) :=
  (Real.log_le_iff_le_exp z.im_pos).mpr (modularTrace_im_le_exp_quotient_dist z)

/-- A quotient-distance bound gives a uniform height bound for every representative. -/
theorem modularTrace_im_le_exp_of_quotient_dist_le (z : UpperHalfPlane) (R : ℝ)
    (hR : dist (modularTraceQuotientMk z)
      (modularTraceQuotientMk UpperHalfPlane.I) ≤ R) :
    z.im ≤ Real.exp R :=
  (modularTrace_im_le_exp_quotient_dist z).trans (Real.exp_le_exp.mpr hR)


/-- The real-axis boundary cannot occur in the capped ambient closed cell. -/
theorem modularTruncatedCell_ambient_im_pos (c : ℂ)
    (hn : 1 ≤ Complex.normSq c) (hr : |c.re| ≤ (1 / 2 : ℝ))
    (hi : 0 ≤ c.im) : 0 < c.im := by
  by_contra h
  have him : c.im = 0 := le_antisymm (le_of_not_gt h) hi
  have hre := abs_le.mp hr
  have hprod := mul_nonneg
    (show 0 ≤ c.re + 1 / 2 by linarith [hre.1])
    (show 0 ≤ 1 / 2 - c.re by linarith [hre.2])
  rw [Complex.normSq_apply, him] at hn
  nlinarith

/-- A finite height cap makes the actual closed standard modular cell compact.
No sign assumption on the cap is needed; negative caps simply give the empty set. -/
theorem modularStandardCell_im_le_isCompact (M : ℝ) :
    IsCompact {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ z.im ≤ M} := by
  let A : Set ℂ := {c | 1 ≤ Complex.normSq c ∧ |c.re| ≤ (1 / 2 : ℝ) ∧
    0 ≤ c.im ∧ c.im ≤ M}
  have hAclosed : IsClosed A := by
    have h1 : IsClosed {c : ℂ | 1 ≤ Complex.normSq c} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h2 : IsClosed {c : ℂ | |c.re| ≤ (1 / 2 : ℝ)} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h3 : IsClosed {c : ℂ | 0 ≤ c.im} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have h4 : IsClosed {c : ℂ | c.im ≤ M} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter (h3.inter h4))
  have hAball : A ⊆ Metric.closedBall (0 : ℂ) (1 / 2 + |M|) := by
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖c‖ ≤ |c.re| + |c.im| := Complex.norm_le_abs_re_add_abs_im c
      _ = |c.re| + c.im := by rw [abs_of_nonneg hc.2.2.1]
      _ ≤ 1 / 2 + |M| := add_le_add hc.2.1 (hc.2.2.2.trans (le_abs_self M))
  have hAcompact : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) (1 / 2 + |M|)).of_isClosed_subset hAclosed hAball
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  convert hAcompact using 1
  ext c
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.1.1, hz.1.2, z.im_pos.le, hz.2⟩
  · intro hc
    have him : 0 < c.im := modularTruncatedCell_ambient_im_pos c hc.1 hc.2.1 hc.2.2.1
    let z : UpperHalfPlane := ⟨c, him⟩
    exact ⟨z, ⟨⟨hc.1, hc.2.1⟩, hc.2.2.2⟩, rfl⟩

/-- The same height cap is compact in the actual closed-cell subtype. -/
theorem modularStandardCell_subtype_im_le_isCompact (M : ℝ) :
    IsCompact {z : ModularGroup.fd | z.val.im ≤ M} := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert modularStandardCell_im_le_isCompact M using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hM⟩
    exact ⟨⟨z, hz⟩, hM, rfl⟩



/-- Six separate copies of the actual closed standard modular cell. -/
abbrev ModularTraceSixCellSpace := Fin 6 × ModularGroup.fd

/-- The actual six-cell restriction of the orbit projection. -/
def modularTraceSixCellMap (p : ModularTraceSixCellSpace) : ModularTraceQuotient :=
  modularTraceQuotientMk (ModularGroup.T ^ p.1.val • p.2.val)

theorem modularTraceSixCellMap_continuous : Continuous modularTraceSixCellMap := by
  apply continuous_prod_of_discrete_left.mpr
  intro r
  exact modularTraceQuotientMk_continuous.comp
    ((continuous_const_smul (ModularGroup.T ^ r.val)).comp continuous_subtype_val)

theorem modularTraceSixCellMap_surjective : Function.Surjective modularTraceSixCellMap := by
  intro x
  obtain ⟨r, z, hz, heq⟩ := modularTraceQuotient_fd_representative x
  exact ⟨⟨r, ⟨z, hz⟩⟩, heq⟩

/-- Compact sets downstairs have compact preimages in the disjoint six-cell domain. -/
theorem modularTraceSixCellMap_isCompact_preimage (K : Set ModularTraceQuotient)
    (hK : IsCompact K) : IsCompact (modularTraceSixCellMap ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall
    (modularTraceQuotientMk UpperHalfPlane.I)
  have hc : IsCompact ((univ : Set (Fin 6)) ×ˢ
      {z : ModularGroup.fd | z.val.im ≤ Real.exp R}) :=
    isCompact_univ.prod (modularStandardCell_subtype_im_le_isCompact (Real.exp R))
  apply hc.of_isClosed_subset
    (hK.isClosed.preimage modularTraceSixCellMap_continuous)
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  have hbound : dist (modularTraceSixCellMap p)
      (modularTraceQuotientMk UpperHalfPlane.I) ≤ R := hR hp
  have him := modularTrace_im_le_exp_of_quotient_dist_le
    (ModularGroup.T ^ p.1.val • p.2.val) R hbound
  have htrans : (ModularGroup.T ^ p.1.val • p.2.val).im = p.2.val.im := by
    simpa only [zpow_natCast] using
      ModularGroup.im_T_zpow_smul p.2.val (p.1.val : ℤ)
  simpa only [htrans] using him

/-- The actual map from the six separate closed cells is proper. -/
theorem modularTraceSixCellMap_isProperMap : IsProperMap modularTraceSixCellMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨modularTraceSixCellMap_continuous,
    fun {_} hK => modularTraceSixCellMap_isCompact_preimage _ hK⟩

/-- Properness and proved coverage make the six-cell restriction a quotient map. -/
theorem modularTraceSixCellMap_isQuotientMap :
    IsQuotientMap modularTraceSixCellMap := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨modularTraceSixCellMap_surjective, fun K => ?_⟩
  constructor
  · exact fun hK => hK.preimage modularTraceSixCellMap_continuous
  · intro hK
    have hclosed := modularTraceSixCellMap_isProperMap.isClosedMap
      (modularTraceSixCellMap ⁻¹' K) hK
    simpa only [image_preimage_eq K modularTraceSixCellMap_surjective] using hclosed

/-- The relation gluing the separate closed cells is the actual map kernel. -/
def modularTraceSixCellBoundarySetoid : Setoid ModularTraceSixCellSpace :=
  Setoid.ker modularTraceSixCellMap

/-- Its kernel is exactly the checked finite boundary relation, with the source
corner condition and correctly oriented source/target residue. -/
theorem modularTraceSixCellBoundarySetoid_iff (p q : ModularTraceSixCellSpace) :
    modularTraceSixCellBoundarySetoid p q ↔
    ∃ i : Fin 10,
      ModularClosedAdmissible (modularClosedReturnWordAt i) p.2.val ∧
      modularClosedReturnWordAt i • p.2.val = q.2.val ∧
      (q.1.val + (modularClosedReturnResidue i).val) % 6 = p.1.val :=
  modularTraceSixCell_closed_quotient_eq_iff_word_index p.1 q.1
    p.2.val q.2.val p.2.property q.2.property

/-- The topological quotient of the six closed standard cells by their exact
finite boundary relation. -/
abbrev ModularTraceSixCellGluing := Quotient modularTraceSixCellBoundarySetoid

/-- The actual glued-six-cell quotient is homeomorphic to the existing trace
orbit quotient with its original topology. This asserts no ideal-quadrilateral
or punctured-torus identification. -/
def modularTraceSixCellGluingHomeomorph :
    ModularTraceSixCellGluing ≃ₜ ModularTraceQuotient :=
  (show IsQuotientMap
    (⟨modularTraceSixCellMap, modularTraceSixCellMap_continuous⟩ :
      C(ModularTraceSixCellSpace, ModularTraceQuotient)) from
        modularTraceSixCellMap_isQuotientMap).homeomorph

/-- The homeomorphism is the actual projected-cell map on each representative. -/
@[simp] theorem modularTraceSixCellGluingHomeomorph_mk (p : ModularTraceSixCellSpace) :
    modularTraceSixCellGluingHomeomorph (Quotient.mk _ p) =
      modularTraceQuotientMk (ModularGroup.T ^ p.1.val • p.2.val) := rfl

end Markov
