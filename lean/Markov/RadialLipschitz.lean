import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Quantitative regularity of a normalized radial section of a normed
plane. Target maps permit measuring the same section in a separate norm,
including Euclidean coordinates. No Farey arc estimate is asserted here. -/

noncomputable section
open scoped NNReal ENNReal
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalizing vectors is Lipschitz wherever their norms have a positive
lower bound. -/
theorem normalize_sub_le_of_norm_lower_bound (x y : E) (c : ℝ) (hc : 0 < c)
    (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / c) * ‖x - y‖ := by
  have hxp : 0 < ‖x‖ := hc.trans_le hx
  have hyp : 0 < ‖y‖ := hc.trans_le hy
  have hcoeff : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = ‖x‖⁻¹ * |‖y‖ - ‖x‖| := by
    have he : ‖x‖⁻¹ - ‖y‖⁻¹ = ‖x‖⁻¹ * (‖y‖ - ‖x‖) * ‖y‖⁻¹ := by
      field_simp
    rw [he, abs_mul, abs_mul, abs_inv, abs_inv, abs_norm, abs_norm]
    field_simp
  have hbase : ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      (2 / ‖x‖) * ‖x - y‖ := by
    calc
      ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
          ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
        congr 1
        simp only [NormedSpace.normalize]
        module
      _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
      _ = ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * |‖y‖ - ‖x‖| := by
        simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hcoeff]
      _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le y x
        rw [norm_sub_rev] at h
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hxp.le))
      _ = (2 / ‖x‖) * ‖x - y‖ := by ring
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_div_iff₀ hxp hc).mpr
  nlinarith

/-- The radial section associated with the affine line through two basis
vectors. -/
def radialBasisSection (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) : E :=
  NormedSpace.normalize (B 0 + t • B 1)

def radialSectionLipschitzConstant (B : Module.Basis (Fin 2) ℝ E) (c : ℝ)
    (hc : 0 < c) : ℝ≥0 := ⟨(2 / c) * ‖B 1‖, by positivity⟩

theorem radialBasisSection_dist_le (B : Module.Basis (Fin 2) ℝ E) (s t c : ℝ)
    (hc : 0 < c) (hs : c ≤ ‖B 0 + s • B 1‖) (ht : c ≤ ‖B 0 + t • B 1‖) :
    dist (radialBasisSection B s) (radialBasisSection B t) ≤
      ((2 / c) * ‖B 1‖) * dist s t := by
  rw [dist_eq_norm]
  apply (normalize_sub_le_of_norm_lower_bound _ _ c hc hs ht).trans_eq
  have he : B 0 + s • B 1 - (B 0 + t • B 1) = (s - t) • B 1 := by module
  rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq]
  ring

/-- A positive denominator bound gives an explicit Lipschitz constant on
any parameter set, in particular the unit interval. -/
theorem radialBasisSection_lipschitzOnWith (B : Module.Basis (Fin 2) ℝ E)
    (S : Set ℝ) (c : ℝ) (hc : 0 < c) (hden : ∀ t ∈ S, c ≤ ‖B 0 + t • B 1‖) :
    LipschitzOnWith (radialSectionLipschitzConstant B c hc) (radialBasisSection B) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  exact radialBasisSection_dist_le B s t c hc (hden s hs) (hden t ht)

theorem basis_affineLine_ne_zero (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    B 0 + t • B 1 ≠ 0 := by
  intro he
  have hh := congrArg (B.coord 0) he
  simp [Module.Basis.coord_apply, Module.Basis.repr_self] at hh

/-- The normalized basis section lies on the unit sphere. -/
@[simp] theorem norm_radialBasisSection (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    ‖radialBasisSection B t‖ = 1 :=
  NormedSpace.norm_normalize (basis_affineLine_ne_zero B t)

/-- Compactness and basis independence supply a positive denominator bound;
no geometric identification of the norm is required. -/
theorem radialBasisSection_exists_norm_lower_bound (B : Module.Basis (Fin 2) ℝ E) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ ‖B 0 + t • B 1‖ := by
  have hcont : Continuous (fun t : ℝ => ‖B 0 + t • B 1‖) :=
    (continuous_const.add (continuous_id.smul continuous_const)).norm
  exact isCompact_Icc.exists_forall_le' hcont.continuousOn
    (fun t _ => norm_pos_iff.mpr (basis_affineLine_ne_zero B t))

theorem radialBasisSection_exists_lipschitzOnWith (B : Module.Basis (Fin 2) ℝ E) :
    ∃ K : ℝ≥0, LipschitzOnWith K (radialBasisSection B) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨c, hc, hden⟩ := radialBasisSection_exists_norm_lower_bound B
  exact ⟨radialSectionLipschitzConstant B c hc,
    radialBasisSection_lipschitzOnWith B _ c hc hden⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear target changes the distance constant by its operator
norm. Taking a Euclidean coordinate map measures Euclidean arc length. -/
theorem radialBasisSection_target_lipschitzOnWith (B : Module.Basis (Fin 2) ℝ E)
    (T : E →L[ℝ] F) (S : Set ℝ) (c : ℝ) (hc : 0 < c)
    (hden : ∀ t ∈ S, c ≤ ‖B 0 + t • B 1‖) :
    LipschitzOnWith (‖T‖₊ * radialSectionLipschitzConstant B c hc)
      (T ∘ radialBasisSection B) S :=
  T.lipschitz.comp_lipschitzOnWith (radialBasisSection_lipschitzOnWith B S c hc hden)

omit [NormedSpace ℝ F] in
/-- The metric variation of a Lipschitz curve on an interval is at most its
Lipschitz constant times the parameter length. -/
theorem lipschitzOnWith_eVariationOn_Icc_le {f : ℝ → F} {K : ℝ≥0} (a b : ℝ)
    (hf : LipschitzOnWith K f (Set.Icc a b)) :
    eVariationOn f (Set.Icc a b) ≤ K * ENNReal.ofReal (b - a) := by
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
    simpa only [Set.univ_inter, id_eq] using
      (monotoneOn_id (s := Set.univ)).eVariationOn_le (Set.mem_univ a) (Set.mem_univ b)
  apply (hf.comp_eVariationOn_le (Set.mapsTo_id _)).trans
  gcongr

/-- An explicit arc-variation bound in any continuous linear target norm. -/
theorem radialBasisSection_target_eVariationOn_le (B : Module.Basis (Fin 2) ℝ E)
    (T : E →L[ℝ] F) (a b c : ℝ) (hc : 0 < c)
    (hden : ∀ t ∈ Set.Icc a b, c ≤ ‖B 0 + t • B 1‖) :
    eVariationOn (T ∘ radialBasisSection B) (Set.Icc a b) ≤
      (‖T‖₊ * radialSectionLipschitzConstant B c hc) * ENNReal.ofReal (b - a) :=
  lipschitzOnWith_eVariationOn_Icc_le a b
    (radialBasisSection_target_lipschitzOnWith B T _ c hc hden)

theorem radialBasisSection_target_boundedVariationOn (B : Module.Basis (Fin 2) ℝ E)
    (T : E →L[ℝ] F) (a b c : ℝ) (hc : 0 < c)
    (hden : ∀ t ∈ Set.Icc a b, c ≤ ‖B 0 + t • B 1‖) :
    BoundedVariationOn (T ∘ radialBasisSection B) (Set.Icc a b) := by
  exact ne_top_of_le_ne_top (by finiteness)
    (radialBasisSection_target_eVariationOn_le B T a b c hc hden)

end Markov
