import Markov.SupportDerivative
import Mathlib.Topology.Ultrafilter

/-! Limits of supporting functionals from one side of a rational ray.
For an arbitrary normed real plane, every choice of norming support on
`a + t • b` converges in operator norm to the support at `a` selected by
`b`, as `t` tends to zero from above. A basis makes the required
noncollinearity explicit; no trace or surface identification is needed. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A support at the displaced point dominates its secant slope at the
initial point. This inequality identifies the selected endpoint in a limit. -/
theorem normingSupport_secant_le (a b : E) (t : ℝ) (ht : 0 < t)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals (a + t • b)) :
    (‖a + t • b‖ - ‖a‖) / t ≤ f b := by
  have ha := normingFunctional_le_norm (a + t • b) a f hf
  have he := hf.2
  simp only [map_add, map_smul, smul_eq_mul] at he
  apply (div_le_iff₀ ht).mpr
  nlinarith

/-- Any choices of norming supports at points approaching the first basis
ray from the second basis direction converge to its selected support. The
topology on the strong dual is its operator-norm topology. -/
theorem normingSupport_tendsto_selectedSupport_of_tendsto
    (B : Module.Basis (Fin 2) ℝ E) {ι : Type*} {l : Filter ι}
    (t : ι → ℝ) (ht : Tendsto t l (𝓝[>] (0 : ℝ)))
    (f : ι → StrongDual ℝ E)
    (hf : ∀ᶠ i in l, f i ∈ normingFunctionals (B 0 + t i • B 1)) :
    Tendsto f l (𝓝 (selectedSupport B)) := by
  letI : FiniteDimensional ℝ E := Module.Finite.of_basis B
  apply (isCompact_closedBall (0 : StrongDual ℝ E) 1).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [hf] with i hi
    simpa using hi.1
  · intro g hg hcluster
    obtain ⟨U, hU, hfg⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
    have hsupport : ∀ᶠ i in (U : Filter ι),
        f i ∈ normingFunctionals (B 0 + t i • B 1) := hU hf
    have htright : Tendsto t (U : Filter ι) (𝓝[>] (0 : ℝ)) := ht.mono_left hU
    have htzero : Tendsto t (U : Filter ι) (𝓝 (0 : ℝ)) :=
      htright.mono_right nhdsWithin_le_nhds
    have hpos : ∀ᶠ i in (U : Filter ι), 0 < t i :=
      htright.eventually self_mem_nhdsWithin
    have hpoint : Tendsto (fun i => B 0 + t i • B 1) (U : Filter ι) (𝓝 (B 0)) := by
      have hconst0 : Tendsto (fun _ : ι => B 0) (U : Filter ι) (𝓝 (B 0)) :=
        tendsto_const_nhds
      have hconst1 : Tendsto (fun _ : ι => B 1) (U : Filter ι) (𝓝 (B 1)) :=
        tendsto_const_nhds
      simpa only [zero_smul, add_zero] using
        hconst0.add (htzero.smul hconst1)
    have heval_cont : Continuous (fun p : StrongDual ℝ E × E => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have heval : Tendsto (fun i => f i (B 0 + t i • B 1))
        (U : Filter ι) (𝓝 (g (B 0))) :=
      (heval_cont.tendsto (g, B 0)).comp (hfg.prodMk_nhds hpoint)
    have heq : (fun i => f i (B 0 + t i • B 1)) =ᶠ[U]
        (fun i => ‖B 0 + t i • B 1‖) := hsupport.mono fun _ hi => hi.2
    have hga : g (B 0) = ‖B 0‖ :=
      tendsto_nhds_unique heval (hpoint.norm.congr' heq.symm)
    have hgnorm : ‖g‖ ≤ 1 := by simpa using hg
    have hgnorming : g ∈ normingFunctionals (B 0) := ⟨hgnorm, hga⟩
    have hgb : selectedSupport B (B 1) ≤ g (B 1) := by
      apply le_of_tendsto_of_tendsto
        ((selectedSupport_directional_limit B).comp htright)
        (((ContinuousLinearMap.apply ℝ ℝ (B 1)).continuous.tendsto g).comp hfg)
      filter_upwards [hsupport, hpos] with i hi hti
      exact normingSupport_secant_le (B 0) (B 1) (t i) hti (f i) hi
    apply (exists_unique_selectedSupport B).unique ?_ (selectedSupport_spec B)
    refine ⟨hgnorming, ?_⟩
    intro q hq
    exact ((selectedSupport_spec B).2 q hq).trans hgb

/-- Full right-hand limiting statement, with an arbitrary norming support
chosen at each positive displacement. -/
theorem normingSupport_tendsto_selectedSupport
    (B : Module.Basis (Fin 2) ℝ E) (f : ℝ → StrongDual ℝ E)
    (hf : ∀ t : ℝ, 0 < t → f t ∈ normingFunctionals (B 0 + t • B 1)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (selectedSupport B)) := by
  apply normingSupport_tendsto_selectedSupport_of_tendsto B id tendsto_id f
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hf t ht

/-- Explicit operator-norm convergence of the difference of the supports. -/
theorem normingSupport_opNorm_sub_tendsto_zero
    (B : Module.Basis (Fin 2) ℝ E) (f : ℝ → StrongDual ℝ E)
    (hf : ∀ t : ℝ, 0 < t → f t ∈ normingFunctionals (B 0 + t • B 1)) :
    Tendsto (fun t => ‖f t - selectedSupport B‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hc : Tendsto (fun _ : ℝ => selectedSupport B) (𝓝[>] (0 : ℝ))
      (𝓝 (selectedSupport B)) := tendsto_const_nhds
  simpa only [sub_self, norm_zero] using
    ((normingSupport_tendsto_selectedSupport B f hf).sub hc).norm

/-- In particular, supports chosen independently along the inverse-integer
displacements converge; no continuity of the choices is required. -/
theorem normingSupport_inverse_nat_tendsto_selectedSupport
    (B : Module.Basis (Fin 2) ℝ E) (f : ℕ → StrongDual ℝ E)
    (hf : ∀ n : ℕ, f n ∈ normingFunctionals (B 0 + ((n : ℝ) + 1)⁻¹ • B 1)) :
    Tendsto f atTop (𝓝 (selectedSupport B)) := by
  apply normingSupport_tendsto_selectedSupport_of_tendsto B
    (fun n : ℕ => ((n : ℝ) + 1)⁻¹) ?_ f (Eventually.of_forall hf)
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_nhdsGT_zero.comp hn

/-- Integer directions with nonzero determinant give the same limit for
the actual selected functional used by the separation theorem. -/
theorem normingSupport_tendsto_selectedSupportAt
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (f : ℝ → StrongDual ℝ E)
    (hf : ∀ t : ℝ, 0 < t →
      f t ∈ normingFunctionals (intVector B u + t • intVector B v)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (selectedSupportAt B u v)) := by
  rw [selectedSupportAt, dif_pos hdet]
  apply normingSupport_tendsto_selectedSupport (intPairBasis B u v hdet) f
  simpa only [intPairBasis_zero, intPairBasis_one] using hf

end Markov
