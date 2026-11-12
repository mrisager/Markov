import Markov.CoveringLoopEndpoint
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected

/-! Integer winding for the literal covering ℝ → AddCircle 1.
The construction uses actual lifted endpoints and actual path homotopy classes.
It proves normalized positive winding and a genuine fundamental-group equivalence.
No punctured-torus marking, singular H1 or geometric holonomy claim is made. -/

noncomputable section
namespace Markov

abbrev NormalizedCircle := AddCircle (1 : ℝ)

def normalizedCircleCover : ℝ → NormalizedCircle := fun x => (x : NormalizedCircle)

theorem normalizedCircleCover_isCoveringMap : IsCoveringMap normalizedCircleCover :=
  AddCircle.isCoveringMap_coe 1

@[simp] theorem normalizedCircleCover_intCast (n : ℤ) :
    normalizedCircleCover (n : ℝ) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
  exact ⟨n, by simp⟩

abbrev NormalizedCircleFibre := normalizedCircleCover ⁻¹' {(0 : NormalizedCircle)}

def normalizedCircleIntegerFibre (n : ℤ) : NormalizedCircleFibre :=
  ⟨(n : ℝ), normalizedCircleCover_intCast n⟩

theorem normalizedCircleIntegerFibre_injective :
    Function.Injective normalizedCircleIntegerFibre := by
  intro n m h
  exact Int.cast_injective (congrArg Subtype.val h)

theorem normalizedCircleIntegerFibre_surjective :
    Function.Surjective normalizedCircleIntegerFibre := by
  intro e
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp e.property
  refine ⟨n, Subtype.ext ?_⟩
  simpa using hn

def normalizedCircleIntegerFibreEquiv : ℤ ≃ NormalizedCircleFibre :=
  Equiv.ofBijective normalizedCircleIntegerFibre
    ⟨normalizedCircleIntegerFibre_injective, normalizedCircleIntegerFibre_surjective⟩

def normalizedCircleWindingEquiv :
    Path.Homotopic.Quotient (0 : NormalizedCircle) 0 ≃ ℤ :=
  (coveringLoopEndpointEquiv normalizedCircleCover_isCoveringMap (0 : ℝ)).trans
    normalizedCircleIntegerFibreEquiv.symm

theorem normalizedCircleWindingEquiv_fibre
    (c : Path.Homotopic.Quotient (0 : NormalizedCircle) 0) :
    normalizedCircleIntegerFibreEquiv (normalizedCircleWindingEquiv c) =
      normalizedCircleCover_isCoveringMap.monodromy c ⟨0, rfl⟩ :=
  normalizedCircleIntegerFibreEquiv.apply_symm_apply _

@[simp] theorem normalizedCircleCover_add (x y : ℝ) :
    normalizedCircleCover (x + y) = normalizedCircleCover x + normalizedCircleCover y := rfl

def normalizedCircleFibreTranslate (n : ℤ) (e : NormalizedCircleFibre) :
    NormalizedCircleFibre :=
  ⟨(n : ℝ) + e.val, by
    change normalizedCircleCover ((n : ℝ) + e.val) = 0
    rw [normalizedCircleCover_add, normalizedCircleCover_intCast, zero_add]
    exact e.property⟩

theorem normalizedCircleIntegerFibreEquiv_add (n m : ℤ) :
    normalizedCircleIntegerFibreEquiv (n + m) =
      normalizedCircleFibreTranslate n (normalizedCircleIntegerFibreEquiv m) := by
  apply Subtype.ext
  exact Int.cast_add n m

/-- Actual path lifting commutes with translation by every integer period. -/
theorem normalizedCircleMonodromy_translate (n : ℤ)
    (c : Path.Homotopic.Quotient (0 : NormalizedCircle) 0)
    (e : NormalizedCircleFibre) :
    normalizedCircleCover_isCoveringMap.monodromy c (normalizedCircleFibreTranslate n e) =
      normalizedCircleFibreTranslate n
        (normalizedCircleCover_isCoveringMap.monodromy c e) := by
  obtain ⟨γ⟩ := c
  apply Subtype.ext
  let cov := normalizedCircleCover_isCoveringMap
  let L := cov.liftPath γ e.val (γ.source.trans e.property.symm)
  have hl : (fun t => (n : ℝ) + L t) =
      cov.liftPath γ ((n : ℝ) + e.val)
        (γ.source.trans (normalizedCircleFibreTranslate n e).property.symm) := by
    apply (cov.eq_liftPath_iff _).mpr
    refine ⟨by fun_prop, ?_, ?_⟩
    · funext t
      change normalizedCircleCover ((n : ℝ) + L t) = γ t
      rw [normalizedCircleCover_add, normalizedCircleCover_intCast, zero_add]
      exact congr_fun (cov.liftPath_lifts γ e.val _) t
    · change (n : ℝ) + L 0 = (n : ℝ) + e.val
      rw [show L 0 = e.val from cov.liftPath_zero γ e.val _]
  exact (congr_fun hl 1).symm

/-- Concatenating paths in their traversal order adds the lifted endpoint labels. -/
theorem normalizedCircleWindingEquiv_trans
    (c d : Path.Homotopic.Quotient (0 : NormalizedCircle) 0) :
    normalizedCircleWindingEquiv (c.trans d) =
      normalizedCircleWindingEquiv c + normalizedCircleWindingEquiv d := by
  apply normalizedCircleIntegerFibreEquiv.injective
  rw [normalizedCircleWindingEquiv_fibre,
    normalizedCircleCover_isCoveringMap.monodromy_trans_apply,
    normalizedCircleIntegerFibreEquiv_add]
  have hc : normalizedCircleCover_isCoveringMap.monodromy c ⟨0, rfl⟩ =
      normalizedCircleFibreTranslate (normalizedCircleWindingEquiv c) ⟨0, rfl⟩ := by
    rw [← normalizedCircleWindingEquiv_fibre]
    apply Subtype.ext
    simp [normalizedCircleIntegerFibreEquiv, normalizedCircleIntegerFibre,
      normalizedCircleFibreTranslate]
  rw [hc, normalizedCircleMonodromy_translate, ← normalizedCircleWindingEquiv_fibre]

@[simp] theorem normalizedCircleWindingEquiv_refl :
    normalizedCircleWindingEquiv (.refl (0 : NormalizedCircle)) = 0 := by
  apply normalizedCircleIntegerFibreEquiv.injective
  rw [normalizedCircleWindingEquiv_fibre,
    normalizedCircleCover_isCoveringMap.monodromy_refl]
  apply Subtype.ext
  simp [normalizedCircleIntegerFibreEquiv, normalizedCircleIntegerFibre]

/-- Winding is the integer endpoint of the genuine covering lift of a based loop. -/
def normalizedCircleWinding (γ : Path (0 : NormalizedCircle) 0) : ℤ :=
  normalizedCircleWindingEquiv (.mk γ)

/-- The winding label is exactly the terminal value of the actual lift starting at zero. -/
theorem normalizedCircleWinding_eq_liftPath_endpoint
    (γ : Path (0 : NormalizedCircle) 0) :
    (normalizedCircleWinding γ : ℝ) =
      normalizedCircleCover_isCoveringMap.liftPath γ 0 γ.source 1 := by
  exact congrArg Subtype.val (normalizedCircleWindingEquiv_fibre (.mk γ))

theorem normalizedCircleWinding_homotopic_iff
    (γ δ : Path (0 : NormalizedCircle) 0) :
    normalizedCircleWinding γ = normalizedCircleWinding δ ↔ γ.Homotopic δ := by
  exact normalizedCircleWindingEquiv.injective.eq_iff.trans Path.Homotopic.Quotient.eq

theorem normalizedCircleWinding_homotopic
    {γ δ : Path (0 : NormalizedCircle) 0} (h : γ.Homotopic δ) :
    normalizedCircleWinding γ = normalizedCircleWinding δ := by
  exact congrArg normalizedCircleWindingEquiv (Path.Homotopic.Quotient.eq.mpr h)

@[simp] theorem normalizedCircleWinding_refl :
    normalizedCircleWinding (Path.refl (0 : NormalizedCircle)) = 0 :=
  normalizedCircleWindingEquiv_refl

theorem normalizedCircleWinding_trans (γ δ : Path (0 : NormalizedCircle) 0) :
    normalizedCircleWinding (γ.trans δ) =
      normalizedCircleWinding γ + normalizedCircleWinding δ :=
  normalizedCircleWindingEquiv_trans (.mk γ) (.mk δ)

/-- The library fundamental-group multiplication reverses traversal order.
Since integer addition is commutative, the positive lifted endpoint labels give
an actual group equivalence without negating their orientation. -/
def normalizedCircleFundamentalGroupEquiv :
    FundamentalGroup NormalizedCircle 0 ≃* Multiplicative ℤ where
  toEquiv := normalizedCircleWindingEquiv.trans Multiplicative.ofAdd
  map_mul' c d := by
    change normalizedCircleWindingEquiv (d.toPath.trans c.toPath) =
      normalizedCircleWindingEquiv c.toPath + normalizedCircleWindingEquiv d.toPath
    rw [normalizedCircleWindingEquiv_trans, add_comm]

/-- The integer-labelled circle loop is the literal projection of the segment [0,n]. -/
def normalizedCircleIntegerLoop (n : ℤ) : Path (0 : NormalizedCircle) 0 :=
  ((Path.segment (0 : ℝ) (n : ℝ)).map
    normalizedCircleCover_isCoveringMap.continuous).cast
      rfl (normalizedCircleCover_intCast n).symm

@[simp] theorem normalizedCircleIntegerLoop_apply (n : ℤ) (t : unitInterval) :
    normalizedCircleIntegerLoop n t = (((t : ℝ) * (n : ℝ) : ℝ) : NormalizedCircle) := by
  simp [normalizedCircleIntegerLoop, Path.segment_apply,
    AffineMap.lineMap_apply_module, normalizedCircleCover]

@[simp] theorem normalizedCircleWinding_integerLoop (n : ℤ) :
    normalizedCircleWinding (normalizedCircleIntegerLoop n) = n := by
  apply normalizedCircleIntegerFibreEquiv.injective
  rw [normalizedCircleWinding, normalizedCircleWindingEquiv_fibre]
  exact coveringLoopEndpoint_projectedPath normalizedCircleCover_isCoveringMap
    (Path.segment (0 : ℝ) (n : ℝ)) (normalizedCircleCover_intCast n)

theorem normalizedCircleIntegerLoop_homotopic_refl_iff (n : ℤ) :
    (normalizedCircleIntegerLoop n).Homotopic (Path.refl (0 : NormalizedCircle)) ↔ n = 0 := by
  rw [← normalizedCircleWinding_homotopic_iff,
    normalizedCircleWinding_integerLoop, normalizedCircleWinding_refl]

/-- The positive once-around circle loop, literally the projection of [0,1]. -/
def normalizedCircleStandardLoop : Path (0 : NormalizedCircle) 0 :=
  ((Path.segment (0 : ℝ) 1).map normalizedCircleCover_isCoveringMap.continuous).cast
    rfl (AddCircle.coe_period (1 : ℝ)).symm

@[simp] theorem normalizedCircleStandardLoop_apply (t : unitInterval) :
    normalizedCircleStandardLoop t = ((t : ℝ) : NormalizedCircle) := by
  simp [normalizedCircleStandardLoop, Path.segment_apply,
    AffineMap.lineMap_apply_module, normalizedCircleCover]

@[simp] theorem normalizedCircleWinding_standardLoop :
    normalizedCircleWinding normalizedCircleStandardLoop = 1 := by
  apply normalizedCircleIntegerFibreEquiv.injective
  rw [normalizedCircleWinding, normalizedCircleWindingEquiv_fibre]
  simpa [coveringLoopEndpoint, normalizedCircleStandardLoop,
    normalizedCircleIntegerFibreEquiv, normalizedCircleIntegerFibre] using
      coveringLoopEndpoint_projectedPath normalizedCircleCover_isCoveringMap
        (Path.segment (0 : ℝ) 1) (AddCircle.coe_period (1 : ℝ))

@[simp] theorem normalizedCircleFundamentalGroupEquiv_standardLoop :
    normalizedCircleFundamentalGroupEquiv
      (FundamentalGroup.fromPath (.mk normalizedCircleStandardLoop)) =
        Multiplicative.ofAdd (1 : ℤ) :=
  normalizedCircleWinding_standardLoop

/-- The explicit positive circle loop is not actually path homotopic to the constant loop. -/
theorem normalizedCircleStandardLoop_not_homotopic_refl :
    ¬ normalizedCircleStandardLoop.Homotopic (Path.refl (0 : NormalizedCircle)) := by
  intro h
  have hw := normalizedCircleWinding_homotopic h
  rw [normalizedCircleWinding_standardLoop, normalizedCircleWinding_refl] at hw
  exact one_ne_zero hw

end Markov
