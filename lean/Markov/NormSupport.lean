import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Supporting functionals for an arbitrary real normed plane. This builds
the existence and uniqueness underlying §3.1 for a given normed space; it
does not construct the McShane–Rivin norm or its trace-derivative formula. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normingFunctionals (a : E) : Set (StrongDual ℝ E) :=
  {f | ‖f‖ ≤ 1 ∧ f a = ‖a‖}

theorem normingFunctionals_nonempty (a : E) : (normingFunctionals a).Nonempty := by
  obtain ⟨f, hnorm, hval⟩ := exists_dual_vector'' ℝ a
  exact ⟨f, hnorm, hval⟩

theorem normingFunctionals_isClosed (a : E) : IsClosed (normingFunctionals a) := by
  have heval : Continuous (fun f : StrongDual ℝ E => f a) :=
    (ContinuousLinearMap.apply ℝ ℝ a).continuous
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_eq heval continuous_const)

theorem normingFunctionals_isCompact [FiniteDimensional ℝ E] (a : E) :
    IsCompact (normingFunctionals a) := by
  apply (isCompact_closedBall (0 : StrongDual ℝ E) 1).of_isClosed_subset
    (normingFunctionals_isClosed a)
  intro f hf
  simpa using hf.1

theorem normingFunctional_on_unitBall (a : E) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals a) (x : E) (hx : ‖x‖ ≤ 1) : f x ≤ 1 := by
  have hbound : |f x| ≤ ‖f‖ * ‖x‖ := by simpa using f.le_opNorm x
  have hmul := mul_le_mul hf.1 hx (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
  exact (le_abs_self (f x)).trans (hbound.trans (by simpa using hmul))

theorem normingFunctional_normalized_eq_one (a : E) (ha : a ≠ 0)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals a) :
    f (‖a‖⁻¹ • a) = 1 := by
  rw [map_smul, hf.2]
  change ‖a‖⁻¹ * ‖a‖ = 1
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)

def IsSelectedSupport (a b : E) (f : StrongDual ℝ E) : Prop :=
  f ∈ normingFunctionals a ∧ ∀ g ∈ normingFunctionals a, g b ≤ f b

/-- The supporting functional maximizing the second coordinate exists and
is unique, because the two basis vectors determine a linear functional. -/
theorem exists_unique_selectedSupport (B : Module.Basis (Fin 2) ℝ E) :
    ∃! f : StrongDual ℝ E, IsSelectedSupport (B 0) (B 1) f := by
  letI : FiniteDimensional ℝ E := Module.Finite.of_basis B
  have heval : Continuous (fun f : StrongDual ℝ E => f (B 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (B 1)).continuous
  obtain ⟨f, hf, hmax⟩ := (normingFunctionals_isCompact (B 0)).exists_isMaxOn
    (normingFunctionals_nonempty (B 0)) heval.continuousOn
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · intro g hg
    exact hmax hg
  · intro g hg
    have heq : g.toLinearMap = f.toLinearMap := by
      apply B.ext
      intro i
      fin_cases i
      · exact hg.1.2.trans hf.2.symm
      · exact le_antisymm (hmax hg.1) (hg.2 f hf)
    ext x
    exact LinearMap.congr_fun heq x

def selectedSupport (B : Module.Basis (Fin 2) ℝ E) : StrongDual ℝ E :=
  Classical.choose (exists_unique_selectedSupport B).exists

theorem selectedSupport_spec (B : Module.Basis (Fin 2) ℝ E) :
    IsSelectedSupport (B 0) (B 1) (selectedSupport B) :=
  Classical.choose_spec (exists_unique_selectedSupport B).exists

theorem selectedSupport_norm_eq_one (B : Module.Basis (Fin 2) ℝ E) :
    ‖selectedSupport B‖ = 1 := by
  have hs := selectedSupport_spec B
  have hp : 0 < ‖B 0‖ := norm_pos_iff.mpr (B.ne_zero 0)
  have he := (selectedSupport B).le_opNorm (B 0)
  rw [hs.1.2, norm_norm] at he
  exact le_antisymm hs.1.1 (by nlinarith)

end Markov
