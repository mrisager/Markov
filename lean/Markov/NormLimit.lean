import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-! Nondegeneracy of a planar seminorm from three strict triangle
inequalities. This is a construction ingredient, not an assertion that the
canonical trace lengths already extend to a seminorm. -/

noncomputable section

open Filter
open scoped Topology

namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A seminorm is unchanged by addition of an element of its kernel. -/
theorem seminorm_add_kernel (p : Seminorm ℝ E) (x y : E) (hy : p y = 0) :
    p (x + y) = p x := by
  have h := p.norm_sub_map_le_sub (x + y) x
  have hsub : x + y - x = y := by abel
  rw [hsub, hy, Real.norm_eq_abs] at h
  have hz : p (x + y) - p x = 0 := abs_nonpos_iff.mp h
  linarith

/-- Three strict triangles at a real basis rule out every nonzero kernel
vector. No separate lower bound or positivity hypothesis is needed. -/
theorem seminorm_kernel_trivial_of_strict_triangles
    (p : Seminorm ℝ E) (B : Module.Basis (Fin 2) ℝ E)
    (h01 : p (B 0 + B 1) < p (B 0) + p (B 1))
    (h0 : p (B 0) < p (B 0 + B 1) + p (B 1))
    (h1 : p (B 1) < p (B 0 + B 1) + p (B 0)) :
    ∀ x : E, p x = 0 → x = 0 := by
  intro x hx
  let s : ℝ := (B.repr x) 0
  let t : ℝ := (B.repr x) 1
  have hrep : x = s • B 0 + t • B 1 := by
    simpa only [s, t, Fin.sum_univ_two] using (B.sum_repr x).symm
  by_cases ht : t = 0
  · rw [hrep, ht, zero_smul, add_zero, map_smul_eq_mul, Real.norm_eq_abs] at hx
    by_cases hs : s = 0
    · rw [hrep, hs, ht, zero_smul, zero_smul, zero_add]
    · have hpa : p (B 0) = 0 :=
        (mul_eq_zero.mp hx).resolve_left (abs_ne_zero.mpr hs)
      have hsum : p (B 0 + B 1) = p (B 1) := by
        simpa only [add_comm] using seminorm_add_kernel p (B 1) (B 0) hpa
      linarith
  · let c : ℝ := -s / t
    have hk : p (t⁻¹ • x) = 0 := by rw [map_smul_eq_mul, hx, mul_zero]
    have hb : B 1 = c • B 0 + t⁻¹ • x := by
      rw [hrep, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
      dsimp [c]
      rw [div_eq_mul_inv]
      module
    have hpB : p (B 1) = |c| * p (B 0) := by
      rw [hb, seminorm_add_kernel p _ _ hk, map_smul_eq_mul, Real.norm_eq_abs]
    have hab : B 0 + B 1 = (1 + c) • B 0 + t⁻¹ • x := by
      rw [hb]
      module
    have hpAB : p (B 0 + B 1) = |1 + c| * p (B 0) := by
      rw [hab, seminorm_add_kernel p _ _ hk, map_smul_eq_mul, Real.norm_eq_abs]
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc] at hpB
      rw [abs_of_nonneg (show 0 ≤ 1 + c by linarith)] at hpAB
      nlinarith
    · rw [abs_of_nonpos hc] at hpB
      rcases le_total 0 (1 + c) with hc' | hc'
      · rw [abs_of_nonneg hc'] at hpAB
        nlinarith
      · rw [abs_of_nonpos hc'] at hpAB
        nlinarith

/-- Pointwise limits preserve the seminorm axioms. -/
def pointwiseLimitSeminorm (p : ℕ → Seminorm ℝ E) (f : E → ℝ)
    (hf : ∀ x : E, Tendsto (fun n : ℕ => p n x) atTop (𝓝 (f x))) : Seminorm ℝ E :=
  Seminorm.of f
    (fun x y => le_of_tendsto_of_tendsto' (hf (x + y)) ((hf x).add (hf y))
      (fun n => (p n).add_le' x y))
    (fun a x => by
      have h : Tendsto (fun n : ℕ => p n (a • x)) atTop (𝓝 (‖a‖ * f x)) := by
        simpa only [map_smul_eq_mul] using (hf x).const_mul ‖a‖
      exact tendsto_nhds_unique (hf (a • x)) h)

theorem pointwiseLimitSeminorm_apply (p : ℕ → Seminorm ℝ E) (f : E → ℝ)
    (hf : ∀ x : E, Tendsto (fun n : ℕ => p n x) atTop (𝓝 (f x))) (x : E) :
    pointwiseLimitSeminorm p f hf x = f x := rfl

/-- A decreasing sequence of seminorms converges pointwise to its real infimum. -/
theorem antitone_seminorm_tendsto_inf (p : ℕ → Seminorm ℝ E) (hp : Antitone p) (x : E) :
    Tendsto (fun n : ℕ => p n x) atTop (𝓝 (⨅ n : ℕ, p n x)) := by
  apply tendsto_atTop_ciInf (fun i j hij => hp hij x)
  refine ⟨0, ?_⟩
  rintro z ⟨n, rfl⟩
  exact apply_nonneg (p n) x

/-- The decreasing pointwise infimum is an actual seminorm. No positive
uniform lower bound is needed for this construction. -/
def antitoneInfSeminorm (p : ℕ → Seminorm ℝ E) (hp : Antitone p) : Seminorm ℝ E :=
  pointwiseLimitSeminorm p (fun x => ⨅ n : ℕ, p n x)
    (antitone_seminorm_tendsto_inf p hp)

theorem antitoneInfSeminorm_apply (p : ℕ → Seminorm ℝ E) (hp : Antitone p) (x : E) :
    antitoneInfSeminorm p hp x = ⨅ n : ℕ, p n x := rfl

/-- Eventual interpolation by the approximants passes exactly to the limit. -/
theorem antitoneInfSeminorm_eventual_value (p : ℕ → Seminorm ℝ E) (hp : Antitone p)
    (x : E) (a : ℝ) (hx : ∀ᶠ n : ℕ in atTop, p n x = a) :
    antitoneInfSeminorm p hp x = a := by
  have h : Tendsto (fun n : ℕ => p n x) atTop (𝓝 a) :=
    tendsto_const_nhds.congr' (hx.mono (fun _ hn => hn.symm))
  exact tendsto_nhds_unique (antitone_seminorm_tendsto_inf p hp x) h

/-- A decreasing fan-limit seminorm is nondegenerate once three prescribed
basis values satisfy the strict triangle inequalities. -/
theorem antitoneInfSeminorm_kernel_trivial
    (p : ℕ → Seminorm ℝ E) (hp : Antitone p) (B : Module.Basis (Fin 2) ℝ E)
    (a b c : ℝ)
    (h0 : ∀ᶠ n : ℕ in atTop, p n (B 0) = a)
    (h1 : ∀ᶠ n : ℕ in atTop, p n (B 1) = b)
    (h01 : ∀ᶠ n : ℕ in atTop, p n (B 0 + B 1) = c)
    (hc : c < a + b) (ha : a < c + b) (hb : b < c + a) :
    ∀ x : E, antitoneInfSeminorm p hp x = 0 → x = 0 := by
  apply seminorm_kernel_trivial_of_strict_triangles (antitoneInfSeminorm p hp) B
  · simpa only [antitoneInfSeminorm_eventual_value p hp (B 0) a h0,
      antitoneInfSeminorm_eventual_value p hp (B 1) b h1,
      antitoneInfSeminorm_eventual_value p hp (B 0 + B 1) c h01] using hc
  · simpa only [antitoneInfSeminorm_eventual_value p hp (B 0) a h0,
      antitoneInfSeminorm_eventual_value p hp (B 1) b h1,
      antitoneInfSeminorm_eventual_value p hp (B 0 + B 1) c h01] using ha
  · simpa only [antitoneInfSeminorm_eventual_value p hp (B 0) a h0,
      antitoneInfSeminorm_eventual_value p hp (B 1) b h1,
      antitoneInfSeminorm_eventual_value p hp (B 0 + B 1) c h01] using hb

/-- Package a nondegenerate seminorm as an actual additive group norm. The
normed group structure can then be obtained with `toNormedAddCommGroup`. -/
def groupNormOfTrivialKernel (p : Seminorm ℝ E)
    (hp : ∀ x : E, p x = 0 → x = 0) : AddGroupNorm E where
  toAddGroupSeminorm := p.toAddGroupSeminorm
  eq_zero_of_map_eq_zero' := hp

theorem groupNormOfTrivialKernel_apply (p : Seminorm ℝ E)
    (hp : ∀ x : E, p x = 0 → x = 0) (x : E) :
    groupNormOfTrivialKernel p hp x = p x := rfl

/-- The decreasing limit of the supplied fan seminorms is a group norm
when three eventual basis values satisfy the strict triangle inequalities. -/
def antitoneInfGroupNorm (p : ℕ → Seminorm ℝ E) (hp : Antitone p)
    (B : Module.Basis (Fin 2) ℝ E) (a b c : ℝ)
    (h0 : ∀ᶠ n : ℕ in atTop, p n (B 0) = a)
    (h1 : ∀ᶠ n : ℕ in atTop, p n (B 1) = b)
    (h01 : ∀ᶠ n : ℕ in atTop, p n (B 0 + B 1) = c)
    (hc : c < a + b) (ha : a < c + b) (hb : b < c + a) : AddGroupNorm E :=
  groupNormOfTrivialKernel (antitoneInfSeminorm p hp)
    (antitoneInfSeminorm_kernel_trivial p hp B a b c h0 h1 h01 hc ha hb)

theorem antitoneInfGroupNorm_apply (p : ℕ → Seminorm ℝ E) (hp : Antitone p)
    (B : Module.Basis (Fin 2) ℝ E) (a b c : ℝ)
    (h0 : ∀ᶠ n : ℕ in atTop, p n (B 0) = a)
    (h1 : ∀ᶠ n : ℕ in atTop, p n (B 1) = b)
    (h01 : ∀ᶠ n : ℕ in atTop, p n (B 0 + B 1) = c)
    (hc : c < a + b) (ha : a < c + b) (hb : b < c + a) (x : E) :
    antitoneInfGroupNorm p hp B a b c h0 h1 h01 hc ha hb x = ⨅ n : ℕ, p n x := rfl

end Markov
