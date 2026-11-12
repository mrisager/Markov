import T1VKWeight
import T1MertensEnvelope

/-! The unconditional number-theoretic input stated for the actual Möbius
sum, and its elementary uniform-envelope consequence. -/
noncomputable section
namespace Markov

def t1_MertensVKBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(t1_mertensNat n : ℝ)| ≤ C*(n : ℝ)*Real.exp (-c*t1_vkWeight n)

theorem t1_mertens_vk_implies_envelope (hM : t1_MertensVKBound) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      t1_mertensEnvelope D ≤ C*Real.exp (-c*t1_vkWeight D) := by
  obtain ⟨C,c,hC,hc,N,hbound⟩ := hM
  let E := Real.exp (Real.exp 1)
  refine ⟨C,c,hC,hc,max N ⌈E⌉₊,?_⟩
  intro D hD
  have hED : E ≤ (D : ℝ) := (Nat.le_ceil E).trans (by exact_mod_cast (show ⌈E⌉₊ ≤ D by omega))
  apply t1_mertensEnvelope_le_of_uniform_bound D (C*Real.exp (-c*t1_vkWeight D))
    (by positivity)
  intro n hn
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast hn
  have hweight := t1_vkWeight_monotone hED (hED.trans hDn) hDn
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hweight (neg_nonpos.mpr hc.le))
  calc
    _ ≤ C*(n : ℝ)*Real.exp (-c*t1_vkWeight n) := hbound n (by omega)
    _ ≤ C*(n : ℝ)*Real.exp (-c*t1_vkWeight D) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end Markov
