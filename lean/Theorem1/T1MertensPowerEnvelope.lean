import T1MertensEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Elementary equivalence between a power saving for the actual Mertens
sum and the corresponding actual supremum envelope. The number-theoretic
power-saving premise is explicit and is not proved in this module. -/
noncomputable section
namespace Markov

def t1_MertensPowerBound (δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(t1_mertensNat n : ℝ)| ≤ C*(n : ℝ)^(1-δ)

def t1_MertensEnvelopePowerBound (δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    t1_mertensEnvelope n ≤ C*(n : ℝ)^(-δ)

theorem t1_mertens_power_implies_envelope (δ : ℝ) (hδ : 0 < δ)
    (hM : t1_MertensPowerBound δ) : t1_MertensEnvelopePowerBound δ := by
  obtain ⟨C,hC,N,hbound⟩ := hM
  refine ⟨C,hC,max N 1,?_⟩
  intro D hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  apply t1_mertensEnvelope_le_of_uniform_bound D (C*(D : ℝ)^(-δ)) (by positivity)
  intro n hDn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hb := hbound n (by omega)
  rw [show 1-δ = 1+(-δ) by ring,Real.rpow_add hnpos,Real.rpow_one] at hb
  have hpow := Real.rpow_le_rpow_of_nonpos hDpos hnD (neg_nonpos.mpr hδ.le)
  calc
    _ ≤ C*((n : ℝ)*(n : ℝ)^(-δ)) := hb
    _ ≤ C*((n : ℝ)*(D : ℝ)^(-δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hnpos.le) hC.le
    _ = _ := by ring

theorem t1_envelope_power_implies_mertens (δ : ℝ)
    (hM : t1_MertensEnvelopePowerBound δ) : t1_MertensPowerBound δ := by
  obtain ⟨C,hC,N,hbound⟩ := hM
  refine ⟨C,hC,max N 1,?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ t1_mertensEnvelope n*n := t1_mertensEnvelope_dominates n n le_rfl
    _ ≤ (C*(n : ℝ)^(-δ))*n :=
      mul_le_mul_of_nonneg_right (hbound n (by omega)) hnpos.le
    _ = C*(n : ℝ)^(1-δ) := by
      rw [show 1-δ = 1+(-δ) by ring,Real.rpow_add hnpos,Real.rpow_one]
      ring

theorem t1_mertens_power_iff_envelope (δ : ℝ) (hδ : 0 < δ) :
    t1_MertensPowerBound δ ↔ t1_MertensEnvelopePowerBound δ :=
  ⟨t1_mertens_power_implies_envelope δ hδ,t1_envelope_power_implies_mertens δ⟩

end Markov
