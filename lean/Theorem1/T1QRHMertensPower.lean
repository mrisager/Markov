import T1RieszMertensGrowth
import T1RieszDesmoothing
import T1FinalScaleTransfer

/-! The paper's actual zero-free half-plane gives genuine power-saving
Mertens cancellation, hence the exact conditional part of Theorem 1. -/
noncomputable section
namespace Markov

theorem t1_mertens_power_of_riesz {σ K : ℝ} {k : ℕ} (hσ : 0 < σ)
    (hσ1 : σ < 1) (hK : 0 < K) (hk : 0 < k)
    (hR : ∀ x : ℝ, 1 ≤ x → |t1_rieszMertens k x| ≤ K*x^(σ+(k : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ t1_MertensPowerBound δ := by
  let β := (σ+(k : ℝ))/((k : ℝ)+1)
  let A := t1_differenceWeightNorm k*K*(1+(k : ℝ))^(σ+(k : ℝ))
  let B := t1_differenceBoundaryConstant k*((k : ℝ)+1)
  have hd : 0 < (k : ℝ)+1 := by positivity
  have hβ : 0 < β := div_pos (by positivity) hd
  have hβ1 : β < 1 := (div_lt_one₀ hd).2 (by linarith)
  have hβm : β*((k : ℝ)+1) = σ+(k : ℝ) := div_mul_cancel₀ _ hd.ne'
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [t1_differenceWeightNorm_nonneg k]
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [t1_differenceBoundaryConstant_nonneg k]
  refine ⟨1-β,sub_pos.mpr hβ1,A+B+1,by linarith,1,?_⟩
  intro n hn
  let x := (n : ℝ)
  have hx : 1 ≤ x := by
    change 1 ≤ (n : ℝ)
    exact_mod_cast hn
  have hx0 := zero_lt_one.trans_le hx
  let h := x^β
  have hh : 1 ≤ h := Real.one_le_rpow hx hβ.le
  have hhx : h ≤ x := by
    rw [← Real.rpow_one x]
    exact Real.rpow_le_rpow_of_exponent_le hx hβ1.le
  have hm := t1_mertens_desmoothing_bound hk hσ.le hK.le hR hx hh hhx
  have hpow : h^k = x^(β*(k : ℝ)) := by
    rw [Real.rpow_mul hx0.le,Real.rpow_natCast]
  have he : x^(σ+(k : ℝ))/h^k = x^β := by
    rw [hpow,← Real.rpow_sub hx0]
    congr 1
    linarith [hβm]
  have hM : t1_mertens x = (t1_mertensNat n : ℝ) := by
    simp only [t1_mertens,x,Nat.floor_natCast]
  rw [hM,he] at hm
  have hf : 1-(1-β) = β := by ring
  rw [hf]
  calc
    _ ≤ A*x^β+B*x^β := hm
    _ = (A+B)*x^β := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg hx0.le _)

theorem t1_QRH_implies_mertens_power (h : QuasiRiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ t1_MertensPowerBound δ := by
  obtain ⟨σ,k,K,hσ,hσ1,hk,hK,hR⟩ := t1_QRH_rieszMertens_bound h
  exact t1_mertens_power_of_riesz (by linarith) hσ1 hK hk hR

theorem t1_markovConditional_of_QRH (h : QuasiRiemannHypothesis) :
    ConditionalBound t1_markovLeadingCoefficient := by
  obtain ⟨δ,hδ,hM⟩ := t1_QRH_implies_mertens_power h
  exact t1_markovConditional_of_mertens_power δ hδ hM

end Markov
