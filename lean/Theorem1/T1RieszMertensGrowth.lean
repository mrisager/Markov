import T1RieszMertensContour
import T1QRHStrip

/-! The shifted integral bounds the actual higher-order Riesz mean by
x^(σ+k), with σ strictly below one under the paper's QRH. -/
noncomputable section
open Complex Set MeasureTheory Filter
namespace Markov

theorem t1_rieszMertens_bound_of_strip {σ C A : ℝ}
    (hσ : (1 : ℝ)/2 ≤ σ) (hσ2 : σ ≤ 2) (hC : 0 < C)
    {k : ℕ} (hk : 0 < k) (hAk : A < (k : ℝ))
    (hF : DifferentiableOn ℂ t1_reciprocalZeta {s : ℂ | s.re ∈ Icc σ 2})
    (hB : ∀ s : ℂ, s.re ∈ Icc σ 2 → ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^A) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → |t1_rieszMertens k x| ≤ K*x^(σ+(k : ℝ)) := by
  let p := A-((k : ℝ)+1)
  let g := fun t : ℝ => (1+|t|)^p
  let G := ∫ t : ℝ, g t
  let B := C*(3 : ℝ)^(k+1)*G/(2*Real.pi)
  have hG : 0 ≤ G := integral_nonneg (fun _ => by dsimp [g]; positivity)
  have hπ : 0 < 2*Real.pi := by positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+1,by linarith,?_⟩
  intro x hx
  have hx0 := zero_lt_one.trans_le hx
  have hg : Integrable g := t1_verticalPower_integrable p (by dsimp [p]; linarith)
  let F := fun t : ℝ => t1_rieszIntegrand k x t1_reciprocalZeta (t1_verticalPoint σ t)
  have hI : ‖∫ t : ℝ, F t‖ ≤ (x^σ*C*(3 : ℝ)^(k+1))*G := by
    have h := norm_integral_le_of_norm_le (f := F) (hg.const_mul (x^σ*C*(3 : ℝ)^(k+1))) ?_
    · simpa only [integral_const_mul] using h
    · filter_upwards with t
      have hRe := t1_verticalPoint_re σ t
      have hs : (t1_verticalPoint σ t).re ∈ Icc σ 2 := by rw [hRe]; exact ⟨le_rfl,hσ2⟩
      simpa only [F,g,p,hRe,t1_verticalPoint_im] using
        t1_rieszIntegrand_norm_le hx0 hC.le (hσ.trans hs.1) (hB _ hs) (k := k)
  rw [← Real.norm_eq_abs,← Complex.norm_real,
    t1_rieszMertens_integral_on_strip hσ hσ2 hk hx hC.le hAk hF hB]
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx0,abs_of_pos (show (0 : ℝ)<2 by norm_num),abs_of_pos Real.pi_pos]
  change x^k/(2*Real.pi)*‖∫ t : ℝ, F t‖ ≤ (B+1)*x^(σ+(k : ℝ))
  calc
    _ ≤ x^k/(2*Real.pi)*((x^σ*C*(3 : ℝ)^(k+1))*G) :=
      mul_le_mul_of_nonneg_left hI (div_nonneg (pow_nonneg hx0.le _) hπ.le)
    _ = B*x^(σ+(k : ℝ)) := by
      rw [Real.rpow_add hx0,Real.rpow_natCast]
      dsimp [B]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

theorem t1_QRH_rieszMertens_bound (h : QuasiRiemannHypothesis) :
    ∃ (σ : ℝ) (k : ℕ) (K : ℝ), (1 : ℝ)/2 ≤ σ ∧ σ < 1 ∧ 0 < k ∧ 0 < K ∧
      ∀ x : ℝ, 1 ≤ x → |t1_rieszMertens k x| ≤ K*x^(σ+(k : ℝ)) := by
  obtain ⟨σ,C,A,hσ,hσ1,hC,hA,hF,hB⟩ := t1_QRH_reciprocalZeta_strip h
  let k := ⌊A⌋₊+1
  have hk : 0 < k := Nat.succ_pos _
  have hAk : A < (k : ℝ) := by
    simpa only [k,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one A
  obtain ⟨K,hK,hbound⟩ := t1_rieszMertens_bound_of_strip hσ (by linarith) hC hk hAk hF hB
  exact ⟨σ,k,K,hσ,hσ1,hk,hK,hbound⟩

end Markov
