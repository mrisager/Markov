import T1ZetaStripDisk

/-! Polynomial growth of the actual reciprocal zeta function on a
closed substrip of the actual zero-free half-plane. -/
noncomputable section
open Complex Set Metric
namespace Markov

theorem t1_reciprocalZeta_fixed_strip {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hzeta : ∀ s : ℂ, s ≠ 1 → 1-δ < s.re → riemannZeta s ≠ 0) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ s : ℂ, 1-δ/2 ≤ s.re → s.re ≤ 2 →
      ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^A := by
  obtain ⟨K,hK,hKbound⟩ := t1_poleRemovedZeta_reciprocal_line_two_bounded
  let B := 75*K+1
  let a := 16/δ
  have hB : 1 < B := by dsimp [B]; linarith
  have hB0 : 0 < B := by linarith
  have ha : 0 < a := div_pos (by norm_num) hδ
  refine ⟨6*K*B^a,2*a+1,by positivity,by linarith,?_⟩
  intro s hs hs'
  let z := t1_zetaDiskCenter s.im
  let w := s-z
  let r := 1+3*δ/4
  let u := 1+|s.im|
  let M := Real.log (B*u^2)
  let f := fun v => t1_poleRemovedZeta (z+v)
  have hu : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg s.im]
  have hu0 : 0 < u := by linarith
  have hu2 : 0 ≤ u^2-1 := by nlinarith
  have hBpow : 1 < B*u^2 := by
    linarith [mul_nonneg hB0.le hu2]
  have hM : 0 < M := Real.log_pos hBpow
  have hr : 0 < r := by dsimp [r]; linarith
  have hr2 : r ≤ 2 := by dsimp [r]; linarith
  have hwN : ‖w‖ = 2-s.re := by
    dsimp [w,z]
    rw [t1_zetaDiskCenter_distance,abs_of_nonpos (by linarith : s.re-2 ≤ 0)]
    ring
  have hw : w ∈ ball 0 r := mem_ball_zero_iff.mpr (by rw [hwN]; dsimp [r]; linarith)
  have hgap : δ/4 ≤ r-‖w‖ := by rw [hwN]; dsimp [r]; linarith
  have hgap0 : 0 < r-‖w‖ := by linarith
  have hw2 : ‖w‖ ≤ 2 := (mem_ball_zero_iff.mp hw).le.trans hr2
  have hf : DifferentiableOn ℂ f (ball 0 r) :=
    (t1_poleRemovedZeta_differentiable.comp
      ((differentiable_const (c := z)).add differentiable_id)).differentiableOn
  have hfn : ∀ v ∈ ball 0 r, f v ≠ 0 := fun v hv =>
    t1_poleRemovedZeta_ne_zero hzeta (t1_zetaDisk_realPart s.im δ hδ hv)
  have hf0 : ‖(f 0)⁻¹‖ ≤ K := by
    simpa only [f,add_zero] using hKbound z (t1_zetaDiskCenter_re s.im)
  have hBound : ∀ v ∈ ball 0 r, ‖f v/f 0‖ < Real.exp M := by
    intro v hv
    have hRe := t1_zetaDisk_realPart s.im δ hδ hv
    have hn := t1_zetaDisk_norm s.im ((mem_ball_zero_iff.mp hv).le.trans hr2)
    have hfN := t1_poleRemovedZeta_norm_le (z+v) (by linarith)
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z+v‖) hn 2
    have hfN' : ‖f v‖ ≤ 75*u^2 := by
      change ‖t1_poleRemovedZeta (z+v)‖ ≤ 75*u^2
      calc
        _ ≤ 3*(1+‖z+v‖)^2 := hfN
        _ ≤ 3*(5*u)^2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = _ := by ring
    change ‖f v/f 0‖ < Real.exp (Real.log (B*u^2))
    rw [div_eq_mul_inv,norm_mul,Real.exp_log (by positivity : 0 < B*u^2)]
    calc
      _ ≤ (75*u^2)*K := mul_le_mul hfN' hf0 (norm_nonneg _) (by positivity)
      _ < _ := by
        dsimp [B]
        nlinarith [sq_pos_of_pos hu0]
  have hExp : 2*M*‖w‖/(r-‖w‖) ≤ a*M := by
    apply (div_le_iff₀ hgap0).2
    calc
      _ ≤ 2*M*2 := mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = a*M*(δ/4) := by dsimp [a]; field_simp [hδ.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  have hR := t1_disk_reciprocal_bound hr hM hf hfn hBound hw
  have hPow : Real.exp (a*M) = B^a*u^(2*a) := by
    dsimp [M]
    rw [mul_comm a,← Real.rpow_def_of_pos (by positivity : 0 < B*u^2),Real.mul_rpow hB0.le (by positivity),
      ← Real.rpow_natCast_mul hu0.le]
    norm_num
  have hInv : ‖(t1_poleRemovedZeta s)⁻¹‖ ≤ K*(B^a*u^(2*a)) := by
    have he : z+w=s := by dsimp [w]; ring
    change ‖(t1_poleRemovedZeta (z+w))⁻¹‖ ≤ _ at hR
    rw [he] at hR
    exact hR.trans (mul_le_mul hf0 ((Real.exp_le_exp.mpr hExp).trans_eq hPow)
      (Real.exp_pos _).le hK.le)
  have hsN : ‖s-1‖ ≤ 6*u := by
    have hn := t1_zetaDisk_norm s.im hw2
    have he : z+w=s := by dsimp [w]; ring
    change 1+‖z+w‖ ≤ 5*u at hn
    rw [he] at hn
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith
  rw [t1_reciprocalZeta,div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (6*u)*(K*(B^a*u^(2*a))) := mul_le_mul hsN hInv (norm_nonneg _) (by positivity)
    _ = 6*K*B^a*u^(2*a+1) := by
      rw [Real.rpow_add hu0,Real.rpow_one]
      ring

end Markov
