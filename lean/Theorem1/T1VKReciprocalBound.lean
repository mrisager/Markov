import T1VKReciprocalCenter
import T1DiskReciprocalBound

/-! The actual moving zero-free region implies a uniform polynomial
reciprocal bound, using disks scaled by the width rather than fixed disks. -/
noncomputable section
open Complex Set Metric
namespace Markov

theorem t1_vkReciprocalZeta_near_line {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, t1_vkContourLeft c s.im ≤ s.re →
      s.re ≤ 1+t1_vkDiskWidth c s.im/4 → ‖t1_reciprocalZeta s‖ ≤ K*(1+|s.im|)^27 := by
  let L := t1_vkInverseWidthConstant c
  let K₀ := (2+4*L)*(4*L)
  let B := 48*K₀+1
  have hL := t1_vkInverseWidthConstant_pos hc
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hB : 1 < B := by dsimp [B]; linarith
  have hB0 : 0 < B := by linarith
  refine ⟨4*K₀*B^6,by positivity,?_⟩
  intro s hs hs'
  let t := s.im
  let d := t1_vkDiskWidth c t
  let z := t1_vkDiskCenter c t
  let w := s-z
  let u := 1+|t|
  let M := Real.log (B*u^4)
  let f := fun v => t1_poleRemovedZeta (z+v)
  have hu : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu0 : 0 < u := by linarith
  have hu4 : 1 ≤ u^4 := one_le_pow₀ hu
  have hBu : 1 < B*u^4 := hB.trans_le (le_mul_of_one_le_right hB0.le hu4)
  have hM : 0 < M := Real.log_pos hBu
  have hd : 0 < d := t1_vkDiskWidth_pos hc t
  have hd' : d ≤ c := t1_vkDiskWidth_le hc.le t
  have heval := t1_vkDisk_evaluation hc s hs hs'
  have hwN : ‖w‖ ≤ 3*d/8 := heval.1
  have hw : w ∈ ball 0 (d/2) := heval.2
  have hgap : d/8 ≤ d/2-‖w‖ := by linarith
  have hgap0 : 0 < d/2-‖w‖ := by linarith
  have hf : DifferentiableOn ℂ f (ball 0 (d/2)) :=
    (t1_poleRemovedZeta_differentiable.comp
      ((differentiable_const (c := z)).add differentiable_id)).differentiableOn
  have hfn : ∀ v ∈ ball 0 (d/2), f v ≠ 0 := fun v hv =>
    hZ _ (t1_vkDisk_inside_region hc hc' t hv)
  have hf0 : ‖(f 0)⁻¹‖ ≤ K₀*u^2 := by
    simpa only [f,add_zero] using t1_vkPoleRemovedZeta_inverse_center hc t
  have hfB : ∀ v ∈ ball 0 (d/2), ‖f v/f 0‖ < Real.exp M := by
    intro v hv
    have hvN := mem_ball_zero_iff.mp hv
    have hn := t1_vkDisk_norm_le hc hc' t (by linarith : ‖v‖ ≤ 1)
    have hRe := t1_vkDisk_inside_region hc hc' t hv
    have hW := t1_vkHeightWidth_le hc.le (z+v).im
    change 1-t1_vkHeightWidth c (z+v).im ≤ (z+v).re at hRe
    have hZnorm := t1_poleRemovedZeta_norm_le (z+v) (by linarith)
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z+v‖) hn 2
    have hb : ‖f v‖ ≤ 48*u^2 := calc
      _ ≤ 3*(1+‖z+v‖)^2 := hZnorm
      _ ≤ 3*(4*u)^2 := mul_le_mul_of_nonneg_left hsquare (by norm_num)
      _ = _ := by ring
    change ‖f v/f 0‖ < Real.exp (Real.log (B*u^4))
    rw [div_eq_mul_inv,norm_mul,Real.exp_log (by positivity : 0 < B*u^4)]
    calc
      _ ≤ (48*u^2)*(K₀*u^2) := mul_le_mul hb hf0 (norm_nonneg _) (by positivity)
      _ = (48*K₀)*u^4 := by ring
      _ < _ := mul_lt_mul_of_pos_right (by dsimp [B]; linarith) (by positivity)
  have hExp : 2*M*‖w‖/(d/2-‖w‖) ≤ 6*M := by
    apply (div_le_iff₀ hgap0).2
    calc
      _ ≤ 2*M*(3*d/8) := mul_le_mul_of_nonneg_left hwN (by positivity)
      _ = 6*M*(d/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  have hPow : Real.exp (6*M) = B^6*u^24 := by
    dsimp [M]
    have hlog : Real.log ((B*u^4)^6) = 6*Real.log (B*u^4) := by
      simpa only [Nat.cast_ofNat] using Real.log_pow (B*u^4) 6
    rw [← hlog,Real.exp_log (by positivity),mul_pow,← pow_mul]
  have hR := t1_disk_reciprocal_bound (by positivity : 0 < d/2) hM hf hfn hfB hw
  have he : z+w=s := by dsimp [w]; ring
  have hInv : ‖(t1_poleRemovedZeta s)⁻¹‖ ≤ (K₀*u^2)*(B^6*u^24) := by
    change ‖(t1_poleRemovedZeta (z+w))⁻¹‖ ≤ _ at hR
    rw [he] at hR
    exact hR.trans (mul_le_mul hf0 ((Real.exp_le_exp.mpr hExp).trans_eq hPow)
      (Real.exp_pos _).le (by positivity))
  have hN : ‖s-1‖ ≤ 4*u := by
    have hn := t1_vkDisk_norm_le hc hc' t (by linarith : ‖w‖ ≤ 1)
    change 1+‖z+w‖ ≤ 4*u at hn
    rw [he] at hn
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith
  rw [t1_reciprocalZeta,div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (4*u)*((K₀*u^2)*(B^6*u^24)) := mul_le_mul hN hInv (norm_nonneg _) (by positivity)
    _ = 4*K₀*B^6*u^27 := by ring

theorem t1_vkReciprocalZeta_moving_region {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, t1_vkContourLeft c s.im ≤ s.re →
      ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^27 := by
  obtain ⟨K,hK,hnear⟩ := t1_vkReciprocalZeta_near_line hc hc' hZ
  let L := 2+4*t1_vkInverseWidthConstant c
  have hL : 0 < L := by dsimp [L]; positivity [t1_vkInverseWidthConstant_pos hc]
  refine ⟨max K L,hK.trans_le (le_max_left _ _),?_⟩
  intro s hs
  by_cases hr : s.re ≤ 1+t1_vkDiskWidth c s.im/4
  · exact (hnear s hs hr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hright := t1_vkReciprocalZeta_right hc (le_of_lt (not_le.mp hr))
    have hu : 1 ≤ 1+|s.im| := le_add_of_nonneg_right (abs_nonneg _)
    have hp : 1+|s.im| ≤ (1+|s.im|)^27 := by
      nth_rw 1 [← pow_one (1+|s.im|)]
      exact pow_le_pow_right₀ hu (by norm_num)
    exact hright.trans (mul_le_mul (le_max_right K L) hp (by positivity) (hL.le.trans (le_max_right K L)))

end Markov
