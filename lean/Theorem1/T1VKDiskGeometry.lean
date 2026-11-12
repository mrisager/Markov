import T1VKRegion

/-! Disks whose radius follows the actual height-dependent width.
The evaluation point stays a fixed fraction of the radius from the edge. -/
noncomputable section
open Complex Metric Set
namespace Markov

def t1_vkDiskWidth (c t : ℝ) : ℝ := t1_vkHeightWidth c (|t|+1)

def t1_vkDiskCenter (c t : ℝ) : ℂ :=
  t1_verticalPoint (1+t1_vkDiskWidth c t/4) t

def t1_vkContourLeft (c t : ℝ) : ℝ := 1-t1_vkDiskWidth c t/8

theorem t1_vkDiskWidth_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < t1_vkDiskWidth c t :=
  t1_vkHeightWidth_pos hc _

theorem t1_vkDiskWidth_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : t1_vkDiskWidth c t ≤ c :=
  t1_vkHeightWidth_le hc _

theorem t1_vkDiskWidth_inv_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (t1_vkDiskWidth c t)⁻¹ ≤ ((1+t1_vkHeightBase)/c)*(1+|t|) := by
  have hB : 0 ≤ t1_vkHeightBase := (Real.exp_pos _).le
  rw [t1_vkDiskWidth,t1_vkHeightWidth,inv_div]
  have ht := t1_vkHeightDenom_le_linear (|t|+1)
  rw [abs_of_nonneg (by positivity : 0 ≤ |t|+1)] at ht
  apply (div_le_iff₀ hc).2
  have hm : ((1+t1_vkHeightBase)/c)*(1+|t|)*c = (1+t1_vkHeightBase)*(1+|t|) := by
    field_simp [hc.ne']
  rw [hm]
  nlinarith [mul_nonneg hB (abs_nonneg t)]

theorem t1_vkContourLeft_bounds {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4) (t : ℝ) :
    (1 : ℝ)/2 ≤ t1_vkContourLeft c t ∧ t1_vkContourLeft c t < 1 := by
  have hD := t1_vkDiskWidth_pos hc t
  have hD' := t1_vkDiskWidth_le hc.le t
  unfold t1_vkContourLeft
  constructor <;> linarith

theorem t1_vkContourLeft_mono {c t u : ℝ} (hc : 0 ≤ c) (htu : |t| ≤ |u|) :
    t1_vkContourLeft c t ≤ t1_vkContourLeft c u := by
  have h : abs (|t|+1) ≤ abs (|u|+1) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ |t|+1),abs_of_nonneg (by positivity : 0 ≤ |u|+1)]
    linarith
  have hw := t1_vkHeightWidth_antitone_abs hc h
  unfold t1_vkContourLeft t1_vkDiskWidth
  linarith

theorem t1_vkDisk_inside_region {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (t : ℝ) {w : ℂ} (hw : w ∈ ball 0 (t1_vkDiskWidth c t/2)) :
    1-t1_vkHeightWidth c (t1_vkDiskCenter c t+w).im ≤ (t1_vkDiskCenter c t+w).re := by
  have hd := t1_vkDiskWidth_pos hc t
  have hd' := t1_vkDiskWidth_le hc.le t
  have hn : ‖w‖ < t1_vkDiskWidth c t/2 := mem_ball_zero_iff.mp hw
  have hi : |(t1_vkDiskCenter c t+w).im| ≤ |t|+1 := by
    rw [Complex.add_im,t1_vkDiskCenter,t1_verticalPoint_im]
    exact (abs_add_le t w.im).trans (add_le_add_right
      ((Complex.abs_im_le_norm w).trans (by linarith : ‖w‖ ≤ 1)) _)
  have hwidth : t1_vkDiskWidth c t ≤ t1_vkHeightWidth c (t1_vkDiskCenter c t+w).im := by
    apply t1_vkHeightWidth_antitone_abs hc.le
    rwa [abs_of_nonneg (by positivity : 0 ≤ |t|+1)]
  have hr := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
  have he : (t1_vkDiskCenter c t+w).re = 1+t1_vkDiskWidth c t/4+w.re := by
    rw [Complex.add_re,t1_vkDiskCenter,t1_verticalPoint_re]
  rw [he]
  linarith

theorem t1_vkDisk_norm_le {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1+‖t1_vkDiskCenter c t+w‖ ≤ 4*(1+|t|) := by
  have hd := t1_vkDiskWidth_pos hc t
  have hd' := t1_vkDiskWidth_le hc.le t
  have hcN := Complex.norm_le_abs_re_add_abs_im (t1_vkDiskCenter c t)
  rw [t1_vkDiskCenter,t1_verticalPoint_re,t1_verticalPoint_im,
    abs_of_nonneg (by linarith : 0 ≤ 1+t1_vkDiskWidth c t/4)] at hcN
  change ‖t1_vkDiskCenter c t‖ ≤ 1+t1_vkDiskWidth c t/4+|t| at hcN
  linarith [norm_add_le (t1_vkDiskCenter c t) w,abs_nonneg t]

theorem t1_vkDisk_evaluation {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hl : t1_vkContourLeft c s.im ≤ s.re)
    (hr : s.re ≤ 1+t1_vkDiskWidth c s.im/4) :
    let w := s-t1_vkDiskCenter c s.im
    ‖w‖ ≤ 3*t1_vkDiskWidth c s.im/8 ∧
      w ∈ ball 0 (t1_vkDiskWidth c s.im/2) := by
  intro w
  have hd := t1_vkDiskWidth_pos hc s.im
  have hN : ‖w‖ = 1+t1_vkDiskWidth c s.im/4-s.re := by
    dsimp only [w,t1_vkDiskCenter]
    rw [← dist_eq_norm,t1_verticalPoint_distance,abs_of_nonpos (by linarith)]
    ring
  unfold t1_vkContourLeft at hl
  refine ⟨by rw [hN]; linarith,mem_ball_zero_iff.mpr ?_⟩
  rw [hN]
  linarith

end Markov
