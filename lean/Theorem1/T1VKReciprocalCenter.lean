import T1VKDiskGeometry
import T1ReciprocalZetaRightBound

/-! Fixed polynomial bounds for the centers of the shrinking disks and
for points to their right. -/
noncomputable section
open Complex
namespace Markov

def t1_vkInverseWidthConstant (c : ℝ) : ℝ := (1+t1_vkHeightBase)/c

theorem t1_vkInverseWidthConstant_pos {c : ℝ} (hc : 0 < c) :
    0 < t1_vkInverseWidthConstant c := by
  unfold t1_vkInverseWidthConstant t1_vkHeightBase
  positivity

theorem t1_vkReciprocalZeta_right {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : 1+t1_vkDiskWidth c s.im/4 ≤ s.re) :
    ‖t1_reciprocalZeta s‖ ≤ (2+4*t1_vkInverseWidthConstant c)*(1+|s.im|) := by
  have hd := t1_vkDiskWidth_pos hc s.im
  have hσ : 1 < s.re := by linarith
  have hw := t1_vkDiskWidth_inv_le hc s.im
  change (t1_vkDiskWidth c s.im)⁻¹ ≤ t1_vkInverseWidthConstant c*(1+|s.im|) at hw
  have hR : 1/(s.re-1) ≤ 4*(t1_vkDiskWidth c s.im)⁻¹ := by
    calc
      _ ≤ 1/(t1_vkDiskWidth c s.im/4) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = _ := by ring
  calc
    _ ≤ 2+1/(s.re-1) := t1_reciprocalZeta_norm_le_right hσ
    _ ≤ 2+4*(t1_vkDiskWidth c s.im)⁻¹ := by linarith
    _ ≤ _ := by linarith [abs_nonneg s.im]

theorem t1_vkPoleRemovedZeta_inverse_center {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(t1_poleRemovedZeta (t1_vkDiskCenter c t))⁻¹‖ ≤
      ((2+4*t1_vkInverseWidthConstant c)*(4*t1_vkInverseWidthConstant c))*(1+|t|)^2 := by
  let z := t1_vkDiskCenter c t
  let d := t1_vkDiskWidth c t
  let L := t1_vkInverseWidthConstant c
  let u := 1+|t|
  have hL := t1_vkInverseWidthConstant_pos hc
  have hd : 0 < d := t1_vkDiskWidth_pos hc t
  have hu : 0 < u := by dsimp [u]; positivity
  have hRe : z.re = 1+d/4 := t1_verticalPoint_re _ _
  have hIm : z.im = t := t1_verticalPoint_im _ _
  have hb := t1_vkReciprocalZeta_right hc (s := z) (by rw [hRe,hIm])
  rw [hIm,t1_reciprocalZeta,div_eq_mul_inv,norm_mul] at hb
  have hN : d/4 ≤ ‖z-1‖ := by
    have he := Complex.abs_re_le_norm (z-1)
    rw [Complex.sub_re,hRe,Complex.one_re,add_sub_cancel_left,abs_of_pos (show 0 < d/4 by positivity)] at he
    exact he
  have hw : d⁻¹ ≤ L*u := t1_vkDiskWidth_inv_le hc t
  calc
    _ ≤ (2+4*L)*u/(d/4) := by
      apply (le_div_iff₀ (show 0 < d/4 by positivity)).2
      exact (mul_le_mul_of_nonneg_left hN (norm_nonneg _)).trans (by simpa only [mul_comm] using hb)
    _ = ((2+4*L)*u)*(4*d⁻¹) := by ring
    _ ≤ ((2+4*L)*u)*(4*(L*u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by norm_num)) (by positivity)
    _ = _ := by ring

end Markov
