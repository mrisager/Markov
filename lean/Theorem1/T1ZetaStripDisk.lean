import T1ZetaGrowth
import T1DiskReciprocalBound

/-! Literal disks centered on Re(s)=2 for the fixed zero-free strip. -/
noncomputable section
open Complex Set Metric
namespace Markov

def t1_zetaDiskCenter (t : ℝ) : ℂ := (2 : ℂ)+(t : ℂ)*I

theorem t1_zetaDiskCenter_re (t : ℝ) : (t1_zetaDiskCenter t).re = 2 := by
  simp [t1_zetaDiskCenter]

theorem t1_zetaDiskCenter_im (t : ℝ) : (t1_zetaDiskCenter t).im = t := by
  simp [t1_zetaDiskCenter]

theorem t1_zetaDiskCenter_norm (t : ℝ) : ‖t1_zetaDiskCenter t‖ ≤ 2+|t| := by
  simpa only [t1_zetaDiskCenter, norm_ofNat,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one] using norm_add_le (2 : ℂ) ((t : ℂ)*I)

theorem t1_zetaDiskCenter_distance (s : ℂ) :
    ‖s-t1_zetaDiskCenter s.im‖ = |s.re-2| := by
  have h : s-t1_zetaDiskCenter s.im = ((s.re-2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re,t1_zetaDiskCenter_re,Complex.ofReal_re]
    · simp only [Complex.sub_im,t1_zetaDiskCenter_im,sub_self,Complex.ofReal_im]
  rw [h,Complex.norm_real,Real.norm_eq_abs]

theorem t1_zetaDisk_realPart (t : ℝ) (δ : ℝ) (hδ : 0 < δ) {w : ℂ}
    (hw : w ∈ ball 0 (1+3*δ/4)) :
    1-δ < (t1_zetaDiskCenter t+w).re := by
  have hn := mem_ball_zero_iff.mp hw
  have h := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
  rw [Complex.add_re,t1_zetaDiskCenter_re]
  linarith

theorem t1_zetaDisk_norm (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 2) :
    1+‖t1_zetaDiskCenter t+w‖ ≤ 5*(1+|t|) := by
  linarith [norm_add_le (t1_zetaDiskCenter t) w,t1_zetaDiskCenter_norm t,abs_nonneg t]

end Markov
