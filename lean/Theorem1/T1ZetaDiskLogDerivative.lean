import T1DiskLogDerivativeDecomposition
import T1ReciprocalZetaRightBound
import T1VKRegion

/-! Signed logarithmic derivative of actual zeta near the line one,
with the center cost supplied by the genuine reciprocal Dirichlet series. -/

namespace Markov
open Complex Filter Metric Set
open scoped ComplexConjugate Topology
noncomputable section

def t1_zetaDiscTranslate (x t : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (z+t1_verticalPoint (1+x) t)

theorem t1_zetaDiscTranslate_analytic {r x t : ℝ} (hr : r ≤ 1) (ht : 2 ≤ |t|) :
    AnalyticOnNhd ℂ (t1_zetaDiscTranslate x t) (closedBall 0 r) := by
  intro z hz
  have hn : z + t1_verticalPoint (1+x) t ≠ 1 := by
    intro he
    have h := congrArg Complex.im he
    simp only [Complex.add_im,t1_verticalPoint_im,Complex.one_im] at h
    have hnorm : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hb := (Complex.abs_im_le_norm z).trans (hnorm.trans hr)
    rw [show z.im = -t by linarith,abs_neg] at hb
    linarith
  unfold t1_zetaDiscTranslate
  have hZ : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact (hZ.analyticOnNhd isOpen_compl_singleton _ hn).comp
    (f := fun w : ℂ => w+t1_verticalPoint (1+x) t) (by fun_prop)

theorem t1_zetaDiscLogDeriv_at_zero {x t : ℝ} (hx : 0 < x) :
    logDeriv (t1_zetaDiscTranslate x t) 0 = logDeriv riemannZeta (t1_verticalPoint (1+x) t) := by
  let c := t1_verticalPoint (1+x) t
  have hc : c ≠ 1 := by
    intro he
    have h := congrArg Complex.re he
    simp [c,t1_verticalPoint_re] at h
    linarith
  change logDeriv (riemannZeta ∘ fun z : ℂ => z+c) 0 = _
  have hζ : DifferentiableAt ℂ riemannZeta ((fun z : ℂ => z+c) 0) := by
    simpa only [zero_add] using differentiableAt_riemannZeta hc
  rw [logDeriv_comp (g := fun z : ℂ => z+c) (x := 0) hζ (by fun_prop)]
  simp [c]

theorem t1_zetaDisc_center_cost {x t : ℝ} (hx : 0 < x) :
    t1_zetaDiscTranslate x t 0 ≠ 0 ∧
      -Real.log ‖t1_zetaDiscTranslate x t 0‖ ≤ Real.log (2+1/x) := by
  let c := t1_verticalPoint (1+x) t
  have hc : 1 < c.re := by rw [t1_verticalPoint_re]; linarith
  have hne : c ≠ 1 := by intro he; simp [he] at hc
  have hn := riemannZeta_ne_zero_of_one_le_re hc.le
  have h := t1_reciprocalZeta_norm_le_right hc
  rw [t1_reciprocalZeta_of_ne_one hne,norm_inv] at h
  have hcx : c.re - 1 = x := by rw [t1_verticalPoint_re]; ring
  rw [hcx] at h
  refine ⟨by simpa [t1_zetaDiscTranslate,c] using hn,?_⟩
  have hlog := Real.log_le_log (inv_pos.mpr (norm_pos_iff.mpr hn)) h
  rw [Real.log_inv] at hlog
  simpa [t1_zetaDiscTranslate,c] using hlog

/-- A zero in translated coordinates always has strictly negative real part. -/
theorem t1_zetaDisc_zero_re_lt {x t : ℝ} {a : ℂ}
    (ha : t1_zetaDiscTranslate x t a = 0) : a.re < -x := by
  by_contra! h
  have hre : 1 ≤ (a+t1_verticalPoint (1+x) t).re := by
    rw [Complex.add_re,t1_verticalPoint_re]
    linarith
  exact riemannZeta_ne_zero_of_one_le_re hre ha

/-- The local logarithmic derivative with the actual finite signed zero sum. -/
theorem t1_zetaDiscLogDerivative_split {R B x t : ℝ}
    (hR : 0 < R) (hRu : R ≤ 1) (hB : 0 ≤ B) (hx : 0 < x) (ht : 2 ≤ |t|)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) R, ‖t1_zetaDiscTranslate x t z‖ ≤ Real.exp B) :
    ∃ (r : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (v : ℂ),
      R/2 < r ∧ r < 3*R/4 ∧
      (∀ a : ℂ, a ∈ S ↔ a ∈ closedBall 0 r ∧ t1_zetaDiscTranslate x t a = 0) ∧
      (∀ a ∈ S, 0 < m a ∧ ‖a‖ < r ∧ a ≠ 0 ∧
        0 ≤ ((m a : ℂ) * t1_blaschkeLogTerm r a).re) ∧
      ‖v‖ ≤ 4*(B+Real.log (2+1/x))/R ∧
      logDeriv riemannZeta (t1_verticalPoint (1+x) t) =
        v + ∑ a ∈ S, (m a : ℂ) * t1_blaschkeLogTerm r a := by
  obtain ⟨h0,hC⟩ := t1_zetaDisc_center_cost (t := t) hx
  have hA : 0 < B + Real.log (2+1/x) :=
    add_pos_of_nonneg_of_pos hB (Real.log_pos (by linarith [one_div_pos.mpr hx]))
  obtain ⟨r,S,m,g,hrlo,hrhi,hS,hm,hg,he⟩ :=
    t1_disk_logDeriv_decomposition hR (t1_zetaDiscTranslate_analytic hRu ht) h0 hA hbound hC
  have hr : 0 < r := by linarith
  refine ⟨r,S,m,logDeriv g 0,hrlo,hrhi,hS,?_,hg,?_⟩
  · intro a ha
    obtain ⟨hm',har,ha0⟩ := hm a ha
    refine ⟨hm',har,ha0,?_⟩
    rw [show (m a : ℂ) = ((m a : ℝ) : ℂ) by exact_mod_cast rfl, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (t1_blaschkeLogTerm_re_nonneg hr ha0 har
      (by linarith [t1_zetaDisc_zero_re_lt ((hS a).mp ha).2]))
  · rwa [t1_zetaDiscLogDeriv_at_zero hx] at he

end
end Markov
