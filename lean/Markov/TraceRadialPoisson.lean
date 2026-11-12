import Markov.TraceSmoothedSections
import Markov.SchwartzLatticeSummability
import Mathlib.Analysis.Fourier.PoissonSummation

/-! Absolute convergence and the radial Poisson step for the actual smoothed
section profile. The integer multiple parameter includes zero at this stage. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace Markov

def traceRadialMesh (S : ℝ) (k : ℤ × ℤ) : ℝ :=
  (S * ‖euclideanIntDirection k‖)⁻¹

def traceRadialNormal (k : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  NormedSpace.normalize (euclideanIntDirection k)

def traceRadialFourierTerm (S Q : ℝ) (k : ℤ × ℤ) (m : ℤ) : ℂ :=
  𝓕 (traceComplexBallIndicator 1) ((S * (m : ℝ)) • euclideanIntDirection k) *
    𝓕 traceComplexMollifier (((m : ℝ) / Q) • euclideanIntDirection k)

theorem traceRadialMesh_pos (S : ℝ) (hS : 0 < S) (k : ℤ × ℤ) (hk : k ≠ 0) :
    0 < traceRadialMesh S k :=
  inv_pos.mpr (mul_pos hS (norm_pos_iff.mpr (euclideanIntDirection_ne_zero k hk)))

theorem traceRadialNormal_norm (k : ℤ × ℤ) (hk : k ≠ 0) :
    ‖traceRadialNormal k‖ = 1 := NormedSpace.norm_normalize (euclideanIntDirection_ne_zero k hk)

theorem integerRay_injective (k : ℤ × ℤ) (hk : k ≠ 0) :
    Function.Injective (fun m : ℤ => (m * k.1, m * k.2)) := by
  intro m n h
  by_cases hk0 : k.1 = 0
  · have hk1 : k.2 ≠ 0 := by intro hh; exact hk (Prod.ext hk0 hh)
    exact mul_right_cancel₀ hk1 (congrArg Prod.snd h)
  · exact mul_right_cancel₀ hk0 (congrArg Prod.fst h)

theorem euclideanIntDirection_integerRay (k : ℤ × ℤ) (m : ℤ) :
    euclideanIntDirection (m * k.1, m * k.2) = (m : ℝ) • euclideanIntDirection k := by
  ext i
  fin_cases i <;> simp [euclideanIntDirection, Int.cast_mul]

theorem trace_indicator_fourier_norm_le_area (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖𝓕 (traceComplexBallIndicator 1) ξ‖ ≤ traceEuclideanArea := by
  rw [Real.fourier_eq]
  calc
    _ ≤ ∫ z, ‖Real.fourierChar (-inner ℝ z ξ) • traceComplexBallIndicator 1 z‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ z, traceBallIndicator 1 z := by
      congr 1
      funext z
      simp only [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
      rw [traceComplexBallIndicator_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (traceBallIndicator_nonneg 1 z)]
    _ = traceEuclideanArea := by rw [traceBallIndicator_integral]; norm_num

def traceScaledMollifierSchwartz (Q : ℝ) (hQ : 0 < Q) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (show HasCompactSupport (traceComplexScaledMollifier Q) from by
    simpa [HasCompactSupport, tsupport, Function.support, traceComplexScaledMollifier] using
      traceScaledMollifier_hasCompactSupport Q hQ).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (traceScaledMollifier_contDiff Q))

theorem trace_mollifier_ray_norm_summable (Q : ℝ) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) :
    Summable (fun m : ℤ =>
      ‖𝓕 traceComplexMollifier (((m : ℝ) / Q) • euclideanIntDirection k)‖) := by
  have hs := (schwartz_fourier_lattice_norm_summable (traceScaledMollifierSchwartz Q hQ)).comp_injective
    (integerRay_injective k hk)
  convert hs using 1
  funext m
  change ‖𝓕 traceComplexMollifier (((m : ℝ) / Q) • euclideanIntDirection k)‖ =
    ‖𝓕 (traceComplexScaledMollifier Q) (euclideanIntDirection (m * k.1, m * k.2))‖
  rw [euclideanIntDirection_integerRay]
  rw [trace_mollifier_fourier_scaling Q hQ, smul_smul]
  simp only [div_eq_mul_inv, mul_comm]

theorem traceRadialFourierTerm_norm_summable (S Q : ℝ) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) :
    Summable (fun m : ℤ => ‖traceRadialFourierTerm S Q k m‖) := by
  apply ((trace_mollifier_ray_norm_summable Q hQ k hk).mul_left traceEuclideanArea).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro m
  rw [traceRadialFourierTerm, norm_mul]
  exact mul_le_mul_of_nonneg_right (trace_indicator_fourier_norm_le_area _) (norm_nonneg _)

theorem traceRadialFourierTerm_summable (S Q : ℝ) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) : Summable (traceRadialFourierTerm S Q k) :=
  (traceRadialFourierTerm_norm_summable S Q hQ k hk).of_norm

theorem traceSmoothedSection_radial_fourier (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) (m : ℤ) :
    𝓕 (fun t => (traceSmoothedSection S Q (traceRadialNormal k) t : ℂ))
      ((m : ℝ) / traceRadialMesh S k) = traceRadialFourierTerm S Q k m :=
  traceSmoothedSection_fourier_at_ray S Q m hS hQ (euclideanIntDirection k)
    (euclideanIntDirection_ne_zero k hk)

theorem traceSmoothedSection_radial_fourier_norm_summable
    (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) (k : ℤ × ℤ) (hk : k ≠ 0) :
    Summable (fun m : ℤ =>
      ‖𝓕 (fun t => (traceSmoothedSection S Q (traceRadialNormal k) t : ℂ))
        ((m : ℝ) / traceRadialMesh S k)‖) := by
  simp_rw [traceSmoothedSection_radial_fourier S Q hS hQ k hk]
  exact traceRadialFourierTerm_norm_summable S Q hQ k hk

theorem fourier_comp_positive_mul_real (f : ℝ → ℂ) (h : ℝ) (hh : 0 < h) (w : ℝ) :
    𝓕 (fun x : ℝ => f (h * x)) w = h⁻¹ • 𝓕 f (w / h) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hphase (x : ℝ) : (h * x) * (w / h) = x * w := by field_simp
  calc
    (∫ x : ℝ, Real.fourierChar (-(x * w)) • f (h * x)) =
        ∫ x : ℝ, Real.fourierChar (-((h * x) * (w / h))) • f (h * x) := by
      simp_rw [hphase]
    _ = _ := by
      simpa only [smul_eq_mul, Module.finrank_self, pow_one] using
        Measure.integral_comp_smul_of_nonneg volume
          (fun x : ℝ => Real.fourierChar (-(x * (w / h))) • f x) h (hR := hh.le)

/-- The available one-dimensional Poisson theorem, rescaled to a positive
mesh. Compact support supplies decay; Fourier samples must be summable. -/
theorem compact_scaled_real_poisson (g : ℝ → ℂ) (hc : Continuous g)
    (hs : HasCompactSupport g) (h : ℝ) (hh : 0 < h)
    (hF : Summable (fun n : ℤ => 𝓕 g ((n : ℝ) / h))) :
    h • (∑' n : ℤ, g (h * (n : ℝ))) = ∑' n : ℤ, 𝓕 g ((n : ℝ) / h) := by
  let q : ℝ → ℂ := fun x => g (h * x)
  have hqc : Continuous q := hc.comp (continuous_const.mul continuous_id)
  have hqs : HasCompactSupport q := by
    simpa only [smul_eq_mul] using hs.comp_smul hh.ne'
  have hqd : q =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    have he := hasCompactSupport_iff_eventuallyEq.mp hqs
    rw [Filter.coclosedCompact_eq_cocompact] at he
    filter_upwards [he] with x hx
    simp only [hx, Pi.zero_apply, norm_zero, one_mul]
    exact norm_nonneg _
  have hqF : Summable (fun n : ℤ => 𝓕 q (n : ℝ)) := by
    simp_rw [show ∀ w : ℝ, 𝓕 q w = h⁻¹ • 𝓕 g (w / h) from
      fun w => fourier_comp_positive_mul_real g h hh w]
    exact hF.const_smul h⁻¹
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    hqc (b := 2) (by norm_num) hqd hqF 0
  have hpeq : (∑' n : ℤ, g (h * (n : ℝ))) =
      ∑' n : ℤ, h⁻¹ • 𝓕 g ((n : ℝ) / h) := by
    simpa [q, fourier_comp_positive_mul_real g h hh] using hp
  rw [hpeq, hF.tsum_const_smul, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]

/-- Exact full one-dimensional Poisson for the actual radial section. All
Fourier-sample summability hypotheses are discharged by the radial kernel. -/
theorem trace_radial_poisson (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) :
    (traceRadialMesh S k) •
        (∑' m : ℤ, (traceSmoothedSection S Q (traceRadialNormal k)
          (traceRadialMesh S k * (m : ℝ)) : ℂ)) =
      ∑' m : ℤ, traceRadialFourierTerm S Q k m := by
  have hθ := traceRadialNormal_norm k hk
  have hc : Continuous (fun t => (traceSmoothedSection S Q (traceRadialNormal k) t : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (traceSmoothedSection_continuous S Q hS hQ hθ)
  have hs : HasCompactSupport
      (fun t => (traceSmoothedSection S Q (traceRadialNormal k) t : ℂ)) := by
    simpa [HasCompactSupport, tsupport, Function.support] using
      traceSmoothedSection_hasCompactSupport S Q hS hQ hθ
  have hF := (traceSmoothedSection_radial_fourier_norm_summable S Q hS hQ k hk).of_norm
  have hp := compact_scaled_real_poisson _ hc hs (traceRadialMesh S k)
    (traceRadialMesh_pos S hS k hk) hF
  simpa only [traceSmoothedSection_radial_fourier S Q hS hQ k hk] using hp

end Markov
