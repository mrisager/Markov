/-
Selected definitions from David Sanftenberg's RiemannGaussian,
commit f5fd3ddb407972f9ca65298fbe9be3225fe06635, Apache 2.0.
The VK port keeps these literal Dirichlet and eta terms; unrelated
Gram, arithmetic flux and zero-detection results are not imported.
-/
import RiemannGaussian.ZetaPrimeGram

namespace RiemannGaussian
noncomputable section

def zetaPrimeExpWeight (σ : ℝ) (m : ℕ) : ℝ := Real.exp (-σ * Real.log m)

/-- The feature norm depends only on the real part of its exponent. -/
theorem norm_zetaPrimeFeature (s : ℂ) (m : ℕ) :
    ‖zetaPrimeFeature s m‖ = zetaPrimeExpWeight s.re m := by
  simp only [zetaPrimeFeature, zetaPrimeExpWeight, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

end
end RiemannGaussian

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
