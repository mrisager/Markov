/-
Selected definitions from David Sanftenberg's RiemannGaussian,
commit f5fd3ddb407972f9ca65298fbe9be3225fe06635, Apache 2.0.
The VK port keeps these literal Dirichlet and eta terms; unrelated
Gram, arithmetic flux and zero-detection results are not imported.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RiemannGaussian
noncomputable section

def pairedEtaCoreSummand (s : ℂ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

def pairedEtaCorePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaCoreSummand s n

end
end RiemannGaussian

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
