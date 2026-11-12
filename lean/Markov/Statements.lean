import Markov.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The asymptotic statements and error scales of Theorems 1 and 12.
The fractional exponents are real numbers. -/

open Filter Asymptotics

namespace Markov

noncomputable def mainTerm (C x : ℝ) : ℝ := C * Real.log (3 * x) ^ 2

noncomputable def unconditionalScale (x : ℝ) : ℝ :=
  Real.log x * Real.rpow (Real.log (Real.log (Real.log x))) ((1 : ℝ) / 10) /
    Real.rpow (Real.log (Real.log x)) ((3 : ℝ) / 10)

noncomputable def conditionalScale (x : ℝ) : ℝ :=
  Real.log x / Real.rpow (Real.log (Real.log x)) ((1 : ℝ) / 2)

/-- Exclude the pole explicitly: the analytic zero-free hypothesis is about `s ≠ 1`. -/
def QuasiRiemannHypothesis : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s ≠ 1 → 1 - δ < s.re → riemannZeta s ≠ 0

def UnconditionalBound (C : ℝ) : Prop :=
  (fun x => count x - mainTerm C x) =O[atTop] unconditionalScale

def ConditionalBound (C : ℝ) : Prop :=
  (fun x => count x - mainTerm C x) =O[atTop] conditionalScale

/-- Both assertions of Theorem 1 with a common positive coefficient.
The proof `t1_mainTheorem` uses `2 * modularMcShaneRivinArea / Real.pi^2`. -/
def MainTheorem : Prop :=
  ∃ C : ℝ, 0 < C ∧ UnconditionalBound C ∧
    (QuasiRiemannHypothesis → ConditionalBound C)

/-- The paper also obtains this consequence using just the prime number theorem. -/
def SublogarithmicBound (C : ℝ) : Prop :=
  (fun x => count x - mainTerm C x) =o[atTop] Real.log

/-- Theorem 12's error bound, parametrized by the count and area. -/
def FullLatticeBound (N : ℝ → ℝ) (area : ℝ) : Prop :=
  (fun R => N R - area * R ^ 2) =O[atTop]
    (fun R => R / Real.rpow (Real.log R) ((3 : ℝ) / 2))

noncomputable def primitiveUnconditionalScale (R : ℝ) : ℝ :=
  R * Real.rpow (Real.log (Real.log R)) ((1 : ℝ) / 10) /
    Real.rpow (Real.log R) ((3 : ℝ) / 10)

noncomputable def primitiveConditionalScale (R : ℝ) : ℝ :=
  R / Real.rpow (Real.log R) ((1 : ℝ) / 2)

end Markov
