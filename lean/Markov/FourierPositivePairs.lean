import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! Pairing the positive and negative frequencies of an absolutely
convergent even integer series, with strictly positive indices explicit. -/

noncomputable section
open Function FourierTransform
open scoped FourierTransform

namespace Markov

/-- Restriction to strictly positive integer indices preserves absolute convergence. -/
theorem summable_norm_positive_of_summable_norm {a : ℤ → ℂ}
    (ha : Summable (fun n : ℤ ↦ ‖a n‖)) :
    Summable (fun m : ℕ ↦ ‖a ((m : ℤ) + 1)‖) := by
  have hi : Function.Injective (fun m : ℕ ↦ (m : ℤ) + 1) := by
    intro i j hij
    dsimp only at hij
    exact Nat.cast_injective (add_right_cancel hij)
  exact ha.comp_injective hi

/-- The full even integer series is the zero term plus twice the positive
series; `m+1` excludes the zero mode from the latter. -/
theorem tsum_int_even_eq_zero_add_two_mul_tsum_positive {a : ℤ → ℂ}
    (ha : Summable (fun n : ℤ ↦ ‖a n‖)) (heven : Function.Even a) :
    (∑' n : ℤ, a n) = a 0 + 2 * ∑' m : ℕ, a ((m : ℤ) + 1) := by
  have hp : Summable (fun m : ℕ ↦ a ((m : ℤ) + 1)) :=
    (summable_norm_positive_of_summable_norm ha).of_norm
  have hneg : (fun m : ℕ ↦ a (-((m : ℤ) + 1))) = (fun m : ℕ ↦ a ((m : ℤ) + 1)) :=
    funext (fun m ↦ heven ((m : ℤ) + 1))
  have hm : Summable (fun m : ℕ ↦ a (-((m : ℤ) + 1))) := by
    rw [hneg]
    exact hp
  rw [tsum_of_add_one_of_neg_add_one hp hm, hneg]
  ring

/-- The corresponding nonzero-frequency discrepancy identity. -/
theorem tsum_int_even_sub_zero_eq_two_mul_tsum_positive {a : ℤ → ℂ}
    (ha : Summable (fun n : ℤ ↦ ‖a n‖)) (heven : Function.Even a) :
    (∑' n : ℤ, a n) - a 0 = 2 * ∑' m : ℕ, a ((m : ℤ) + 1) := by
  rw [tsum_int_even_eq_zero_add_two_mul_tsum_positive ha heven]
  ring

/-- Negating the integration variable shows that Fourier transformation
preserves evenness, with the standard negative-exponent convention. -/
theorem fourier_even_of_even {f : ℝ → ℂ} (hf : Function.Even f) : Function.Even (𝓕 f) := by
  intro r
  have hcomp : f ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) = f := by
    funext x
    exact hf x
  have key := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f r
  rw [hcomp] at key
  exact key.symm

end Markov
