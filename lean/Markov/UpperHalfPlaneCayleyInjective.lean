import Markov.UpperHalfPlaneCayley

noncomputable section
namespace Markov

/-- The literal Cayley map is injective on the actual upper half-plane. -/
theorem upperHalfPlaneCayley_injective : Function.Injective upperHalfPlaneCayley := by
  intro z w h
  have hcross := (div_eq_div_iff (upperHalfPlaneCayley_den_ne_zero z)
    (upperHalfPlaneCayley_den_ne_zero w)).mp h
  have he : (2*Complex.I)*((z : ℂ)-(w : ℂ)) = 0 := by
    calc
      (2*Complex.I)*((z : ℂ)-(w : ℂ)) =
          ((z : ℂ)-Complex.I)*((w : ℂ)+Complex.I) -
            ((w : ℂ)-Complex.I)*((z : ℂ)+Complex.I) := by ring
      _ = 0 := sub_eq_zero.mpr hcross
  have hz : (z : ℂ) = (w : ℂ) := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero))
  exact UpperHalfPlane.ext hz

end Markov
