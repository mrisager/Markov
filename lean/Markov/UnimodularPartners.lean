import Markov.FareyHolonomy

/-! Integral partners of a unimodular vector differ by an integral shear.
All statements here are coordinate identities over the integers. -/

namespace Markov

/-- The determinant coordinate identity before imposing unimodularity. -/
theorem intDet_vector_decomposition (u v w : ℤ × ℤ) :
    intDet u w • v = intDet v w • u + intDet u v • w := by
  ext <;> simp [intDet, zsmul_eq_mul] <;> ring

/-- The integral kernel of determinant against a unimodular vector is the
integral span of that vector, with an explicit coefficient. -/
theorem unimodular_kernel_eq_zsmul (u w x : ℤ × ℤ)
    (huw : intDet u w = 1) (hux : intDet u x = 0) :
    x = intDet x w • u := by
  simpa only [huw, hux, one_smul, zero_smul, add_zero]
    using intDet_vector_decomposition u x w

/-- Partners with determinant 1 have an exact integral-shear relation.
The shear coefficient is itself the determinant of the two partners. -/
theorem unimodular_partners_shear (u v w : ℤ × ℤ)
    (huv : intDet u v = 1) (huw : intDet u w = 1) :
    v = w + intDet v w • u := by
  have h := intDet_vector_decomposition u v w
  simpa only [huv, huw, one_smul, add_comm] using h

/-- Existential form of the integral-shear relation. -/
theorem unimodular_partners_exists_shear (u v w : ℤ × ℤ)
    (huv : intDet u v = 1) (huw : intDet u w = 1) :
    ∃ k : ℤ, v = w + k • u :=
  ⟨intDet v w, unimodular_partners_shear u v w huv huw⟩

/-- The orientation-reversed form has the opposite shear coefficient. -/
theorem neg_unimodular_partners_shear (u v w : ℤ × ℤ)
    (huv : intDet u v = -1) (huw : intDet u w = -1) :
    v = w + (-intDet v w) • u := by
  have hv : intDet (-u) v = 1 := by
    dsimp [intDet] at *
    nlinarith
  have hw : intDet (-u) w = 1 := by
    dsimp [intDet] at *
    nlinarith
  have h := unimodular_partners_shear (-u) v w hv hw
  simpa only [smul_neg, neg_smul] using h

/-- Orientation-reversed partners also differ by an integral multiple. -/
theorem neg_unimodular_partners_exists_shear (u v w : ℤ × ℤ)
    (huv : intDet u v = -1) (huw : intDet u w = -1) :
    ∃ k : ℤ, v = w + k • u :=
  ⟨-intDet v w, neg_unimodular_partners_shear u v w huv huw⟩

end Markov
