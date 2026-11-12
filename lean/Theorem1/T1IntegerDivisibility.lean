import Markov.PrimitiveRayDecomposition

noncomputable section
namespace Markov

theorem t1_dvd_integer_gcd_iff (g : ℕ) (p : ℤ × ℤ) :
    g ∣ Int.gcd p.1 p.2 ↔ (g : ℤ) ∣ p.1 ∧ (g : ℤ) ∣ p.2 := by
  constructor
  · intro hd
    have hd' := Int.natCast_dvd_natCast.mpr hd
    exact ⟨hd'.trans (Int.gcd_dvd_left _ _), hd'.trans (Int.gcd_dvd_right _ _)⟩
  · rintro ⟨h1, h2⟩
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd h1 h2)

/-- Divisibility of both signed coordinates constructs an actual integer
preimage under scalar multiplication. -/
theorem t1_integer_gcd_dvd_iff_nsmul (g : ℕ) (p : ℤ × ℤ) :
    g ∣ Int.gcd p.1 p.2 ↔ ∃ q : ℤ × ℤ, g • q = p := by
  rw [t1_dvd_integer_gcd_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    ext <;> simp [ha, hb]
  · rintro ⟨q, rfl⟩
    change (g : ℤ) ∣ (g : ℤ) * q.1 ∧ (g : ℤ) ∣ (g : ℤ) * q.2
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem t1_integer_nsmul_injective (g : ℕ) (hg : 0 < g) :
    Function.Injective (fun p : ℤ × ℤ => g • p) := by
  have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  intro p q h
  apply Prod.ext
  · apply mul_left_cancel₀ hg'
    simpa only [nsmul_eq_mul, Prod.fst_mul, Prod.fst_natCast] using congrArg Prod.fst h
  · apply mul_left_cancel₀ hg'
    simpa only [nsmul_eq_mul, Prod.snd_mul, Prod.snd_natCast] using congrArg Prod.snd h

theorem t1_integer_nsmul_ne_zero (g : ℕ) (hg : 0 < g) {p : ℤ × ℤ}
    (hp : p ≠ (0, 0)) : g • p ≠ (0, 0) := by
  intro h
  apply hp
  apply t1_integer_nsmul_injective g hg
  simpa only [smul_zero] using h

end Markov
