import T1MertensFinite

/-! The uniform Mertens envelope and its elementary bound by one.
`T1MertensVKEnvelope` and `T1MertensPowerEnvelope` relate arithmetic
decay estimates to bounds for this envelope. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_mertensNat_abs_le (n : ℕ) : |t1_mertensNat n| ≤ n := by
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 n, |μ g| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ Finset.Icc 1 n, (1 : ℤ) :=
      Finset.sum_le_sum (fun g _ => ArithmeticFunction.abs_moebius_le_one)
    _ = _ := by simp

theorem t1_mertensNat_real_abs_le (n : ℕ) : |(t1_mertensNat n : ℝ)| ≤ n := by
  exact_mod_cast t1_mertensNat_abs_le n

def t1_mertensRatio (n : ℕ) : ℝ := |(t1_mertensNat n : ℝ)| / n

theorem t1_mertensRatio_nonneg (n : ℕ) : 0 ≤ t1_mertensRatio n :=
  div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

theorem t1_mertensRatio_le_one (n : ℕ) : t1_mertensRatio n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, t1_mertensRatio]
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
      (t1_mertensNat_real_abs_le n)

def t1_mertensEnvelope (D : ℕ) : ℝ :=
  sSup (t1_mertensRatio '' Set.Ici D)

theorem t1_mertensEnvelope_bddAbove (D : ℕ) :
    BddAbove (t1_mertensRatio '' Set.Ici D) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, _, rfl⟩
  exact t1_mertensRatio_le_one n

theorem t1_mertensEnvelope_nonneg (D : ℕ) : 0 ≤ t1_mertensEnvelope D := by
  exact (t1_mertensRatio_nonneg D).trans (le_csSup (t1_mertensEnvelope_bddAbove D)
    (Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)))

theorem t1_mertensEnvelope_le_one (D : ℕ) : t1_mertensEnvelope D ≤ 1 := by
  apply csSup_le ⟨t1_mertensRatio D, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩
  rintro _ ⟨n, _, rfl⟩
  exact t1_mertensRatio_le_one n

/-- The supremum is over the actual summatory-Möbius ratios, so its uniform
bound is derived rather than supplied as a cancellation premise. -/
theorem t1_mertensEnvelope_dominates (D n : ℕ) (hDn : D ≤ n) :
    |(t1_mertensNat n : ℝ)| ≤ t1_mertensEnvelope D * n := by
  by_cases hn : n = 0
  · simp [hn, t1_mertensNat_zero]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply (div_le_iff₀ hnR).mp
    exact le_csSup (t1_mertensEnvelope_bddAbove D)
      (Set.mem_image_of_mem _ (Set.mem_Ici.mpr hDn))

theorem t1_mertensEnvelope_antitone : Antitone t1_mertensEnvelope := by
  intro D E hDE
  apply csSup_le ⟨t1_mertensRatio E, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩
  rintro _ ⟨n, hn, rfl⟩
  exact le_csSup (t1_mertensEnvelope_bddAbove D)
    (Set.mem_image_of_mem _ (Set.mem_Ici.mpr (hDE.trans hn)))

/-- Transfer a genuinely proved uniform Mertens bound to the actual
envelope. This lemma retains its analytic bound as an explicit premise. -/
theorem t1_mertensEnvelope_le_of_uniform_bound (D : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, D ≤ n → |(t1_mertensNat n : ℝ)| ≤ C * n) :
    t1_mertensEnvelope D ≤ C := by
  apply csSup_le ⟨t1_mertensRatio D, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩
  rintro _ ⟨n, hn, rfl⟩
  by_cases hn0 : n = 0
  · simpa only [t1_mertensRatio, hn0, Nat.cast_zero, div_zero] using hC
  · exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn0)).mpr (hM n hn)

end Markov
