import Markov.TraceSeminorm

/-! The actual decreasing trace seminorms and their nondegenerate limit.
Every profile and eventual interpolation statement comes from the checked
seed matrix data. -/

noncomputable section
open Filter
open scoped Topology
namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

omit [AddCommGroup E] [Module ℝ E] in
private theorem prefixEnvelope_eq_mul {F : Type*} (f : ℕ → E → ℝ) (g : ℕ → F → ℝ)
    (m : ℕ) (x : E) (q : F) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, f i x = c * g i q) : prefixEnvelope f m x = c * prefixEnvelope g m q := by
  induction m with
  | zero => exact h 0
  | succ m ih =>
    simp only [prefixEnvelope, ih, h, mul_max_of_nonneg _ _ hc]

theorem finiteTraceSeminorm_pos_formula (B : Module.Basis (Fin 2) ℝ E)
    (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hsum : 0 < s + t) :
    finiteTraceSeminorm B n (s • B 0 + t • B 1) =
      (s + t) * seedFrontierProfile modularGeneratorA modularGeneratorB n (t / (s + t)) := by
  rw [finiteTraceSeminorm_positive_cone B n _ ⟨s, t, hs, ht, rfl⟩]
  apply prefixEnvelope_eq_mul _ _ _ _ _ _ hsum.le
  intro i
  exact seedLinearPiece_profile B _ _ n i s t hsum.ne'

theorem finiteTraceSeminorm_next_formula (B : Module.Basis (Fin 2) ℝ E)
    (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hsum : 0 < s + t) :
    finiteTraceSeminorm B n (s • B 1 + t • (-B 0)) =
      (s + t) * seedFrontierProfile modularGeneratorB modularGeneratorA.adjugate n (t / (s + t)) := by
  rw [finiteTraceSeminorm_next_cone B n _ ⟨s, t, hs, ht, rfl⟩]
  apply prefixEnvelope_eq_mul _ _ _ _ _ _ hsum.le
  intro i
  change seedLinearPiece B modularGeneratorB modularGeneratorA.adjugate n i
    (quarterCoordinateMap B (s • B 1 + t • (-B 0))) = _
  rw [show quarterCoordinateMap B (s • B 1 + t • (-B 0)) = s • B 0 + t • B 1 by
    simp only [map_add, map_smul, map_neg, quarterCoordinateMap_one, quarterCoordinateMap_zero,
      neg_neg]]
  exact seedLinearPiece_profile B _ _ n i s t hsum.ne'

private theorem finiteTraceSeminorm_succ_positive (B : Module.Basis (Fin 2) ℝ E)
    (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    finiteTraceSeminorm B (n + 1) (s • B 0 + t • B 1) ≤
      finiteTraceSeminorm B n (s • B 0 + t • B 1) := by
  by_cases hsum : s + t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0]
  · have hp : 0 < s + t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hsum)
    rw [finiteTraceSeminorm_pos_formula B (n + 1) s t hs ht hp,
      finiteTraceSeminorm_pos_formula B n s t hs ht hp]
    exact mul_le_mul_of_nonneg_left (seedFrontierProfile_succ_le _ _ seed_positiveFrickePair n _
      (div_nonneg ht hp.le) ((div_le_one hp).mpr (by linarith))) hp.le

private theorem finiteTraceSeminorm_succ_next (B : Module.Basis (Fin 2) ℝ E)
    (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    finiteTraceSeminorm B (n + 1) (s • B 1 + t • (-B 0)) ≤
      finiteTraceSeminorm B n (s • B 1 + t • (-B 0)) := by
  by_cases hsum : s + t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0]
  · have hp : 0 < s + t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hsum)
    rw [finiteTraceSeminorm_next_formula B (n + 1) s t hs ht hp,
      finiteTraceSeminorm_next_formula B n s t hs ht hp]
    exact mul_le_mul_of_nonneg_left
      (seedFrontierProfile_succ_le _ _ (quadrantSeed_positiveFrickePair 1) n _
        (div_nonneg ht hp.le) ((div_le_one hp).mpr (by linarith))) hp.le

theorem finiteTraceSeminorm_succ_le (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) :
    finiteTraceSeminorm B (n + 1) ≤ finiteTraceSeminorm B n := by
  intro x
  change finiteTraceSeminorm B (n + 1) x ≤ finiteTraceSeminorm B n x
  let s : ℝ := (B.repr x) 0
  let t : ℝ := (B.repr x) 1
  have hrep : x = s • B 0 + t • B 1 := by
    simpa only [s, t, Fin.sum_univ_two] using (B.sum_repr x).symm
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · rw [hrep]
      exact finiteTraceSeminorm_succ_positive B n s t hs ht
    · have he : x = -( (-t) • B 1 + s • (-B 0)) := by rw [hrep]; module
      rw [he, map_neg_eq_map, map_neg_eq_map]
      exact finiteTraceSeminorm_succ_next B n (-t) s (by linarith) hs
  · by_cases ht : 0 ≤ t
    · have he : x = t • B 1 + (-s) • (-B 0) := by rw [hrep]; module
      rw [he]
      exact finiteTraceSeminorm_succ_next B n t (-s) ht (by linarith)
    · have he : x = -((-s) • B 0 + (-t) • B 1) := by rw [hrep]; module
      rw [he, map_neg_eq_map, map_neg_eq_map]
      exact finiteTraceSeminorm_succ_positive B n (-s) (-t) (by linarith) (by linarith)

theorem finiteTraceSeminorm_antitone (B : Module.Basis (Fin 2) ℝ E) :
    Antitone (finiteTraceSeminorm B) :=
  antitone_nat_of_succ_le (finiteTraceSeminorm_succ_le B)

theorem finiteTraceSeminorm_eventual_positive (B : Module.Basis (Fin 2) ℝ E)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      finiteTraceSeminorm B n ((p.1 : ℝ) • B 0 + (p.2 : ℝ) • B 1) =
        primitiveSeedLength modularGeneratorA modularGeneratorB p hp := by
  obtain ⟨N, hN⟩ := seedFrontierProfile_eventual_interpolation _ _ seed_positiveFrickePair p hp
  refine ⟨N, ?_⟩
  intro n hn
  have hs : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have ht : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp.2.1
  have hmass := profileMass_pos p hp
  rw [finiteTraceSeminorm_pos_formula B n _ _ hs ht hmass]
  change profileMass p * seedFrontierProfile _ _ n (profileParameter p) = _
  rw [hN n hn]
  exact mul_div_cancel₀ _ hmass.ne'

/-- Eventual interpolation on the second quadrant uses its own actual seed. -/
theorem finiteTraceSeminorm_eventual_next (B : Module.Basis (Fin 2) ℝ E)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      finiteTraceSeminorm B n ((p.1 : ℝ) • B 1 + (p.2 : ℝ) • (-B 0)) =
        primitiveSeedLength modularGeneratorB modularGeneratorA.adjugate p hp := by
  obtain ⟨N, hN⟩ := seedFrontierProfile_eventual_interpolation
    modularGeneratorB modularGeneratorA.adjugate (quadrantSeed_positiveFrickePair 1) p hp
  refine ⟨N, ?_⟩
  intro n hn
  have hs : (0 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have ht : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp.2.1
  have hmass := profileMass_pos p hp
  rw [finiteTraceSeminorm_next_formula B n _ _ hs ht hmass]
  change profileMass p * seedFrontierProfile _ _ n (profileParameter p) = _
  rw [hN n hn]
  exact mul_div_cancel₀ _ hmass.ne'


theorem traceSeedLength_basis_zero (hp : NonnegativePrimitiveDirection (1, 0)) :
    primitiveSeedLength modularGeneratorA modularGeneratorB (1, 0) hp = traceAxisLength := by
  have hseed : SeededFarey (1, 0) (0, 1) modularGeneratorA modularGeneratorB
      (1, 0) (0, 1) modularGeneratorA modularGeneratorB := .seed
  rw [primitiveSeedLength, primitiveSeedTrace, hseed.primitiveSeedMatrix_left]
  simp only [modular_generators_det_trace.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem traceSeedLength_basis_one (hp : NonnegativePrimitiveDirection (0, 1)) :
    primitiveSeedLength modularGeneratorA modularGeneratorB (0, 1) hp = traceAxisLength := by
  have hseed : SeededFarey (1, 0) (0, 1) modularGeneratorA modularGeneratorB
      (1, 0) (0, 1) modularGeneratorA modularGeneratorB := .seed
  rw [primitiveSeedLength, primitiveSeedTrace, hseed.primitiveSeedMatrix_right]
  simp only [modular_generators_det_trace.2.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem traceSeedLength_basis_sum (hp : NonnegativePrimitiveDirection (1, 1)) :
    primitiveSeedLength modularGeneratorA modularGeneratorB (1, 1) hp = traceAxisLength := by
  have hseed : SeededFarey (1, 0) (0, 1) modularGeneratorA modularGeneratorB
      (1, 0) (0, 1) modularGeneratorA modularGeneratorB := .seed
  have hdiag : SeededFarey (1, 0) (0, 1) modularGeneratorA modularGeneratorB
      (1, 0) (1, 1) modularGeneratorA (modularGeneratorA * modularGeneratorB) := by
    simpa using hseed.left
  rw [primitiveSeedLength, primitiveSeedTrace, hdiag.primitiveSeedMatrix_right]
  simp only [modular_generators_det_trace.2.2.2.2, Int.cast_ofNat, traceAxisLength]


theorem finiteTraceSeminorm_eventual_basis_zero (B : Module.Basis (Fin 2) ℝ E) :
    ∀ᶠ n : ℕ in atTop, finiteTraceSeminorm B n (B 0) = traceAxisLength := by
  let hp : NonnegativePrimitiveDirection (1, 0) := FareyHolonomy.seed.left_nonnegativePrimitive
  obtain ⟨N, hN⟩ := finiteTraceSeminorm_eventual_positive B (1, 0) hp
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero]
    using (hN n hn).trans (traceSeedLength_basis_zero hp)

theorem finiteTraceSeminorm_eventual_basis_one (B : Module.Basis (Fin 2) ℝ E) :
    ∀ᶠ n : ℕ in atTop, finiteTraceSeminorm B n (B 1) = traceAxisLength := by
  let hp : NonnegativePrimitiveDirection (0, 1) := FareyHolonomy.seed.right_nonnegativePrimitive
  obtain ⟨N, hN⟩ := finiteTraceSeminorm_eventual_positive B (0, 1) hp
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Int.cast_one, Int.cast_zero, one_smul, zero_smul, zero_add]
    using (hN n hn).trans (traceSeedLength_basis_one hp)

theorem finiteTraceSeminorm_eventual_basis_sum (B : Module.Basis (Fin 2) ℝ E) :
    ∀ᶠ n : ℕ in atTop, finiteTraceSeminorm B n (B 0 + B 1) = traceAxisLength := by
  have hp : NonnegativePrimitiveDirection (1, 1) := by
    simpa using FareyHolonomy.seed.left.right_nonnegativePrimitive
  obtain ⟨N, hN⟩ := finiteTraceSeminorm_eventual_positive B (1, 1) hp
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Int.cast_one, one_smul] using (hN n hn).trans (traceSeedLength_basis_sum hp)

/-- An actual nondegenerate group norm constructed from the trace data. -/
def traceGroupNorm (B : Module.Basis (Fin 2) ℝ E) : AddGroupNorm E :=
  antitoneInfGroupNorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) B
    traceAxisLength traceAxisLength traceAxisLength
    (finiteTraceSeminorm_eventual_basis_zero B) (finiteTraceSeminorm_eventual_basis_one B)
    (finiteTraceSeminorm_eventual_basis_sum B)
    (by linarith [traceAxisLength_pos]) (by linarith [traceAxisLength_pos])
    (by linarith [traceAxisLength_pos])

theorem traceGroupNorm_apply (B : Module.Basis (Fin 2) ℝ E) (x : E) :
    traceGroupNorm B x = ⨅ n : ℕ, finiteTraceSeminorm B n x := rfl

theorem traceGroupNorm_positive (B : Module.Basis (Fin 2) ℝ E)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    traceGroupNorm B ((p.1 : ℝ) • B 0 + (p.2 : ℝ) • B 1) =
      primitiveSeedLength modularGeneratorA modularGeneratorB p hp := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) _ = _
  apply antitoneInfSeminorm_eventual_value
  exact eventually_atTop.mpr (finiteTraceSeminorm_eventual_positive B p hp)

theorem traceGroupNorm_next (B : Module.Basis (Fin 2) ℝ E)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    traceGroupNorm B ((p.1 : ℝ) • B 1 + (p.2 : ℝ) • (-B 0)) =
      primitiveSeedLength modularGeneratorB modularGeneratorA.adjugate p hp := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) _ = _
  apply antitoneInfSeminorm_eventual_value
  exact eventually_atTop.mpr (finiteTraceSeminorm_eventual_next B p hp)

theorem traceGroupNorm_smul (B : Module.Basis (Fin 2) ℝ E) (a : ℝ) (x : E) :
    traceGroupNorm B (a • x) = |a| * traceGroupNorm B x := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) (a • x) =
    |a| * antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) x
  rw [map_smul_eq_mul, Real.norm_eq_abs]


@[simp] theorem traceGroupNorm_basis_zero (B : Module.Basis (Fin 2) ℝ E) :
    traceGroupNorm B (B 0) = traceAxisLength := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) _ = _
  exact antitoneInfSeminorm_eventual_value _ _ _ _ (finiteTraceSeminorm_eventual_basis_zero B)

@[simp] theorem traceGroupNorm_basis_one (B : Module.Basis (Fin 2) ℝ E) :
    traceGroupNorm B (B 1) = traceAxisLength := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) _ = _
  exact antitoneInfSeminorm_eventual_value _ _ _ _ (finiteTraceSeminorm_eventual_basis_one B)

@[simp] theorem traceGroupNorm_basis_sum (B : Module.Basis (Fin 2) ℝ E) :
    traceGroupNorm B (B 0 + B 1) = traceAxisLength := by
  change antitoneInfSeminorm (finiteTraceSeminorm B) (finiteTraceSeminorm_antitone B) _ = _
  exact antitoneInfSeminorm_eventual_value _ _ _ _ (finiteTraceSeminorm_eventual_basis_sum B)

end Markov
