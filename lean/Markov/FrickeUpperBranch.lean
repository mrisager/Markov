import Markov.SeededFarey
import Markov.QuadrantSeeds

/-! The actual Farey moves stay on the increasing product-trace branch.
Every descendant product trace dominates both factor traces, and every
noninitial pair is on the upper branch of the Fricke quadratic. -/

namespace Markov

private theorem fricke_move_dominates_and_upper (a b c : ℤ)
    (ha : 3 ≤ a) (hc : 0 ≤ c) (hbc : b ≤ c) :
    c ≤ a * c - b ∧ a * c ≤ 2 * (a * c - b) := by
  have hm : 0 ≤ (a - 3) * c := mul_nonneg (by linarith) hc
  constructor <;> nlinarith

/-- A seed whose product trace dominates both factor traces retains this
ordering under every actual seeded Farey move. -/
theorem SeededFarey.product_trace_ge_factors
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0)
    (hord0 : M0.trace ≤ (M0 * N0).trace ∧ N0.trace ≤ (M0 * N0).trace)
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    M.trace ≤ (M * N).trace ∧ N.trace ≤ (M * N).trace := by
  induction h with
  | seed => exact hord0
  | @left u v M N h ih =>
    have hp := h.positiveFrickePair hp0
    have hm := (fricke_move_dominates_and_upper M.trace N.trace (M * N).trace
      hp.trace_left (by linarith [hp.trace_product]) ih.2).1
    rw [matrix_trace_left_move M N hp.det_left]
    exact ⟨ih.1.trans hm, hm⟩
  | @right u v M N h ih =>
    have hp := h.positiveFrickePair hp0
    have hm := (fricke_move_dominates_and_upper N.trace M.trace (M * N).trace
      hp.trace_right (by linarith [hp.trace_product]) ih.1).1
    rw [matrix_trace_right_move M N hp.det_right]
    exact ⟨hm, ih.2.trans hm⟩

/-- Maximum form of the factor/product trace ordering. -/
theorem SeededFarey.product_trace_ge_max
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0)
    (hord0 : max M0.trace N0.trace ≤ (M0 * N0).trace)
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    max M.trace N.trace ≤ (M * N).trace := by
  exact max_le (h.product_trace_ge_factors hp0
    ⟨(le_max_left _ _).trans hord0, (le_max_right _ _).trans hord0⟩).1
    (h.product_trace_ge_factors hp0
      ⟨(le_max_left _ _).trans hord0, (le_max_right _ _).trans hord0⟩).2

/-- Apart from the initial direction pair, the actual product trace lies
on the upper branch: twice the product trace exceeds the two factor traces'
product. The exceptional seed is explicitly retained. -/
theorem SeededFarey.upper_branch_or_seed
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0)
    (hord0 : M0.trace ≤ (M0 * N0).trace ∧ N0.trace ≤ (M0 * N0).trace)
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    (u = u0 ∧ v = v0) ∨ M.trace * N.trace ≤ 2 * (M * N).trace := by
  cases h with
  | seed => exact Or.inl ⟨rfl, rfl⟩
  | @left u v M N h =>
    have hp := h.positiveFrickePair hp0
    have hord := h.product_trace_ge_factors hp0 hord0
    right
    rw [matrix_trace_left_move M N hp.det_left]
    exact (fricke_move_dominates_and_upper M.trace N.trace (M * N).trace
      hp.trace_left (by linarith [hp.trace_product]) hord.2).2
  | @right u v M N h =>
    have hp := h.positiveFrickePair hp0
    have hord := h.product_trace_ge_factors hp0 hord0
    right
    rw [matrix_trace_right_move M N hp.det_right]
    have hm := (fricke_move_dominates_and_upper N.trace M.trace (M * N).trace
      hp.trace_right (by linarith [hp.trace_product]) hord.1).2
    nlinarith only [hm]

/-- The explicit nonseed version of the upper-branch theorem. -/
theorem SeededFarey.upper_branch_of_not_seed
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0)
    (hord0 : M0.trace ≤ (M0 * N0).trace ∧ N0.trace ≤ (M0 * N0).trace)
    (h : SeededFarey u0 v0 M0 N0 u v M N) (hne : (u, v) ≠ (u0, v0)) :
    M.trace * N.trace ≤ 2 * (M * N).trace := by
  rcases h.upper_branch_or_seed hp0 hord0 with ⟨hu, hv⟩ | hb
  · exact (hne (Prod.ext hu hv)).elim
  · exact hb

/-- The ordering hypothesis is checked for every actual quadrant seed. -/
theorem quadrantSeed_product_trace_ge_factors (k : Fin 4) :
    (quadrantSeedMatrices k).1.trace ≤
        ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace ∧
      (quadrantSeedMatrices k).2.trace ≤
        ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace := by
  rw [(quadrantSeed_trace_triple k).1, (quadrantSeed_trace_triple k).2.1,
    (quadrantSeed_trace_triple k).2.2]
  split_ifs <;> norm_num

/-- Both factor traces are bounded by the product trace in every actual
quadrant Farey pair. -/
theorem SeededFarey.quadrant_product_trace_ge_factors (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    M.trace ≤ (M * N).trace ∧ N.trace ≤ (M * N).trace :=
  h.product_trace_ge_factors (quadrantSeed_positiveFrickePair k)
    (quadrantSeed_product_trace_ge_factors k)

/-- Maximum form for the actual quadrant words. -/
theorem SeededFarey.quadrant_product_trace_ge_max (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    max M.trace N.trace ≤ (M * N).trace :=
  max_le (h.quadrant_product_trace_ge_factors k).1
    (h.quadrant_product_trace_ge_factors k).2

/-- Every nonseed actual quadrant word lies on the upper Fricke branch. -/
theorem SeededFarey.quadrant_upper_branch_of_not_seed (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hne : (u, v) ≠ ((quadrantSeedDirections k).1, (quadrantSeedDirections k).2)) :
    M.trace * N.trace ≤ 2 * (M * N).trace :=
  h.upper_branch_of_not_seed (quadrantSeed_positiveFrickePair k)
    (quadrantSeed_product_trace_ge_factors k) hne

/-- The sum of the original seed labels has height exactly one. -/
theorem quadrantSeed_sum_height (k : Fin 4) :
    intHeight ((quadrantSeedDirections k).1 + (quadrantSeedDirections k).2) = 1 := by
  fin_cases k <;> norm_num [quadrantSeedDirections, intHeight]

/-- Every actual quadrant birth above height one uses the upper branch of
the Fricke quadratic, with no numerical trace-ordering hypothesis remaining. -/
theorem SeededFarey.quadrant_upper_branch_of_height (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    M.trace * N.trace ≤ 2 * (M * N).trace := by
  apply h.quadrant_upper_branch_of_not_seed k
  rintro he
  have hu := congrArg Prod.fst he
  have hv := congrArg Prod.snd he
  dsimp only at hu hv
  rw [hu, hv, quadrantSeed_sum_height] at hheight
  linarith

end Markov
