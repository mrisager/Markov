import T1PrimitiveOrbitBijection

/-! The exact paper count identity, now for the actual ordered positive
Markov triples and the actual primitive geometric lattice count, including
both exceptional orbits. No orbit-count input is assumed. -/
noncomputable section
open Filter
namespace Markov

theorem t1_primitiveOrbitDomain_card (x : ℝ) (hx : 2 ≤ x) :
    Nat.card (t1_primitiveOrbitDomain x) =
      12 * t1_geometricSectorCount (t1_markovLength x) + 12 := by
  have hR : 0 < t1_markovLength x := t1_markovLength_pos x (by linarith)
  letI : Fintype (t1_geometricSectorSet (t1_markovLength x)) :=
    (t1_geometricSectorSet_finite _ hR).fintype
  have h6 : Nat.card (Fin 6) = 6 := by simp [Nat.card_eq_fintype_card]
  have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have hs : Nat.card (t1_geometricSectorSet (t1_markovLength x)) =
      t1_geometricSectorCount (t1_markovLength x) := Nat.card_coe_set_eq _
  have hb : Nat.card {p : ℤ × ℤ // p ∈ t1_boundaryOrbitFinset} = 12 := by
    change Nat.card t1_boundaryOrbitFinset = 12
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,t1_boundaryOrbitFinset_card]
  change Nat.card ((Fin 6 × Bool × t1_geometricSectorSet (t1_markovLength x)) ⊕
    {p : ℤ × ℤ // p ∈ t1_boundaryOrbitFinset}) = _
  rw [Nat.card_sum,Nat.card_prod,Nat.card_prod,h6,h2,hs,hb]
  omega

theorem t1_geometricPrimitiveCount_sector_decomposition (x : ℝ) (hx : 2 ≤ x) :
    t1_geometricPrimitiveCount (t1_markovLength x) =
      12 * t1_geometricSectorCount (t1_markovLength x) + 12 := by
  have he := Nat.card_congr (t1_primitiveOrbitEquiv x hx)
  have he' : Nat.card (t1_primitiveOrbitDomain x) =
      t1_geometricPrimitiveCount (t1_markovLength x) := by
    simpa only [Nat.card_coe_set_eq,t1_geometricPrimitiveCount] using he
  exact he'.symm.trans (t1_primitiveOrbitDomain_card x hx)

theorem t1_actual_markov_primitive_nat_identity (x : ℝ) (hx : 2 ≤ x) :
    t1_geometricPrimitiveCount (t1_markovLength x) + 12 = 12 * countNat ⌊x⌋₊ := by
  rw [t1_geometricPrimitiveCount_sector_decomposition x hx]
  have hs := t1_geometricSectorCount_add_two x hx
  omega

theorem t1_actual_markov_primitive_identity (x : ℝ) (hx : 2 ≤ x) :
    count x = (t1_geometricPrimitiveCount (t1_markovLength x) : ℝ) / 12 + 1 := by
  have hn := t1_actual_markov_primitive_nat_identity x hx
  have hr : (t1_geometricPrimitiveCount (t1_markovLength x) : ℝ) + 12 =
      12 * (countNat ⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  unfold count
  linarith

theorem t1_actual_markov_primitive_identity_eventually :
    ∀ᶠ x : ℝ in atTop,
      count x = (t1_geometricPrimitiveCount (t1_markovLength x) : ℝ) / 12 + 1 := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact t1_actual_markov_primitive_identity x hx

def t1_primitiveLeadingCoefficient : ℝ := 6 * modularMcShaneRivinArea / Real.pi^2

def t1_markovLeadingCoefficient : ℝ := 2 * modularMcShaneRivinArea / Real.pi^2

theorem t1_markovLeadingCoefficient_pos : 0 < t1_markovLeadingCoefficient :=
  div_pos (mul_pos (by norm_num) modularMcShaneRivinArea_pos) (sq_pos_of_pos Real.pi_pos)

theorem t1_leadingCoefficient_div_three :
    t1_primitiveLeadingCoefficient / 3 = t1_markovLeadingCoefficient := by
  unfold t1_primitiveLeadingCoefficient t1_markovLeadingCoefficient
  ring

end Markov
