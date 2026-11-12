import T1FareyWordCoverage

/-! Actual word uniqueness in the half-quadrant, proved from integral
unimodular splits and the literal two child operations. -/
namespace Markov

private theorem t1_fareyWord_pair_cons_ne_nil (b : Bool) (w : List Bool) :
    t1_fareyWordDirections (b::w) ≠ t1_fareyWordDirections [] := by
  have hc := t1_fareyWord_cone w
  intro he
  have h11 := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.1) he
  have h12 := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.2) he
  have h21 := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.1) he
  have h22 := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.2) he
  cases b <;>
    simp only [t1_fareyWordDirections, Prod.fst_add, Prod.snd_add] at h11 h12 h21 h22 <;>
    omega

private theorem t1_fareyWord_left_right_disjoint (w v : List Bool) :
    t1_fareyWordDirections (false::w) ≠ t1_fareyWordDirections (true::v) := by
  have hw := t1_fareyWord_cone w
  have hv := t1_fareyWord_cone v
  intro he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  apply nonnegative_left_right_disjoint
    (t1_fareyWordDirections w).1 (t1_fareyWordDirections w).2
    (t1_fareyWordDirections v).1 (t1_fareyWordDirections v).2
    (by omega) (by omega) (by omega) (by omega) ?_ he1 he2
  intro hz
  have hz2 := congrArg Prod.snd hz
  change (t1_fareyWordDirections w).2.2 = 0 at hz2
  omega

theorem t1_fareyWordDirections_injective : Function.Injective t1_fareyWordDirections := by
  intro w
  induction w with
  | nil =>
    intro v he
    cases v with
    | nil => rfl
    | cons c v => exact (t1_fareyWord_pair_cons_ne_nil c v he.symm).elim
  | cons b w ih =>
    intro v he
    cases v with
    | nil => exact (t1_fareyWord_pair_cons_ne_nil b w he).elim
    | cons c v =>
      cases b <;> cases c
      · have hu := congrArg Prod.fst he
        have hs := congrArg Prod.snd he
        change (t1_fareyWordDirections w).1 = (t1_fareyWordDirections v).1 at hu
        change (t1_fareyWordDirections w).1 + (t1_fareyWordDirections w).2 =
          (t1_fareyWordDirections v).1 + (t1_fareyWordDirections v).2 at hs
        have hp : t1_fareyWordDirections w = t1_fareyWordDirections v := by
          apply Prod.ext hu
          rw [hu] at hs
          exact add_left_cancel hs
        exact congrArg (List.cons false) (ih hp)
      · exact (t1_fareyWord_left_right_disjoint w v he).elim
      · exact (t1_fareyWord_left_right_disjoint v w he.symm).elim
      · have hv := congrArg Prod.snd he
        have hs := congrArg Prod.fst he
        change (t1_fareyWordDirections w).2 = (t1_fareyWordDirections v).2 at hv
        change (t1_fareyWordDirections w).1 + (t1_fareyWordDirections w).2 =
          (t1_fareyWordDirections v).1 + (t1_fareyWordDirections v).2 at hs
        have hp : t1_fareyWordDirections w = t1_fareyWordDirections v := by
          apply Prod.ext ?_ hv
          rw [hv] at hs
          exact add_right_cancel hs
        exact congrArg (List.cons true) (ih hp)

theorem t1_fareyWordDirection_injective : Function.Injective t1_fareyWordDirection := by
  intro w v he
  have hw := t1_fareyWord_cone w
  have hv := t1_fareyWord_cone v
  have hsplit := unimodular_positive_sum_unique
    (t1_fareyWordDirections w).1 (t1_fareyWordDirections w).2
    (t1_fareyWordDirections v).1 (t1_fareyWordDirections v).2
    (by omega) (by omega) (by omega) (by omega)
    (t1_fareyWord_holonomy w).det_eq_one (t1_fareyWord_holonomy v).det_eq_one he
  exact t1_fareyWordDirections_injective (Prod.ext hsplit.1 hsplit.2)

theorem t1_strict_sector_exists_unique_farey_word (p : ℤ × ℤ)
    (hp2 : 0 < p.2) (hp12 : 2*p.2 < p.1) (hp : IsCoprime p.1 p.2) :
    ∃! w : List Bool, t1_fareyWordDirection w = p := by
  obtain ⟨w,hw⟩ := t1_strict_sector_exists_farey_word p hp2 hp12 hp
  exact ⟨w,hw,fun v hv => t1_fareyWordDirection_injective (hv.trans hw.symm)⟩

end Markov
