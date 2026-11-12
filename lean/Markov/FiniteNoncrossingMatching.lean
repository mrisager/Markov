import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Find

/-! A finite, ordered matching lemma. Noncrossing is stated literally as the
absence of interleaving matched pairs. No curve, region, bigon, or slide is
part of the statement. -/

namespace Markov

/-- No two pairs of the matching interleave in the linear order. The displayed
inequalities already imply that each pair is oriented from left to right. -/
def FinMatchingNoncrossing {N : ℕ} (m : Fin N → Fin N) : Prop :=
  ∀ a c, a < c → c < m a → m a < m c → False

/-- The matching carries every point strictly inside a matched interval to
another point strictly inside that interval. This follows from involutivity
and noncrossing, without an interval-closure hypothesis. -/
theorem finMatching_interval_closed {N : ℕ} (m : Fin N → Fin N)
    (hm : Function.Involutive m) (hnc : FinMatchingNoncrossing m)
    (a c : Fin N) (hac : a < c) (hcma : c < m a) :
    a < m c ∧ m c < m a := by
  constructor
  · by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
    · exact hnc (m c) a hlt (by simpa only [hm c] using hac)
        (by simpa only [hm c] using hcma)
    · have hca : c = m a := by
        simpa only [hm c] using congrArg m heq
      exact (ne_of_lt hcma) hca
  · by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
    · exact hnc a c hac hcma hlt
    · have hca : c = a := by
        simpa only [hm c, hm a] using (congrArg m heq).symm
      exact (ne_of_lt hac) hca.symm

/-- A nonempty finite fixed-point-free noncrossing involution matches two
consecutive underlying integer indices. The proof minimizes the positive gap
and derives closure of the interval from the previous theorem. -/
theorem finMatching_exists_consecutive {N : ℕ} (hN : 0 < N)
    (m : Fin N → Fin N) (hm : Function.Involutive m)
    (hfixed : ∀ a, m a ≠ a) (hnc : FinMatchingNoncrossing m) :
    ∃ a b : Fin N, m a = b ∧ a.val + 1 = b.val := by
  classical
  have hforward : ∃ a : Fin N, a < m a := by
    let a : Fin N := ⟨0, hN⟩
    rcases lt_or_gt_of_ne (hfixed a) with hlt | hgt
    · exact ⟨m a, by simpa only [hm a] using hlt⟩
    · exact ⟨a, hgt⟩
  have hex : ∃ d : ℕ, ∃ a : Fin N, a.val + d = (m a).val ∧ 0 < d := by
    obtain ⟨a, ha⟩ := hforward
    refine ⟨(m a).val - a.val, a, ?_, ?_⟩ <;> omega
  obtain ⟨a, hagap, hdpos⟩ := Nat.find_spec hex
  have hd : Nat.find hex = 1 := by
    by_contra hd
    have hlarge : 2 ≤ Nat.find hex := by omega
    have hcN : a.val + 1 < N := by have := (m a).isLt; omega
    let c : Fin N := ⟨a.val + 1, hcN⟩
    have hac : a < c := by change a.val < a.val + 1; omega
    have hcma : c < m a := by change a.val + 1 < (m a).val; omega
    obtain ⟨hamc, hmcma⟩ := finMatching_interval_closed m hm hnc a c hac hcma
    have hinside : ∃ b : Fin N, b < m b ∧ a < b ∧ m b < m a := by
      rcases lt_or_gt_of_ne (hfixed c) with hlt | hgt
      · exact ⟨m c, by simpa only [hm c] using hlt, hamc,
          by simpa only [hm c] using hcma⟩
      · exact ⟨c, hgt, hac, hmcma⟩
    obtain ⟨b, hb, hab, hbma⟩ := hinside
    have hbGap : ∃ x : Fin N,
        x.val + ((m b).val - b.val) = (m x).val ∧ 0 < (m b).val - b.val := by
      exact ⟨b, by omega, by omega⟩
    have hmin := Nat.find_min' hex hbGap
    change a.val < b.val at hab
    change (m b).val < (m a).val at hbma
    omega
  exact ⟨a, m a, rfl, by omega⟩

end Markov
