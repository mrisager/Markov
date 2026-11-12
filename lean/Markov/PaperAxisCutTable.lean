import Markov.FiniteRealCutTable
import Markov.PaperAxisCutSet

/-! Constructed ordered finite original-side cuts of one actual metric period.
Every gap assertion is derived from the literal cut set and finite sorting.
No actual cell-label or cyclic-word classification is assumed here. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual interior cut times of the indicated actual metric period. -/
def paperAxisPeriodInteriorCuts (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : Set ℝ :=
  Ioo a (a + modularClosedGeodesicPeriod g) ∩ paperAxisSideCuts g hg

theorem paperAxisPeriodInteriorCuts_finite (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    (paperAxisPeriodInteriorCuts g hg a).Finite :=
  paperAxisSideCuts_finite_Ioo g hg a (a + modularClosedGeodesicPeriod g)

/-- The actual finite point set contains precisely the period endpoints and
all actual interior cuts. It is constructed without a partition witness. -/
def paperAxisPeriodCutPoints (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : Finset ℝ :=
  finiteRealCutPoints a (a + modularClosedGeodesicPeriod g)
    (paperAxisPeriodInteriorCuts g hg a) (paperAxisPeriodInteriorCuts_finite g hg a)

/-- The actual strictly ordered finite parameter table for one metric period. -/
def paperAxisPeriodCutTable (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Fin (paperAxisPeriodCutPoints g hg a).card ↪o ℝ :=
  finiteRealCutTable a (a + modularClosedGeodesicPeriod g)
    (paperAxisPeriodInteriorCuts g hg a) (paperAxisPeriodInteriorCuts_finite g hg a)

theorem paperAxisPeriodCutPoints_card_pos (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    0 < (paperAxisPeriodCutPoints g hg a).card :=
  finiteRealCutPoints_card_pos _ _ _ _

theorem paperAxisPeriodCutTable_strictMono (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    StrictMono (paperAxisPeriodCutTable g hg a) :=
  (paperAxisPeriodCutTable g hg a).strictMono

theorem paperAxisPeriodCutTable_range (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    range (paperAxisPeriodCutTable g hg a) = (paperAxisPeriodCutPoints g hg a : Set ℝ) :=
  finiteRealCutTable_range _ _ _ _

theorem paperAxisPeriodCutTable_bounds (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin (paperAxisPeriodCutPoints g hg a).card) :
    a ≤ paperAxisPeriodCutTable g hg a i ∧
      paperAxisPeriodCutTable g hg a i ≤ a + modularClosedGeodesicPeriod g :=
  finiteRealCutTable_bounds _ _ (lt_add_of_pos_right a (modularClosedGeodesicPeriod_pos g hg))
    _ _ (fun _ ht => ht.1) i

/-- The actual first/last values are the actual chosen metric period endpoints. -/
theorem paperAxisPeriodCutTable_endpoints (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    paperAxisPeriodCutTable g hg a ⟨0, paperAxisPeriodCutPoints_card_pos g hg a⟩ = a ∧
    paperAxisPeriodCutTable g hg a
      ⟨(paperAxisPeriodCutPoints g hg a).card - 1,
        Nat.sub_lt (paperAxisPeriodCutPoints_card_pos g hg a) (by decide)⟩ =
          a + modularClosedGeodesicPeriod g := by
  have hab : a < a + modularClosedGeodesicPeriod g :=
    lt_add_of_pos_right a (modularClosedGeodesicPeriod_pos g hg)
  exact ⟨finiteRealCutTable_first _ _ hab _ _ (fun _ ht => ht.1),
    finiteRealCutTable_last _ _ hab _ _ (fun _ ht => ht.1)⟩

/-- Every actual consecutive open table gap avoids EVERY original translated
side, not merely the already selected cell labels. -/
theorem paperAxisPeriodCutTable_gap_off_sides (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin (paperAxisPeriodCutPoints g hg a).card) (hij : j.val = i.val + 1)
    (x : ℝ) (hx : x ∈ Ioo (paperAxisPeriodCutTable g hg a i) (paperAxisPeriodCutTable g hg a j)) :
    x ∉ paperAxisSideCuts g hg := by
  intro hcut
  have ha : a < x := lt_of_le_of_lt (paperAxisPeriodCutTable_bounds g hg a i).1 hx.1
  have hb : x < a + modularClosedGeodesicPeriod g :=
    lt_of_lt_of_le hx.2 (paperAxisPeriodCutTable_bounds g hg a j).2
  exact finiteRealCutTable_gap_not_mem _ _ _ _ i j hij x hx ⟨⟨ha, hb⟩, hcut⟩

/-- Consecutive integer indices give a genuinely nonempty open real gap. -/
theorem paperAxisPeriodCutTable_gap_nonempty (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin (paperAxisPeriodCutPoints g hg a).card) (hij : j.val = i.val + 1) :
    (Ioo (paperAxisPeriodCutTable g hg a i) (paperAxisPeriodCutTable g hg a j)).Nonempty := by
  apply nonempty_Ioo.mpr
  apply paperAxisPeriodCutTable_strictMono g hg a
  change i.val < j.val
  omega

end Markov
