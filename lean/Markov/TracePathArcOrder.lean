import Markov.TraceBoundaryOpenArcs
import Mathlib.Topology.Connected.Basic

/-! Disjoint actual path arcs have ordered parameter intervals. Interval
overlap would produce a common actual path point. Within one traversal,
injectivity also gives the converse. Distinct connected components of the
same actual set are disjoint, so their nonempty path arcs are ordered. -/

noncomputable section
open Set
namespace Markov

/-- An interior parameter gives an actual point of the open path arc. -/
theorem traceBoundaryPath_mem_openArc (a b t : ℝ) (ht : t ∈ Ioo a b) :
    traceBoundaryPath t ∈ traceBoundaryOpenArc a b :=
  ⟨t, ht, rfl⟩

/-- Every nontrivial parameter interval has a nonempty actual path arc. -/
theorem traceBoundaryOpenArc_nonempty (a b : ℝ) (hab : a < b) :
    (traceBoundaryOpenArc a b).Nonempty := by
  refine ⟨traceBoundaryPath ((a + b) / 2), ?_⟩
  apply traceBoundaryPath_mem_openArc
  constructor <;> linarith

/-- If two actual open path arcs are disjoint, their nonempty parameter
intervals cannot overlap. This implication needs no traversal bounds. -/
theorem traceBoundaryOpenArc_parameters_ordered_of_disjoint
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hdisjoint : Disjoint (traceBoundaryOpenArc a b) (traceBoundaryOpenArc c d)) :
    b ≤ c ∨ d ≤ a := by
  by_contra horder
  push_neg at horder
  have hgap : max a c < min b d :=
    lt_min (max_lt hab horder.1) (max_lt horder.2 hcd)
  obtain ⟨t, hlow, hhigh⟩ := exists_between hgap
  have ht : t ∈ Ioo a b :=
    ⟨(le_max_left a c).trans_lt hlow, hhigh.trans_le (min_le_left b d)⟩
  have ht' : t ∈ Ioo c d :=
    ⟨(le_max_right a c).trans_lt hlow, hhigh.trans_le (min_le_right b d)⟩
  exact Set.disjoint_left.mp hdisjoint
    (traceBoundaryPath_mem_openArc a b t ht)
    (traceBoundaryPath_mem_openArc c d t ht')

/-- Within the single traversal, parameter order is equivalent to
disjointness of the actual nonempty open path arcs. -/
theorem traceBoundaryOpenArc_disjoint_iff_parameters_ordered
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4)
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 4) :
    Disjoint (traceBoundaryOpenArc a b) (traceBoundaryOpenArc c d) ↔ b ≤ c ∨ d ≤ a := by
  constructor
  · exact traceBoundaryOpenArc_parameters_ordered_of_disjoint a b c d hab hcd
  · intro horder
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ ⟨s, hs, he⟩
    have htperiod : t ∈ Ioc (0 : ℝ) 4 :=
      ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩
    have hsperiod : s ∈ Ioc (0 : ℝ) 4 :=
      ⟨hc.trans_lt hs.1, hs.2.le.trans hd⟩
    have hts : t = s := traceBoundaryPath_injOn_Ioc htperiod hsperiod he.symm
    rcases horder with hbc | hda
    · linarith [ht.2, hs.1]
    · linarith [hs.2, ht.1]

/-- Actual path arcs which are distinct connected components of the
same set are disjoint. No parameter uniqueness assumption is needed. -/
theorem traceBoundaryOpenArc_disjoint_of_distinct_components
    (S : Set TracePlane) (x y : TracePlane) (a b c d : ℝ)
    (hx : connectedComponentIn S x = traceBoundaryOpenArc a b)
    (hy : connectedComponentIn S y = traceBoundaryOpenArc c d)
    (hne : traceBoundaryOpenArc a b ≠ traceBoundaryOpenArc c d) :
    Disjoint (traceBoundaryOpenArc a b) (traceBoundaryOpenArc c d) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [← hx] at hz
  rw [← hy] at hz'
  apply hne
  calc
    traceBoundaryOpenArc a b = connectedComponentIn S x := hx.symm
    _ = connectedComponentIn S z := connectedComponentIn_eq hz
    _ = connectedComponentIn S y := (connectedComponentIn_eq hz').symm
    _ = traceBoundaryOpenArc c d := hy

/-- Distinct actual connected components, each represented by a nonempty
open path interval, have ordered parameter intervals. -/
theorem traceBoundaryOpenArc_parameters_ordered_of_distinct_components
    (S : Set TracePlane) (x y : TracePlane) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hx : connectedComponentIn S x = traceBoundaryOpenArc a b)
    (hy : connectedComponentIn S y = traceBoundaryOpenArc c d)
    (hne : traceBoundaryOpenArc a b ≠ traceBoundaryOpenArc c d) :
    b ≤ c ∨ d ≤ a :=
  traceBoundaryOpenArc_parameters_ordered_of_disjoint a b c d hab hcd
    (traceBoundaryOpenArc_disjoint_of_distinct_components S x y a b c d hx hy hne)

end Markov
