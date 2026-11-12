import Markov.TraceUnresolvedArcLength
import Markov.TraceClosedBoundaryArcs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Finite sums of actual component curve variations. The uniform constant
is the sum of the variations of the eight original signed radial pieces;
no Hausdorff-measure or packing hypothesis is used. -/

noncomputable section
open Set
open scoped ENNReal
namespace Markov

/-- Ordered, nonoverlapping closed subintervals use at most the variation
of their enclosing interval. Adjacent endpoints may be shared. -/
theorem eVariationOn_sum_Icc_le_of_ordered
    {E : Type*} [PseudoEMetricSpace E] {ι : Type*}
    (f : ℝ → E) (S : Finset ι) (a b : ι → ℝ) (L U : ℝ)
    (hbound : ∀ i ∈ S, L ≤ a i ∧ a i < b i ∧ b i ≤ U)
    (horder : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i ∈ S, eVariationOn f (Icc (a i) (b i))) ≤ eVariationOn f (Icc L U) := by
  classical
  induction S using Finset.strongInductionOn generalizing L U
  rename_i S ih
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image a hS
  have hleft (j : ι) (hj : j ∈ S.erase i) : b j ≤ a i := by
    have hjS := Finset.mem_of_mem_erase hj
    rcases horder j hjS i hi (Finset.ne_of_mem_erase hj) with hji | hij
    · exact hji
    · have haji := hmax j hjS
      linarith [(hbound i hi).2.1]
  have hsum : (∑ j ∈ S.erase i, eVariationOn f (Icc (a j) (b j))) ≤
      eVariationOn f (Icc L (a i)) := by
    apply ih (S.erase i) (Finset.erase_ssubset hi) L (a i)
    · intro j hj
      exact ⟨(hbound j (Finset.mem_of_mem_erase hj)).1,
        (hbound j (Finset.mem_of_mem_erase hj)).2.1, hleft j hj⟩
    · intro j hj k hk hjk
      exact horder j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
  calc
    _ = (∑ j ∈ S.erase i, eVariationOn f (Icc (a j) (b j))) +
        eVariationOn f (Icc (a i) (b i)) := (Finset.sum_erase_add S (fun j ↦ eVariationOn f (Icc (a j) (b j))) hi).symm
    _ ≤ eVariationOn f (Icc L (a i)) + eVariationOn f (Icc (a i) (b i)) :=
      add_le_add hsum le_rfl
    _ ≤ eVariationOn f (Icc L (a i) ∪ Icc (a i) (b i)) :=
      eVariationOn.add_le_union f (fun x hx y hy ↦ hx.2.trans hy.1)
    _ ≤ eVariationOn f (Icc L U) := by
      apply eVariationOn.mono
      intro x hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans ((hbound i hi).2.1.le.trans (hbound i hi).2.2)⟩
      · exact ⟨(hbound i hi).1.trans hx.1, hx.2.trans (hbound i hi).2.2⟩

/-- Disjoint actual slope arcs in the same original signed frame have
nonoverlapping parameter intervals. -/
theorem slopeBoundaryArc_parameters_ordered_of_disjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hd : Disjoint (slopeBoundaryArc B a b) (slopeBoundaryArc B c d)) :
    b ≤ c ∨ d ≤ a := by
  by_contra hn
  push_neg at hn
  have hgap : max a c < min b d := lt_min (max_lt hab hn.1) (max_lt hn.2 hcd)
  obtain ⟨t, hlow, hhigh⟩ := exists_between hgap
  have ht : t ∈ Ioo a b :=
    ⟨(le_max_left a c).trans_lt hlow, hhigh.trans_le (min_le_left b d)⟩
  have ht' : t ∈ Ioo c d :=
    ⟨(le_max_right a c).trans_lt hlow, hhigh.trans_le (min_le_right b d)⟩
  apply Set.disjoint_left.mp hd
  · rw [← radialBasisSection_image_Ioo]
    exact ⟨t, ht, rfl⟩
  · rw [← radialBasisSection_image_Ioo]
    exact ⟨t, ht', rfl⟩

/-- Actual total curve variation of the eight signed radial boundary pieces. -/
def traceSignedBoundaryVariation : ℝ≥0∞ :=
  ∑ k : Fin 8, eVariationOn (signedTraceEuclideanRadialSection k) (Icc (0 : ℝ) 1)

theorem signedTraceEuclideanRadialSection_unit_variation_ne_top (k : Fin 8) :
    eVariationOn (signedTraceEuclideanRadialSection k) (Icc (0 : ℝ) 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness)
    (signedTraceEuclideanRadialSection_eVariationOn_le k 0 1 (by norm_num)
      (by norm_num) (by norm_num))

theorem traceSignedBoundaryVariation_ne_top : traceSignedBoundaryVariation ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro k _
  exact signedTraceEuclideanRadialSection_unit_variation_ne_top k

/-- A positive finite real constant built only from actual curve variation. -/
def traceComponentVariationConstant : ℝ := traceSignedBoundaryVariation.toReal + 1

theorem traceComponentVariationConstant_pos : 0 < traceComponentVariationConstant := by
  dsimp [traceComponentVariationConstant]
  positivity

/-- A finite disjoint family of actual signed cutoff arcs uses no more than
the total variation of the eight original signed radial boundary pieces. -/
theorem signedTraceCutoffArcLength_sum_le
    {ι : Type*} (S : Finset ι) (n : ℕ) (k : ι → Fin 8) (u v : ι → ℤ × ℤ)
    (hcon : ∀ i ∈ S, ConsecutiveCutoffSlopes n (u i) (v i))
    (hdis : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (slopeBoundaryArc (signedSectorBasis traceBasis (k i))
        (cutoffSlope (u i)) (cutoffSlope (v i)))
        (slopeBoundaryArc (signedSectorBasis traceBasis (k j))
          (cutoffSlope (u j)) (cutoffSlope (v j)))) :
    (∑ i ∈ S, signedTraceCutoffArcLength (k i) (u i) (v i)) ≤
      traceSignedBoundaryVariation := by
  classical
  rw [← Finset.sum_fiberwise S k]
  apply Finset.sum_le_sum
  intro q _
  have heq : (∑ i ∈ S with k i = q, signedTraceCutoffArcLength (k i) (u i) (v i)) =
      ∑ i ∈ S with k i = q,
        eVariationOn (signedTraceEuclideanRadialSection q)
          (Icc (cutoffSlope (u i)) (cutoffSlope (v i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [signedTraceCutoffArcLength, (Finset.mem_filter.mp hi).2]
  rw [heq]
  apply eVariationOn_sum_Icc_le_of_ordered _ _ _ _ 0 1
  · intro i hi
    have h := hcon i (Finset.mem_filter.mp hi).1
    exact ⟨(cutoffSlope_mem_Icc n (u i) h.1).1,
      ((consecutiveCutoffSlopes_iff_slope n (u i) (v i)).mp h).2.2.1,
      (cutoffSlope_mem_Icc n (v i) h.2.1).2⟩
  · intro i hi j hj hij
    have hiS := (Finset.mem_filter.mp hi).1
    have hjS := (Finset.mem_filter.mp hj).1
    have hd := hdis i hiS j hjS hij
    rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2] at hd
    exact slopeBoundaryArc_parameters_ordered_of_disjoint _ _ _ _ _
      (((consecutiveCutoffSlopes_iff_slope n (u i) (v i)).mp (hcon i hiS)).2.2.1)
      (((consecutiveCutoffSlopes_iff_slope n (u j) (v j)).mp (hcon j hjS)).2.2.1) hd

/-- The corresponding finite real variation sum is bounded by one positive
constant independent of the cutoff or the chosen finite component family. -/
theorem signedTraceCutoffArcLength_toReal_sum_le
    {ι : Type*} (S : Finset ι) (n : ℕ) (k : ι → Fin 8) (u v : ι → ℤ × ℤ)
    (hcon : ∀ i ∈ S, ConsecutiveCutoffSlopes n (u i) (v i))
    (hdis : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (slopeBoundaryArc (signedSectorBasis traceBasis (k i))
        (cutoffSlope (u i)) (cutoffSlope (v i)))
        (slopeBoundaryArc (signedSectorBasis traceBasis (k j))
          (cutoffSlope (u j)) (cutoffSlope (v j)))) :
    (∑ i ∈ S, (signedTraceCutoffArcLength (k i) (u i) (v i)).toReal) ≤
      traceComponentVariationConstant := by
  have hfinite : ∀ i ∈ S, signedTraceCutoffArcLength (k i) (u i) (v i) ≠ ⊤ := by
    intro i hi
    exact signedTraceCutoffArcLength_ne_top n (k i) (u i) (v i) (hcon i hi)
  have h := ENNReal.toReal_mono traceSignedBoundaryVariation_ne_top
    (signedTraceCutoffArcLength_sum_le S n k u v hcon hdis)
  rw [ENNReal.toReal_sum hfinite] at h
  exact h.trans (by dsimp [traceComponentVariationConstant]; linarith)

/-- Distinct connected components of the actual uncut boundary are disjoint,
so their signed radial variations have the same uniform finite sum bound. -/
theorem trace_actual_component_variation_sum_le
    {ι : Type*} (S : Finset ι) (H : ℝ) (k : ι → Fin 8) (u v : ι → ℤ × ℤ)
    (x : ι → TracePlane)
    (hcon : ∀ i ∈ S, ConsecutiveCutoffSlopes ⌊H⌋₊ (u i) (v i))
    (hcomp : ∀ i ∈ S, connectedComponentIn (traceUncutBoundary H) (x i) =
      slopeBoundaryArc (signedSectorBasis traceBasis (k i))
        (cutoffSlope (u i)) (cutoffSlope (v i)))
    (hne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      connectedComponentIn (traceUncutBoundary H) (x i) ≠
        connectedComponentIn (traceUncutBoundary H) (x j)) :
    (∑ i ∈ S, (signedTraceCutoffArcLength (k i) (u i) (v i)).toReal) ≤
      traceComponentVariationConstant := by
  apply signedTraceCutoffArcLength_toReal_sum_le S ⌊H⌋₊ k u v hcon
  intro i hi j hj hij
  rw [← hcomp i hi, ← hcomp j hj]
  apply Set.disjoint_left.mpr
  intro z hz hz'
  apply hne i hi j hj hij
  exact (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm

/-- The selected unresolved lengths themselves have a uniform finite sum
whenever the selected actual components are pairwise distinct. -/
theorem traceUnresolvedArcLength_sum_le_of_distinct_components
    (S : Finset (ℤ × ℤ)) (K H η : ℝ) (hH : 1 ≤ H)
    (hunresolved : ∀ d ∈ S, IsTraceUnresolved d K H η)
    (hdistinct : ∀ d ∈ S, ∀ e ∈ S, d ≠ e →
      traceUnresolvedComponent d K H η ≠ traceUnresolvedComponent e K H η) :
    (∑ d ∈ S, traceUnresolvedArcLength d K H η) ≤ traceComponentVariationConstant := by
  classical
  let a (d : S) : TraceUnresolvedComponentData d.val H η :=
    traceUnresolvedComponentData d.val K H η ⟨hunresolved d.val d.property, hH⟩
  have hchosen (d : S) : traceUnresolvedComponent d.val K H η =
      slopeBoundaryArc (signedSectorBasis traceBasis (a d).sector)
        (cutoffSlope (a d).left) (cutoffSlope (a d).right) := by
    simp only [traceUnresolvedComponent,
      dif_pos (show IsTraceUnresolved d.val K H η ∧ 1 ≤ H from
        ⟨hunresolved d.val d.property, hH⟩)]
    rfl
  have hlength (d : S) : traceUnresolvedArcLength d.val K H η =
      (signedTraceCutoffArcLength (a d).sector (a d).left (a d).right).toReal := by
    simp only [traceUnresolvedArcLength,
      dif_pos (show IsTraceUnresolved d.val K H η ∧ 1 ≤ H from
        ⟨hunresolved d.val d.property, hH⟩)]
    rfl
  have hsum := trace_actual_component_variation_sum_le
    (Finset.univ : Finset S) H (fun d ↦ (a d).sector)
    (fun d ↦ (a d).left) (fun d ↦ (a d).right) (fun d ↦ (a d).basepoint)
    (fun d _ ↦ (a d).consecutive) (fun d _ ↦ (a d).component_eq)
    (by
      intro d _ e _ hde
      rw [(a d).component_eq, (a e).component_eq, ← hchosen d, ← hchosen e]
      exact hdistinct d.val d.property e.val e.property (fun he ↦ hde (Subtype.ext he)))
  simp_rw [← hlength] at hsum
  rw [Finset.sum_coe_sort S (fun d : ℤ × ℤ ↦ traceUnresolvedArcLength d K H η)] at hsum
  exact hsum

end Markov
