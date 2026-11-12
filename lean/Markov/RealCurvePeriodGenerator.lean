import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic

noncomputable section
open Set Filter Topology
namespace Markov

/-- All real periods of a curve, with their actual additive subgroup structure. -/
def realCurvePeriodSubgroup {X : Type*} (c : ℝ → X) : AddSubgroup ℝ where
  carrier := {T | Function.Periodic c T}
  zero_mem' := by intro t; simp
  add_mem' hT hU := hT.add_period hU
  neg_mem' hT := hT.neg

/-- Membership in the period group is literal function periodicity. -/
theorem realCurvePeriodSubgroup_mem_iff {X : Type*} (c : ℝ → X) (T : ℝ) :
    T ∈ realCurvePeriodSubgroup c ↔ Function.Periodic c T := Iff.rfl

/-- Injectivity on one neighborhood of zero isolates zero in the period group. -/
theorem realCurvePeriodSubgroup_isolated_zero {X : Type*} (c : ℝ → X)
    (hinj : ∃ U ∈ 𝓝 (0 : ℝ), Set.InjOn c U) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (realCurvePeriodSubgroup c : Set ℝ) (Set.Ioo 0 r) := by
  obtain ⟨U, hU, hUc⟩ := hinj
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, Set.disjoint_left.mpr ?_⟩
  intro T hT hTr
  have hzero : (0 : ℝ) ∈ U := hrU (by simpa using hr)
  have hTin : T ∈ U := hrU (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hTr.1] using hTr.2)
  have hTeq : T = 0 := hUc hTin hzero (Function.Periodic.eq hT)
  exact hTr.1.ne' hTeq

/-- A locally injective periodic real curve has an actual least positive period;
its full period subgroup is cyclic, and the given positive period is a positive
natural multiple of that least period. Only injectivity near zero is needed. -/
theorem realCurvePeriodGenerator_of_injOn_nhds {X : Type*} (c : ℝ → X)
    (hinj : ∃ U ∈ 𝓝 (0 : ℝ), Set.InjOn c U) {L : ℝ}
    (hL : 0 < L) (hper : Function.Periodic c L) :
    ∃ T0 : ℝ, 0 < T0 ∧ Function.Periodic c T0 ∧
      (∀ T : ℝ, 0 < T → Function.Periodic c T → T0 ≤ T) ∧
      realCurvePeriodSubgroup c = AddSubgroup.zmultiples T0 ∧
      ∃ n : ℕ, 0 < n ∧ L = (n : ℝ) * T0 := by
  have hbot : realCurvePeriodSubgroup c ≠ ⊥ := by
    intro h
    have hm : L ∈ (⊥ : AddSubgroup ℝ) := h ▸ hper
    have hzero : L = 0 := AddSubgroup.mem_bot.mp hm
    exact hL.ne' hzero
  obtain ⟨r, hr, hiso⟩ := realCurvePeriodSubgroup_isolated_zero c hinj
  obtain ⟨T0, hleast⟩ := AddSubgroup.exists_isLeast_pos hbot hr hiso
  have hcyc : realCurvePeriodSubgroup c = AddSubgroup.closure {T0} :=
    AddSubgroup.cyclic_of_min hleast
  have hgen : realCurvePeriodSubgroup c = AddSubgroup.zmultiples T0 := by
    rw [AddSubgroup.zmultiples_eq_closure]
    exact hcyc
  have hLmem : L ∈ AddSubgroup.closure {T0} := hcyc ▸ hper
  obtain ⟨k, hk⟩ := AddSubgroup.mem_closure_singleton.mp hLmem
  have hkmul : (k : ℝ) * T0 = L := by simpa only [zsmul_eq_mul] using hk
  have hkpos_real : (0 : ℝ) < (k : ℝ) := by nlinarith [hleast.1.2]
  have hkpos : (0 : ℤ) < k := Int.cast_pos.mp hkpos_real
  lift k to ℕ using hkpos.le with n hn
  refine ⟨T0, hleast.1.2, hleast.1.1, ?_, hgen, n, ?_, ?_⟩
  · intro T hT hTc
    exact hleast.2 ⟨hTc, hT⟩
  · exact_mod_cast hkpos
  · simpa only [Int.cast_natCast] using hkmul.symm

/-- The usual topological local-injectivity hypothesis supplies the period generator. -/
theorem realCurvePeriodGenerator_of_isLocallyInjective {X : Type*} (c : ℝ → X)
    (hinj : IsLocallyInjective c) {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic c L) :
    ∃ T0 : ℝ, 0 < T0 ∧ Function.Periodic c T0 ∧
      (∀ T : ℝ, 0 < T → Function.Periodic c T → T0 ≤ T) ∧
      realCurvePeriodSubgroup c = AddSubgroup.zmultiples T0 ∧
      ∃ n : ℕ, 0 < n ∧ L = (n : ℝ) * T0 :=
  realCurvePeriodGenerator_of_injOn_nhds c
    ((isLocallyInjective_iff_nhds.mp hinj) 0) hL hper

/-- Local equality of distances gives the exact injectivity needed for the
least-period theorem, without any assumed discreteness of periods. -/
theorem realCurvePeriodGenerator_of_local_dist_eq {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X)
    (hlocal : ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Metric.ball (0 : ℝ) r,
      ∀ u ∈ Metric.ball (0 : ℝ) r, dist (c s) (c u) = dist s u)
    {L : ℝ} (hL : 0 < L) (hper : Function.Periodic c L) :
    ∃ T0 : ℝ, 0 < T0 ∧ Function.Periodic c T0 ∧
      (∀ T : ℝ, 0 < T → Function.Periodic c T → T0 ≤ T) ∧
      realCurvePeriodSubgroup c = AddSubgroup.zmultiples T0 ∧
      ∃ n : ℕ, 0 < n ∧ L = (n : ℝ) * T0 := by
  obtain ⟨r, hr, hd⟩ := hlocal
  apply realCurvePeriodGenerator_of_injOn_nhds c ?_ hL hper
  refine ⟨Metric.ball (0 : ℝ) r, Metric.ball_mem_nhds 0 hr, ?_⟩
  intro s hs u hu hsu
  apply dist_eq_zero.mp
  rw [← hd s hs u hu, hsu, dist_self]

end Markov
