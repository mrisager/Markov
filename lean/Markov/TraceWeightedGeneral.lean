import Markov.TraceUnresolvedCutoffTransport
import Markov.CorollaryElevenParameters
import Markov.TraceComponentReciprocalSum
import Markov.TraceComponentVariationSum
import Markov.FiniteComponentMaxWeights

/-! Uniform weighted unresolved estimates for arbitrary external cutoffs.
Finite component maxima avoid any invariance assumption about selected
parametrizations of one component. -/

noncomputable section
open Set
namespace Markov

/-- The actual large-direction weighted sum is bounded using proved
component packing, inverse-length summation, and total component variation. -/
theorem trace_weighted_unresolved_annulus_bound :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ (A : Finset (ℤ × ℤ)) (L K H η : ℝ),
      0 < L → L ≤ K → 1 ≤ H → 0 ≤ η →
      (∀ d ∈ A, IsCoprime d.1 d.2) →
      (∀ d ∈ A, L ≤ intEuclidean d ∧ intEuclidean d ≤ K) →
      (∀ d ∈ A, IsTraceUnresolved d K H η) →
      (∑ d ∈ A, traceUnresolvedArcLength d K H η / intEuclidean d) ≤
        traceComponentVariationConstant *
          (1 / L + 2 * (M * Real.exp (-(κ * H)) + 2 * η) * K) := by
  classical
  obtain ⟨M, κ, hM, hκ, hrecip⟩ := trace_component_sum_inv_le_exp_width
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro A L K H η hL hLK hH hη hprimitive hannulus hunresolved
  have hK : 0 ≤ K := hL.le.trans hLK
  have hB : 0 ≤ 1 / L + 2 * (M * Real.exp (-(κ * H)) + 2 * η) * K := by positivity
  apply finite_sum_component_div_le_of_representative_sums A
    (fun d => traceUnresolvedComponent d K H η) intEuclidean
    (fun d => traceUnresolvedArcLength d K H η) _ traceComponentVariationConstant hB
    (fun d _ => traceUnresolvedArcLength_nonneg d K H η)
    (fun d hd => hL.trans_le (hannulus d hd).1)
  · intro j hj
    obtain ⟨d0, hd0, hd0comp⟩ := Finset.mem_image.mp hj
    obtain ⟨x, hx, _k, _u, _v, _hcon, hxcomp, _hdesc, _hmem, _hfin, _hlen⟩ :=
      traceUnresolvedArcLength_spec d0 K H η (hunresolved d0 hd0) hH
    apply hrecip (A.filter fun d => traceUnresolvedComponent d K H η = j)
      L K H η hL hLK hH hη x hx
    · intro d hd
      exact hprimitive d (Finset.mem_filter.mp hd).1
    · intro d hd
      exact hannulus d (Finset.mem_filter.mp hd).1
    · intro d hd
      obtain ⟨hdA, hdcomp⟩ := Finset.mem_filter.mp hd
      obtain ⟨_x, _hx, _k, _u, _v, _hcon, _hxcomp, _hdesc, hmem, _hfin, _hlen⟩ :=
        traceUnresolvedArcLength_spec d K H η (hunresolved d hdA) hH
      rw [hdcomp, ← hd0comp, ← hxcomp] at hmem
      exact hmem
  · intro T hTA hinj
    apply traceUnresolvedArcLength_sum_le_of_distinct_components T K H η hH
      (fun d hd => hunresolved d (hTA hd))
    intro d hd e he hde hcomp
    exact hde (hinj hd he hcomp)

/-- The actual full weighted unresolved sum, uniformly for every external
radius `K ≥ 1`. The positive constants depend only on the constructed body. -/
theorem trace_weighted_unresolved_general :
    ∃ C c H0 : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ H0 ∧
      ∀ (K H ε η : ℝ), 1 ≤ K → H0 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      (∑ d ∈ primitiveUnresolvedUpTo K H η K,
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤
          C * (1 / (H * Real.sqrt H) + K * Real.exp (-(c * H))) := by
  classical
  obtain ⟨D, Cs, hD, hCs, hsmall⟩ := trace_unresolved_small_weighted_bound_of_split_cutoff
  obtain ⟨M, κ, hM, hκ, hannulus⟩ := trace_weighted_unresolved_annulus_bound
  let V := traceComponentVariationConstant
  have hV : 0 < V := traceComponentVariationConstant_pos
  let a := 2 * traceAxisLength
  have ha : 0 < a := mul_pos (by norm_num) traceAxisLength_pos
  let c := min κ a
  have hc : 0 < c := lt_min hκ ha
  let B := 2 * V * (M + traceCornerLowerConstant)
  have hcorner : 0 < traceCornerLowerConstant := traceCornerLowerConstant_pos
  have hB : 0 ≤ B := by positivity
  let C := Cs + V + B
  have hC : 0 < C := by positivity
  let H0 := (4 * D + 1) ^ 2 + 1
  have hH0 : 1 ≤ H0 := by dsimp [H0]; nlinarith [sq_nonneg (4 * D + 1)]
  refine ⟨C, c, H0, hC, hc, hH0, ?_⟩
  intro K H ε η hK hH hε hη hbasic
  have hHone : 1 ≤ H := hH0.trans hH
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hHone
  have hlarge : (4 * D + 1) ^ 2 ≤ H := by dsimp [H0] at hH; linarith
  let L := H * Real.sqrt H
  have hLone : 1 ≤ L := corollary11_split_radius_one_le H hHone
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  let U := primitiveUnresolvedUpTo K H η K
  have hsmallbound :
      (∑ d ∈ U.filter (fun d => intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤ Cs / L :=
    hsmall K L H ε η hLone hHone hε hη hbasic
      (corollary11_split_log_cutoff D H hD.le hHone hlarge)
  have hlargebound :
      (∑ d ∈ U.filter (fun d => ¬ intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤
      V * (1 / L + 2 * (M * Real.exp (-(κ * H)) + 2 * η) * K) := by
    by_cases hLK : L ≤ K
    · apply hannulus (U.filter (fun d => ¬ intEuclidean d ≤ L)) L K H η
        hLp hLK hHone hη.le
      · intro d hd
        exact ((mem_primitiveUnresolvedUpTo K H η K d).mp (Finset.mem_filter.mp hd).1).1
      · intro d hd
        have hm := (mem_primitiveUnresolvedUpTo K H η K d).mp (Finset.mem_filter.mp hd).1
        exact ⟨(lt_of_not_ge (Finset.mem_filter.mp hd).2).le, hm.2.1⟩
      · intro d hd
        exact ((mem_primitiveUnresolvedUpTo K H η K d).mp (Finset.mem_filter.mp hd).1).2.2
    · have hempty : U.filter (fun d => ¬ intEuclidean d ≤ L) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        have hm := (mem_primitiveUnresolvedUpTo K H η K d).mp (Finset.mem_filter.mp hd).1
        exact (Finset.mem_filter.mp hd).2 (hm.2.1.trans (le_of_not_ge hLK))
      rw [hempty, Finset.sum_empty]
      positivity
  have heta : 2 * η ≤ traceCornerLowerConstant * Real.exp (-(a * H)) := by
    have hh : (2 + ε) * η ≤ traceCornerLowerConstant * Real.exp (-(a * H)) := by
      simpa only [a, neg_mul] using hbasic
    nlinarith [mul_pos hε hη]
  have hκexp : Real.exp (-(κ * H)) ≤ Real.exp (-(c * H)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left κ a) hHp.le)
  have haexp : Real.exp (-(a * H)) ≤ Real.exp (-(c * H)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right κ a) hHp.le)
  have hwidth : M * Real.exp (-(κ * H)) + 2 * η ≤
      (M + traceCornerLowerConstant) * Real.exp (-(c * H)) := by
    calc
      _ ≤ M * Real.exp (-(κ * H)) + traceCornerLowerConstant * Real.exp (-(a * H)) :=
        add_le_add le_rfl heta
      _ ≤ M * Real.exp (-(c * H)) + traceCornerLowerConstant * Real.exp (-(c * H)) :=
        add_le_add (mul_le_mul_of_nonneg_left hκexp hM.le)
          (mul_le_mul_of_nonneg_left haexp traceCornerLowerConstant_pos.le)
      _ = _ := by ring
  have hlargefinal :
      (∑ d ∈ U.filter (fun d => ¬ intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤
      V / L + B * (K * Real.exp (-(c * H))) := by
    apply hlargebound.trans
    calc
      _ ≤ V * (1 / L + 2 * ((M + traceCornerLowerConstant) * Real.exp (-(c * H))) * K) := by
        gcongr
      _ = _ := by dsimp [B]; ring
  have hsplit : (∑ d ∈ U, traceUnresolvedArcLength d K H η / intEuclidean d) =
      (∑ d ∈ U.filter (fun d => intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) +
      (∑ d ∈ U.filter (fun d => ¬ intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) :=
    (Finset.sum_filter_add_sum_filter_not U (fun d => intEuclidean d ≤ L) _).symm
  change (∑ d ∈ U, traceUnresolvedArcLength d K H η / intEuclidean d) ≤
    C * (1 / L + K * Real.exp (-(c * H)))
  rw [hsplit]
  calc
    _ ≤ Cs / L + (V / L + B * (K * Real.exp (-(c * H)))) :=
      add_le_add hsmallbound hlargefinal
    _ = (Cs + V) * (1 / L) + B * (K * Real.exp (-(c * H))) := by ring
    _ ≤ C * (1 / L) + C * (K * Real.exp (-(c * H))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    _ = _ := by ring

end Markov
