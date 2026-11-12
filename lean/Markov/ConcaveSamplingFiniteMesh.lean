import Markov.ConcaveSamplingCells
import Markov.SamplingMeshTelescoping

/-! The finite-mesh estimate in the concave sampling proof of Lemma 9. -/

open Set MeasureTheory

namespace Markov

/-- The discrepancy of a finite, shifted uniform mesh is controlled by the two
endpoint values at one mesh width. -/
theorem concave_sampling_finite_mesh_bound {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) (hc : ContinuousOn f (Icc 0 1))
    (h0 : f 0 = 0) (h1 : f 1 = 0) {h u : ℝ} {N : ℕ}
    (hh : 0 < h) (hhsmall : h < 1 / 8) (hN : 2 ≤ N)
    (hu : u ∈ Icc 0 h) (hlast : u + (N : ℝ) * h ∈ Icc (1 - h) 1) :
    |h * (∑ j ∈ Finset.Icc 0 N, f (u + (j : ℝ) * h)) -
        (∫ t in (0 : ℝ)..1, f t)| ≤ 7 * h * (f h + f (1 - h)) := by
  let x : ℕ → ℝ := fun j ↦ u + (j : ℝ) * h
  have hx0 : x 0 = u := by simp [x]
  have hx1 : x 1 = u + h := by simp [x]
  have hstep (j : ℕ) : x (j + 1) = x j + h := by
    dsimp [x]
    push_cast
    ring
  have hpred (j : ℕ) (hj : 1 ≤ j) : x (j - 1) = x j - h := by
    have key := hstep (j - 1)
    rw [Nat.sub_add_cancel hj] at key
    linarith
  have hmono : Monotone x := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp [x]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hij' hh.le) u
  have hxN : x N ∈ Icc (1 - h) 1 := hlast
  have hxmem (j : ℕ) (hj : j ≤ N) : x j ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?_, (hmono hj).trans hxN.2⟩
    dsimp [x]
    exact add_nonneg hu.1 (mul_nonneg (Nat.cast_nonneg j) hh.le)
  have hx1mem : x 1 ∈ Icc (0 : ℝ) 1 := hxmem 1 (by omega)
  have hxNmem : x N ∈ Icc (0 : ℝ) 1 := hxmem N le_rfl
  have hx01 : x 0 ∈ Icc (0 : ℝ) (2 * h) := by
    rw [hx0]
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hx11 : x 1 ∈ Icc (0 : ℝ) (2 * h) := by
    rw [hx1]
    constructor <;> linarith [hu.1, hu.2]
  have hxNm1 : x (N - 1) ∈ Icc (1 - 2 * h) 1 := by
    rw [hpred N (by omega)]
    constructor <;> linarith [hxN.1, hxN.2]
  have hhhalf : h ≤ 1 / 2 := by linarith
  have hfh : 0 ≤ f h :=
    concave_zero_endpoints_nonneg hf h0 h1 ⟨hh.le, by linarith⟩
  have hfr : 0 ≤ f (1 - h) :=
    concave_zero_endpoints_nonneg hf h0 h1 ⟨by linarith, by linarith⟩
  have hnonneg (j : ℕ) (hj : j ≤ N) : 0 ≤ f (x j) :=
    concave_zero_endpoints_nonneg hf h0 h1 (hxmem j hj)
  have hfx0 : f (x 0) ≤ 2 * f h :=
    concave_sampling_left_endpoint_bound hf h0 h1 hh hhhalf hx01
  have hfx1 : f (x 1) ≤ 2 * f h :=
    concave_sampling_left_endpoint_bound hf h0 h1 hh hhhalf hx11
  have hfxN : f (x N) ≤ 2 * f (1 - h) :=
    concave_sampling_right_endpoint_bound hf h0 h1 hh hhhalf
      ⟨by linarith [hxN.1], hxN.2⟩
  have hfxNm1 : f (x (N - 1)) ≤ 2 * f (1 - h) :=
    concave_sampling_right_endpoint_bound hf h0 h1 hh hhhalf hxNm1
  have hint {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
      (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hc.mono (fun _ ht ↦ ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
  have hcore := sampling_mesh_core_bounds f x h N (by omega)
    (fun j hj ↦ hint (hxmem j (by simp only [Finset.mem_Ico] at hj; omega))
      (hxmem (j + 1) (by simp only [Finset.mem_Ico] at hj; omega)) (hmono (by omega)))
    (by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have hp := concave_sampling_cell_integral_bounds hf hc hh
        (by rw [← hpred j hj'.1]; exact hxmem (j - 1) (by omega))
        (by rw [← hstep j]; exact hxmem (j + 1) (by omega))
      simpa only [← hstep j, ← hpred j hj'.1] using hp)
  have hcorelo : -h * f h ≤
      (∫ t in x 1..x N, f t) - h * ∑ j ∈ Finset.Ico 1 N, f (x j) := by
    have hm := mul_le_mul_of_nonneg_left hfx1 hh.le
    have hn := mul_nonneg hh.le (hnonneg N le_rfl)
    nlinarith [hcore.1]
  have hcorehi :
      (∫ t in x 1..x N, f t) - h * ∑ j ∈ Finset.Ico 1 N, f (x j) ≤
        h * f (1 - h) := by
    have hm := mul_le_mul_of_nonneg_left hfxNm1 hh.le
    have hn := mul_nonneg hh.le (hnonneg 0 (by omega))
    nlinarith [hcore.2]
  have hleft_nonneg : 0 ≤ ∫ t in (0 : ℝ)..x 1, f t :=
    intervalIntegral.integral_nonneg hx1mem.1 (fun t ht ↦
      concave_zero_endpoints_nonneg hf h0 h1 ⟨ht.1, ht.2.trans hx1mem.2⟩)
  have hleft : (∫ t in (0 : ℝ)..x 1, f t) ≤ 4 * h * f h := by
    have key := intervalIntegral.integral_mono_on hx1mem.1
      (hint (by norm_num) hx1mem hx1mem.1) (intervalIntegrable_const (c := 2 * f h))
      (fun t ht ↦ concave_sampling_left_endpoint_bound hf h0 h1 hh hhhalf
        ⟨ht.1, ht.2.trans hx11.2⟩)
    rw [intervalIntegral.integral_const] at key
    simp only [sub_zero, smul_eq_mul] at key
    nlinarith [mul_nonneg (sub_nonneg.mpr hx11.2) hfh]
  have hright_nonneg : 0 ≤ ∫ t in x N..(1 : ℝ), f t :=
    intervalIntegral.integral_nonneg hxN.2 (fun t ht ↦
      concave_zero_endpoints_nonneg hf h0 h1 ⟨hxNmem.1.trans ht.1, ht.2⟩)
  have hright : (∫ t in x N..(1 : ℝ), f t) ≤ 2 * h * f (1 - h) := by
    have key := intervalIntegral.integral_mono_on hxN.2
      (hint hxNmem (by norm_num) hxN.2) (intervalIntegrable_const (c := 2 * f (1 - h)))
      (fun t ht ↦ concave_sampling_right_endpoint_bound hf h0 h1 hh hhhalf
        ⟨by linarith [hxN.1, ht.1], ht.2⟩)
    rw [intervalIntegral.integral_const] at key
    simp only [smul_eq_mul] at key
    nlinarith [mul_nonneg (show 0 ≤ h - (1 - x N) by linarith [hxN.1]) hfr]
  have hsum : (∑ j ∈ Finset.Icc 0 N, f (x j)) =
      (∑ j ∈ Finset.Ico 1 N, f (x j)) + f (x 0) + f (x N) := by
    have hset : Finset.Icc 0 N = insert 0 (insert N (Finset.Ico 1 N)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
    ring
  have hintid : (∫ t in (0 : ℝ)..1, f t) =
      (∫ t in (0 : ℝ)..x 1, f t) + (∫ t in x 1..x N, f t) +
        (∫ t in x N..(1 : ℝ), f t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint (by norm_num) hx1mem hx1mem.1)
      (hint hx1mem hxNmem (hmono (by omega))),
      intervalIntegral.integral_add_adjacent_intervals
        (hint (by norm_num) hxNmem hxNmem.1) (hint hxNmem (by norm_num) hxNmem.2)]
  change |h * (∑ j ∈ Finset.Icc 0 N, f (x j)) - (∫ t in (0 : ℝ)..1, f t)| ≤ _
  rw [hsum, hintid]
  apply abs_le.mpr
  have hhL := mul_nonneg hh.le hfh
  have hhR := mul_nonneg hh.le hfr
  have hB0 := mul_nonneg hh.le (hnonneg 0 (by omega))
  have hBN := mul_nonneg hh.le (hnonneg N le_rfl)
  have hB0' := mul_le_mul_of_nonneg_left hfx0 hh.le
  have hBN' := mul_le_mul_of_nonneg_left hfxN hh.le
  constructor <;> nlinarith

end Markov
