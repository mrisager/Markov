import Markov.PrimitiveAxisLeastPeriod
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

noncomputable section
open Set
open scoped Pointwise
namespace Markov

/-- The distances to zero and one force an actual real isometry to be
a translation or a reflection, with its literal value at zero retained. -/
theorem real_isometry_translation_or_reflection (f : ℝ → ℝ) (hf : Isometry f) :
    (∀ t, f t = t + f 0) ∨ (∀ t, f t = f 0 - t) := by
  have h01 : |f 1 - f 0| = 1 := by
    simpa only [Real.dist_eq, sub_zero, abs_one] using hf.dist_eq 1 0
  have hs (t : ℝ) :
      (f t-f 0)^2 = t^2 ∧ (f t-f 1)^2 = (t-1)^2 := by
    constructor
    · have h := congrArg (fun x : ℝ => x^2) (hf.dist_eq t 0)
      simpa only [Real.dist_eq, sq_abs, sub_zero] using h
    · have h := congrArg (fun x : ℝ => x^2) (hf.dist_eq t 1)
      simpa only [Real.dist_eq, sq_abs] using h
  by_cases hp : 0 ≤ f 1-f 0
  · have h1 : f 1 = f 0+1 := by rw [abs_of_nonneg hp] at h01; linarith
    left
    intro t
    obtain ⟨h0t, h1t⟩ := hs t
    rw [h1] at h1t
    nlinarith
  · have h1 : f 1 = f 0-1 := by
      rw [abs_of_neg (lt_of_not_ge hp)] at h01
      linarith
    right
    intro t
    obtain ⟨h0t, h1t⟩ := hs t
    rw [h1] at h1t
    nlinarith

/-- In a free isometric action, a group element mapping a full isometric real
line into itself acts on that line by an actual translation. Reflection would
fix a point and hence be the identity, contradicting the reflection formula. -/
theorem isometricLine_smul_translation
    {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
    [IsIsometricSMul G X] [IsCancelSMul G X]
    (α : ℝ → X) (hα : Isometry α) (g : G)
    (hrange : MapsTo (fun x : X => g • x) (range α) (range α)) :
    ∃ c : ℝ, ∀ t : ℝ, g • α t = α (t+c) := by
  have hy : ∀ t : ℝ, ∃ u : ℝ, α u = g • α t :=
    fun t => hrange (mem_range_self t)
  choose f hf using hy
  have hisom : Isometry f := by
    apply Isometry.of_dist_eq
    intro s t
    calc
      dist (f s) (f t) = dist (α (f s)) (α (f t)) := (hα.dist_eq _ _).symm
      _ = dist (g • α s) (g • α t) := by rw [hf s, hf t]
      _ = dist (α s) (α t) := dist_smul g _ _
      _ = dist s t := hα.dist_eq s t
  rcases real_isometry_translation_or_reflection f hisom with hplus | hminus
  · refine ⟨f 0, fun t => (hf t).symm.trans ?_⟩
    exact congrArg α (hplus t)
  · have hfix : g • α (f 0/2) = α (f 0/2) := by
      rw [← hf, hminus]
      congr 1
      ring
    have hg : g = 1 := IsCancelSMul.eq_one_of_smul hfix
    have hid (t : ℝ) : f t = t := hα.injective (by rw [hf, hg, one_smul])
    have hbad := hminus 1
    rw [hid 0, hid 1] at hbad
    norm_num at hbad

/-- Full actual integral equivariance of the selected invariant axis. -/
theorem modularHyperbolicAxis_add_int_period (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (n : ℤ) (t : ℝ) :
    modularHyperbolicAxis g hg (t+(n : ℝ)*modularClosedGeodesicPeriod g) =
      g^n • modularHyperbolicAxis g hg t := by
  have hsub (t : ℝ) :
      modularHyperbolicAxis g hg (t-modularClosedGeodesicPeriod g) =
        g⁻¹ • modularHyperbolicAxis g hg t := by
    have h := congrArg (fun z : UpperHalfPlane => g⁻¹ • z)
      (modularHyperbolicAxis_action g hg (t-modularClosedGeodesicPeriod g))
    simpa only [sub_add_cancel, inv_smul_smul] using h
  induction n using Int.induction_on generalizing t with
  | zero => simp only [Int.cast_zero, zero_mul, add_zero, zpow_zero, one_smul]
  | succ n ih =>
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc,
      ← modularHyperbolicAxis_action, ih]
    rw [← mul_self_zpow, mul_smul]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, sub_mul, one_mul, ← add_sub_assoc, hsub, ih]
    have he : g^(-(n : ℤ)-1) = g⁻¹*g^(-(n : ℤ)) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
    rw [he, mul_smul]

/-- An actual deck transformation preserving an actual axis range acts by a
literal parameter shift; no centralizer or orientation premise is assumed. -/
theorem modularHyperbolicAxis_translation_of_range_preserving
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (h : modularTraceSubgroup)
    (hrange : range (fun t : ℝ => h • modularHyperbolicAxis g hg t) =
      range (modularHyperbolicAxis g hg)) :
    ∃ c : ℝ, ∀ t : ℝ,
      h • modularHyperbolicAxis g hg t = modularHyperbolicAxis g hg (t+c) := by
  apply isometricLine_smul_translation (modularHyperbolicAxis g hg)
    (modularHyperbolicAxis_isometry g hg) h
  rintro x ⟨t, rfl⟩
  rw [← hrange]
  exact ⟨t, rfl⟩

/-- The exact period group identifies the full actual setwise axis stabilizer.
The period-group equality is explicit here, for reuse beyond canonical words. -/
theorem modularHyperbolicAxis_range_translate_eq_iff_of_periodSubgroup
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (hperiod : realCurvePeriodSubgroup (modularClosedGeodesic g hg) =
      AddSubgroup.zmultiples (modularClosedGeodesicPeriod g))
    (h : modularTraceSubgroup) :
    range (fun t : ℝ => h • modularHyperbolicAxis g hg t) =
      range (modularHyperbolicAxis g hg) ↔ h ∈ Subgroup.zpowers g := by
  constructor
  · intro he
    obtain ⟨c, hc⟩ := modularHyperbolicAxis_translation_of_range_preserving g hg h he
    have hper : Function.Periodic (modularClosedGeodesic g hg) c := by
      intro t
      change modularTraceQuotientMk (modularHyperbolicAxis g hg (t+c)) =
        modularTraceQuotientMk (modularHyperbolicAxis g hg t)
      rw [← hc t, modularTraceQuotientMk_smul]
    have hm : c ∈ realCurvePeriodSubgroup (modularClosedGeodesic g hg) := hper
    rw [hperiod] at hm
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    have hn' : (n : ℝ)*modularClosedGeodesicPeriod g = c := by
      simpa only [zsmul_eq_mul] using hn
    have hh : h = g^n := by
      apply IsCancelSMul.right_cancel h (g^n) (modularHyperbolicAxis g hg 0)
      calc
        h • modularHyperbolicAxis g hg 0 = modularHyperbolicAxis g hg (0+c) := hc 0
        _ = modularHyperbolicAxis g hg (0+(n : ℝ)*modularClosedGeodesicPeriod g) := by rw [hn']
        _ = g^n • modularHyperbolicAxis g hg 0 := modularHyperbolicAxis_add_int_period g hg n 0
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, hh.symm⟩
  · intro hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t+(n : ℝ)*modularClosedGeodesicPeriod g, ?_⟩
      rw [modularHyperbolicAxis_add_int_period, hn]
    · rintro ⟨t, rfl⟩
      refine ⟨t-(n : ℝ)*modularClosedGeodesicPeriod g, ?_⟩
      have he := modularHyperbolicAxis_add_int_period g hg n
        (t-(n : ℝ)*modularClosedGeodesicPeriod g)
      rw [sub_add_cancel, hn] at he
      exact he.symm

/-- The full setwise range stabilizer of the canonical actual invariant axis
is exactly the powers of its actual canonical holonomy. -/
theorem paperPrimitiveHyperbolicAxis_range_translate_eq_iff
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (h : modularTraceSubgroup) :
    range (fun t : ℝ => h • modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
      (paperPrimitiveHolonomy_hyperbolic k p hp) t) =
      range (modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp)) ↔
      h ∈ Subgroup.zpowers (paperPrimitiveHolonomy k p hp) := by
  apply modularHyperbolicAxis_range_translate_eq_iff_of_periodSubgroup
  simpa only [paperPrimitiveClosedGeodesic, paperPrimitiveHolonomy_period] using
    paperPrimitiveClosedGeodesic_periodSubgroup k p hp

/-- The genuine subgroup stabilizer for the pointwise action on actual sets. -/
theorem paperPrimitiveHyperbolicAxis_stabilizer
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    MulAction.stabilizer modularTraceSubgroup
      (range (modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp))) =
      Subgroup.zpowers (paperPrimitiveHolonomy k p hp) := by
  ext h
  rw [MulAction.mem_stabilizer_iff, ← Set.range_smul]
  exact paperPrimitiveHyperbolicAxis_range_translate_eq_iff k p hp h

end Markov
