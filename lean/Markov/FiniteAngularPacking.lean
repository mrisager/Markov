import Markov.PrimitiveAngularSpacing
import Markov.TraceUnresolvedAngularWidth
import Markov.CircleAngularLift
import Mathlib.Data.Finset.Sort

/-! Finite angular packing derived from primitive spacing and actual lifted
normal intervals. No quantitative packing estimate is assumed. -/

noncomputable section
open Set
namespace Markov

/-- A finite separated subset of a real interval has the usual sharp
one-dimensional packing bound, including both endpoints. -/
theorem finset_interval_packing_mul (P : Finset ℝ) (a b δ : ℝ)
    (hab : a ≤ b) (hδ : 0 < δ)
    (hmem : ∀ x ∈ P, x ∈ Icc a b)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ |x - y|) :
    (P.card : ℝ) * δ ≤ b - a + δ := by
  classical
  by_cases hempty : P = ∅
  · subst P
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  have hpos : 0 < P.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  let p : Fin P.card ↪o ℝ := P.orderEmbOfFin rfl
  have hp (i : Fin P.card) : p i ∈ P := P.orderEmbOfFin_mem rfl i
  have hbound : ∀ (i : ℕ) (hi : i < P.card), a + (i : ℝ) * δ ≤ p ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa only [Nat.cast_zero, zero_mul, add_zero] using (hmem _ (hp ⟨0, hi⟩)).1
    | succ i ih =>
        intro hi
        have hi' : i < P.card := by omega
        have hord : p ⟨i, hi'⟩ < p ⟨i + 1, hi⟩ :=
          p.strictMono (by exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
        have hgap := hsep _ (hp ⟨i + 1, hi⟩) _ (hp ⟨i, hi'⟩) (ne_of_gt hord)
        rw [abs_of_pos (sub_pos.mpr hord)] at hgap
        have hh := ih hi'
        push_cast
        linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hnlt : n < P.card := by omega
  have hlo := hbound n hnlt
  have hhi := (hmem _ (hp ⟨n, hnlt⟩)).2
  rw [hn]
  push_cast
  nlinarith

theorem finset_interval_packing (P : Finset ℝ) (a b δ : ℝ)
    (hab : a ≤ b) (hδ : 0 < δ)
    (hmem : ∀ x ∈ P, x ∈ Icc a b)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ |x - y|) :
    (P.card : ℝ) ≤ 1 + (b - a) / δ := by
  have hh := finset_interval_packing_mul P a b δ hab hδ hmem hsep
  calc
    _ ≤ (b - a + δ) / δ := (le_div_iff₀ hδ).mpr hh
    _ = _ := by field_simp; ring

/-- Lifted primitive normal parameters inherit reciprocal-square spacing. -/
theorem primitive_finset_card_le_of_real_angle_lifts
    (D : Finset (ℤ × ℤ)) (T a b : ℝ) (hT : 1 ≤ T) (hab : a ≤ b)
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ D, intEuclidean d ≤ T)
    (φ : ℤ × ℤ → ℝ) (hφmem : ∀ d ∈ D, φ d ∈ Icc a b)
    (hφ : ∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) = circleNormal (φ d)) :
    (D.card : ℝ) ≤ 1 + (b - a) * T ^ 2 := by
  classical
  have hδ : 0 < 1 / T ^ 2 := by positivity
  have hsep (d : ℤ × ℤ) (hd : d ∈ D) (e : ℤ × ℤ) (he : e ∈ D) (hne : d ≠ e) :
      1 / T ^ 2 ≤ |φ d - φ e| := by
    have hh := primitive_angular_spacing d e (hprimitive d hd) (hprimitive e he)
      hne T hT (hsize d hd) (hsize e he)
    rw [hφ d hd, hφ e he] at hh
    exact hh.trans (angle_circleNormal_le_abs_sub _ _)
  have hinj : Set.InjOn φ D := by
    intro d hd e he hde
    by_contra hne
    have hh := hsep d hd e he hne
    rw [hde, sub_self, abs_zero] at hh
    exact (not_le_of_gt hδ) hh
  have hh := finset_interval_packing (D.image φ) a b (1 / T ^ 2) hab hδ
    (by intro x hx; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx; exact hφmem d hd)
    (by
      intro x hx y hy hxy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      exact hsep d hd e he (fun hde => hxy (congrArg φ hde)))
  rw [Finset.card_image_of_injOn hinj] at hh
  simpa only [one_div, div_inv_eq_mul] using hh

/-- An actual boundary-arc normal neighborhood admits interval packing
with its actual turn, including any crossing of the circular seam. -/
theorem primitive_finset_card_le_trace_arc_neighborhood
    (D : Finset (ℤ × ℤ)) (T a b η : ℝ) (hT : 1 ≤ T)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) (hη : 0 ≤ η)
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ D, intEuclidean d ≤ T)
    (hmem : ∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood (normalsOn traceBasis (traceBoundaryOpenArc a b)) η) :
    (D.card : ℝ) ≤ 1 +
      ((traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal + 2 * η) * T ^ 2 := by
  classical
  have hJ := (traceBoundaryOpenArc_normals_isConnected a b ha hab hb).1
  have harc : normalsOn traceBasis (traceBoundaryOpenArc a b) ⊆
      circleNormal '' Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) := by
    rw [← closure_normalsOn_traceBoundaryOpenArc a b ha hab hb]
    exact subset_closure
  have hpoint (d : D) : ∃ φ ∈ Icc (traceCyclicAngleLift a - η)
      (Function.leftLim traceCyclicAngleLift b + η),
      NormedSpace.normalize (euclideanIntDirection d.val) = circleNormal φ :=
    exists_mem_Icc_eq_circleNormal_of_mem_closedAngularNeighborhood_of_subset _ hJ _ _ η harc
      _ (hmem d.val d.property)
  choose φ hφmem hφ using hpoint
  let ψ : ℤ × ℤ → ℝ := fun d => if hd : d ∈ D then φ ⟨d, hd⟩ else 0
  have hlohi : traceCyclicAngleLift a - η ≤ Function.leftLim traceCyclicAngleLift b + η := by
    have horder := traceCyclicAngleLift.mono.le_leftLim hab
    linarith
  have hh := primitive_finset_card_le_of_real_angle_lifts D T _ _ hT hlohi hprimitive hsize ψ
    (by intro d hd; simpa only [ψ, dif_pos hd] using hφmem ⟨d, hd⟩)
    (by intro d hd; simpa only [ψ, dif_pos hd] using hφ ⟨d, hd⟩)
  rw [traceBoundaryTurn_openArc_toReal a b ha hab hb]
  convert hh using 1
  ring

/-- Primitive directions of bounded size assigned to one actual unresolved
component obey packing with that component's actual turn. -/
theorem primitive_finset_card_le_trace_component_neighborhood
    (D : Finset (ℤ × ℤ)) (T H η : ℝ) (hT : 1 ≤ T) (hH : 1 ≤ H) (hη : 0 ≤ η)
    (x : TracePlane) (hx : x ∈ traceUncutBoundary H)
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ D, intEuclidean d ≤ T)
    (hmem : ∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) :
    (D.card : ℝ) ≤ 1 +
      ((traceBoundaryTurn (connectedComponentIn (traceUncutBoundary H) x)).toReal + 2 * η) * T ^ 2 := by
  obtain ⟨a, b, ha, hab, hb, _, _, hcomp⟩ :=
    traceUncutBoundary_exists_path_component H hH x hx
  rw [hcomp] at hmem ⊢
  exact primitive_finset_card_le_trace_arc_neighborhood D T a b η hT ha hab hb hη
    hprimitive hsize hmem

end Markov
