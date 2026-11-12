import Markov.StandardPrimitiveCircles
import Markov.NormalizedCircleWindingConjugation

noncomputable section
open Set Topology
namespace Markov

/-- A literal graph circle with its stated nonzero value above zero. -/
def standardPuncturedGraphCircle (f : C(NormalizedCircle, NormalizedCircle))
    (hf0 : f 0 ≠ 0) (u : NormalizedCircle) : StandardPuncturedTorus :=
  ⟨(u, f u), by
    intro he
    have hu : u = 0 := congrArg Prod.fst he
    have hv : f u = 0 := congrArg Prod.snd he
    exact hf0 (hu ▸ hv)⟩

theorem continuous_standardPuncturedGraphCircle (f : C(NormalizedCircle, NormalizedCircle))
    (hf0 : f 0 ≠ 0) : Continuous (standardPuncturedGraphCircle f hf0) := by
  unfold standardPuncturedGraphCircle
  fun_prop

/-- The actual graph map is closed embedded because its first coordinate is
a literal left inverse. -/
theorem standardPuncturedGraphCircle_isClosedEmbedding
    (f : C(NormalizedCircle, NormalizedCircle)) (hf0 : f 0 ≠ 0) :
    IsClosedEmbedding (standardPuncturedGraphCircle f hf0) :=
  (continuous_standardPuncturedGraphCircle f hf0).isClosedEmbedding
    (fun _ _ he => congrArg (fun z : StandardPuncturedTorus => z.val.1) he)

/-- The actual positive once-around loop of the literal graph. -/
def standardPuncturedGraphLoop (f : C(NormalizedCircle, NormalizedCircle))
    (hf0 : f 0 ≠ 0) : Path (standardPuncturedGraphCircle f hf0 0)
      (standardPuncturedGraphCircle f hf0 0) :=
  normalizedCircleStandardLoop.map (continuous_standardPuncturedGraphCircle f hf0)

/-- The second coordinate loop translated to its actual basepoint zero. -/
def standardGraphSecondBasedLoop (f : C(NormalizedCircle, NormalizedCircle)) :
    Path (0 : NormalizedCircle) 0 :=
  normalizedCircleTranslatedLoop (normalizedCircleStandardLoop.map f.continuous)

/-- Its genuine covering winding, using the proved circle-pi1 completeness. -/
def standardGraphCircleWinding (f : C(NormalizedCircle, NormalizedCircle)) : ℤ :=
  normalizedCircleWinding (standardGraphSecondBasedLoop f)

/-- The affine comparison loop, with columns (1,winding) and (0,1), actual
offset f(0), and the graph's literal original basepoint. -/
def standardPuncturedGraphAffineLoop (f : C(NormalizedCircle, NormalizedCircle))
    (hf0 : f 0 ≠ 0) : Path (standardPuncturedGraphCircle f hf0 0)
      (standardPuncturedGraphCircle f hf0 0) where
  toFun t := standardPuncturedAffineCircle (1, standardGraphCircleWinding f) (0, 1)
    (by norm_num [intDet]) (f 0) hf0 (normalizedCircleStandardLoop t)
  continuous_toFun := (continuous_standardPuncturedAffineCircle
    (1, standardGraphCircleWinding f) (0, 1) (by norm_num [intDet]) (f 0) hf0).comp
    normalizedCircleStandardLoop.continuous
  source' := by
    apply Subtype.ext
    simp [standardPuncturedAffineCircle, standardTorusIntegerCombination, standardPuncturedGraphCircle]
  target' := by
    apply Subtype.ext
    simp [standardPuncturedAffineCircle, standardTorusIntegerCombination, standardPuncturedGraphCircle]

/-- In the actual once-around parameter, only the two interval endpoints
represent the zero circle point. -/
theorem normalizedCircleStandardLoop_eq_zero_iff (t : unitInterval) :
    normalizedCircleStandardLoop t = 0 ↔ t = 0 ∨ t = 1 := by
  by_cases ht : t = 1
  · simp [ht]
  have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun he => ht (Subtype.ext he))
  rw [normalizedCircleStandardLoop_apply,
    AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨t.property.1, hlt⟩]
  constructor
  · intro he
    exact Or.inl (Subtype.ext he)
  · rintro (he | he)
    · rw [he]
      rfl
    · exact (ht he).elim

/-- Genuine puncture-preserving based homotopy from an actual graph circle
to its actual affine circle, using circle-pi1 completeness rather than H1.
The graph hypothesis is explicit; arbitrary embedded curves are not classified. -/
theorem standardPuncturedGraphLoop_homotopic_affine
    (f : C(NormalizedCircle, NormalizedCircle)) (hf0 : f 0 ≠ 0) :
    (standardPuncturedGraphLoop f hf0).Homotopic (standardPuncturedGraphAffineLoop f hf0) := by
  have hh : (standardGraphSecondBasedLoop f).Homotopic
      (normalizedCircleIntegerLoop (standardGraphCircleWinding f)) := by
    apply (normalizedCircleWinding_homotopic_iff _ _).mp
    rw [normalizedCircleWinding_integerLoop]
    rfl
  obtain ⟨H⟩ := hh
  have havoid (s t : unitInterval) :
      (normalizedCircleStandardLoop t, f 0 + H (s, t)) ≠ (0 : StandardTorus) := by
    intro he
    have hz : normalizedCircleStandardLoop t = 0 := congrArg Prod.fst he
    have hv : f 0 + H (s, t) = 0 := congrArg Prod.snd he
    rcases (normalizedCircleStandardLoop_eq_zero_iff t).mp hz with rfl | rfl
    · exact hf0 (by simpa only [H.source, add_zero] using hv)
    · exact hf0 (by simpa only [H.target, add_zero] using hv)
  have hint (t : unitInterval) :
      normalizedCircleIntegerLoop (standardGraphCircleWinding f) t =
        standardGraphCircleWinding f • normalizedCircleStandardLoop t := by
    rw [normalizedCircleIntegerLoop_apply, normalizedCircleStandardLoop_apply,
      ← AddCircle.coe_zsmul]
    congr 1
    simp only [zsmul_eq_mul, mul_comm]
  refine ⟨{
    toFun := fun st => ⟨(normalizedCircleStandardLoop st.2, f 0 + H st), havoid st.1 st.2⟩
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change f 0 + H (0, t) = f (normalizedCircleStandardLoop t)
      have h0 : H (0, t) = standardGraphSecondBasedLoop f t := H.map_zero_left t
      rw [h0]
      change f 0 + (f (normalizedCircleStandardLoop t) - f 0) = _
      abel
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · change normalizedCircleStandardLoop t =
        (1 : ℤ) • normalizedCircleStandardLoop t + (0 : ℤ) • f 0
      simp
    · change f 0 + H (1, t) =
        standardGraphCircleWinding f • normalizedCircleStandardLoop t + (1 : ℤ) • f 0
      have h1 : H (1, t) = normalizedCircleIntegerLoop (standardGraphCircleWinding f) t :=
        H.map_one_left t
      rw [h1, hint, one_smul, add_comm]
  · intro s t ht
    rcases ht with rfl | rfl
    · apply Subtype.ext
      change (normalizedCircleStandardLoop 0, f 0 + H (s, 0)) =
        (normalizedCircleStandardLoop 0, f (normalizedCircleStandardLoop 0))
      rw [H.source]
      simp
    · apply Subtype.ext
      change (normalizedCircleStandardLoop 1, f 0 + H (s, 1)) =
        (normalizedCircleStandardLoop 1, f (normalizedCircleStandardLoop 1))
      rw [H.target]
      simp

end Markov
