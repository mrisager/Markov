import Markov.OriginalNielsenStandardLinear
import Markov.OriginalGeometricRealization
import Markov.UnimodularTorusHomeomorphisms

noncomputable section
namespace Markov

/-- The actual standard-coordinate formula, retaining both original signed
labels: the literal integer columns are J(v),J(u). -/
def OriginalPairLinearMap (u v : ℤ × ℤ)
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient) : Prop :=
  ∀ z : ModularTraceQuotient,
    (modularTraceQuotientPuncturedTorusHomeomorph (f z)).val =
      standardTorusColumnMap (originalToStandardCircleLabel v) (originalToStandardCircleLabel u)
        (modularTraceQuotientPuncturedTorusHomeomorph z).val

/-- Constructed actual linear witnesses, actual connector and exact original
nonabelian generator images; this is stronger than the older existential. -/
def OriginalPairLinearlyRealized (u v : ℤ × ℤ) (g h : modularTraceSubgroup) : Prop :=
  (intDet u v = 1 ∨ intDet u v = -1) ∧
  ∃ (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)),
    OriginalPairLinearMap u v f ∧
    originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis 0) = g ∧
    originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis 1) = h

/-- The actual identity represents A,B at the literal negative original labels. -/
theorem originalPairLinearlyRealized_basis :
    OriginalPairLinearlyRealized (-1, 0) (0, -1)
      (paperTraceFreeGroupBasis 0) (paperTraceFreeGroupBasis 1) := by
  refine ⟨Or.inl (by norm_num [intDet]), Homeomorph.refl _, Path.refl _, ?_, ?_, ?_⟩
  · intro z
    ext <;> simp [standardTorusColumnMap, standardTorusIntegerCombination, originalToStandardCircleLabel]
  · rw [originalMarkedHomeomorphEquiv_refl]
    rfl
  · rw [originalMarkedHomeomorphEquiv_refl]
    rfl

theorem OriginalPairLinearlyRealized.swap {u v : ℤ × ℤ} {g h : modularTraceSubgroup}
    (hp : OriginalPairLinearlyRealized u v g h) : OriginalPairLinearlyRealized v u h g := by
  rcases hp with ⟨hd, f, cf, hlin, hA, hB⟩
  let ca := originalNielsenRightSwapConnector
  have he : originalMarkedHomeomorphEquiv modularCoordinateSwapHomeomorph ca =
      originalCoordinateSwapMarkedEquiv := rfl
  let c := basedHomeomorphCompositeConnector f modularCoordinateSwapHomeomorph
    paperGeneratorCenterPoint cf ca
  have hcomp : originalMarkedHomeomorphEquiv (modularCoordinateSwapHomeomorph.trans f) c =
      originalCoordinateSwapMarkedEquiv.trans (originalMarkedHomeomorphEquiv f cf) := by
    rw [← originalMarkedHomeomorphEquiv_comp f modularCoordinateSwapHomeomorph cf ca, he]
  refine ⟨?_, modularCoordinateSwapHomeomorph.trans f, c, ?_, ?_, ?_⟩
  · have hh : intDet v u = -intDet u v := by unfold intDet; ring
    rw [hh]
    rcases hd with hd | hd <;> simp [hd]
  · intro z
    change (modularTraceQuotientPuncturedTorusHomeomorph (f (modularCoordinateSwapHomeomorph z))).val = _
    rw [hlin, modularCoordinateSwapHomeomorph_standard, standardCoordinateSwapPuncturedTorusHomeomorph_coe]
    apply Prod.ext <;> simp [standardTorusColumnMap, standardTorusIntegerCombination, add_comm]
  · rw [hcomp, MulEquiv.trans_apply, originalCoordinateSwapMarkedEquiv_A, hB]
  · rw [hcomp, MulEquiv.trans_apply, originalCoordinateSwapMarkedEquiv_B, hA]

theorem OriginalPairLinearlyRealized.invert_second {u v : ℤ × ℤ} {g h : modularTraceSubgroup}
    (hp : OriginalPairLinearlyRealized u v g h) : OriginalPairLinearlyRealized u (-v) g h⁻¹ := by
  rcases hp with ⟨hd, f, cf, hlin, hA, hB⟩
  let ca : Path paperGeneratorCenterPoint (modularFirstReflectionHomeomorph paperGeneratorCenterPoint) :=
    (Path.refl paperGeneratorCenterPoint).cast rfl modularFirstReflectionHomeomorph_center
  have he : originalMarkedHomeomorphEquiv modularFirstReflectionHomeomorph ca =
      originalFirstReflectionMarkedEquiv := rfl
  let c := basedHomeomorphCompositeConnector f modularFirstReflectionHomeomorph
    paperGeneratorCenterPoint cf ca
  have hcomp : originalMarkedHomeomorphEquiv (modularFirstReflectionHomeomorph.trans f) c =
      originalFirstReflectionMarkedEquiv.trans (originalMarkedHomeomorphEquiv f cf) := by
    rw [← originalMarkedHomeomorphEquiv_comp f modularFirstReflectionHomeomorph cf ca, he]
  refine ⟨?_, modularFirstReflectionHomeomorph.trans f, c, ?_, ?_, ?_⟩
  · have hh : intDet u (-v) = -intDet u v := by simp [intDet]; ring
    rw [hh]
    rcases hd with hd | hd <;> simp [hd]
  · intro z
    change (modularTraceQuotientPuncturedTorusHomeomorph (f (modularFirstReflectionHomeomorph z))).val = _
    rw [hlin, modularFirstReflectionHomeomorph_standard, standardFirstReflectionPuncturedTorusHomeomorph_coe]
    apply Prod.ext <;>
      simp [standardTorusColumnMap, standardTorusIntegerCombination, originalToStandardCircleLabel,
        smul_neg, neg_smul]
  · rw [hcomp, MulEquiv.trans_apply, originalFirstReflectionMarkedEquiv_A, hA]
  · rw [hcomp, MulEquiv.trans_apply, originalFirstReflectionMarkedEquiv_B, map_inv, hB]

theorem OriginalPairLinearlyRealized.invert_first {u v : ℤ × ℤ} {g h : modularTraceSubgroup}
    (hp : OriginalPairLinearlyRealized u v g h) : OriginalPairLinearlyRealized (-u) v g⁻¹ h :=
  hp.swap.invert_second.swap

theorem OriginalPairLinearlyRealized.left {u v : ℤ × ℤ} {g h : modularTraceSubgroup}
    (hp : OriginalPairLinearlyRealized u v g h) : OriginalPairLinearlyRealized u (u+v) g (g*h) := by
  rcases hp with ⟨hd, f, cf, hlin, hA, hB⟩
  let ca := originalNielsenConnectorCorrected
  have he : originalMarkedHomeomorphEquiv originalNielsenHomeomorph ca = originalNielsenMarkedEquiv := rfl
  let c := basedHomeomorphCompositeConnector f originalNielsenHomeomorph paperGeneratorCenterPoint cf ca
  have hcomp : originalMarkedHomeomorphEquiv (originalNielsenHomeomorph.trans f) c =
      originalNielsenMarkedEquiv.trans (originalMarkedHomeomorphEquiv f cf) := by
    rw [← originalMarkedHomeomorphEquiv_comp f originalNielsenHomeomorph cf ca, he]
  refine ⟨?_, originalNielsenHomeomorph.trans f, c, ?_, ?_, ?_⟩
  · have hh : intDet u (u+v) = intDet u v := by simp [intDet]; ring
    rwa [hh]
  · intro z
    change (modularTraceQuotientPuncturedTorusHomeomorph (f (originalNielsenHomeomorph z))).val = _
    rw [hlin, originalNielsenHomeomorph_standard_linear]
    apply Prod.ext <;>
      simp only [standardTorusColumnMap, standardTorusIntegerCombination, originalToStandardCircleLabel,
        Prod.fst_add, Prod.snd_add, neg_add, smul_add, add_smul, neg_smul] <;> abel
  · rw [hcomp, MulEquiv.trans_apply, originalNielsenMarkedEquiv_A, hA]
  · rw [hcomp, MulEquiv.trans_apply, originalNielsenMarkedEquiv_B, map_mul, hA, hB]

theorem OriginalPairLinearlyRealized.right {u v : ℤ × ℤ} {g h : modularTraceSubgroup}
    (hp : OriginalPairLinearlyRealized u v g h) : OriginalPairLinearlyRealized (u+v) v (g*h) h := by
  rcases hp with ⟨hd, f, cf, hlin, hA, hB⟩
  let ca := originalNielsenRightConnectorCorrected
  have he : originalMarkedHomeomorphEquiv originalNielsenRightHomeomorph ca =
      originalNielsenRightMarkedEquiv := rfl
  let c := basedHomeomorphCompositeConnector f originalNielsenRightHomeomorph paperGeneratorCenterPoint cf ca
  have hcomp : originalMarkedHomeomorphEquiv (originalNielsenRightHomeomorph.trans f) c =
      originalNielsenRightMarkedEquiv.trans (originalMarkedHomeomorphEquiv f cf) := by
    rw [← originalMarkedHomeomorphEquiv_comp f originalNielsenRightHomeomorph cf ca, he]
  refine ⟨?_, originalNielsenRightHomeomorph.trans f, c, ?_, ?_, ?_⟩
  · have hh : intDet (u+v) v = intDet u v := by simp [intDet]; ring
    rwa [hh]
  · intro z
    change (modularTraceQuotientPuncturedTorusHomeomorph (f (originalNielsenRightHomeomorph z))).val = _
    rw [hlin, originalNielsenRightHomeomorph_standard_linear]
    apply Prod.ext <;>
      simp only [standardTorusColumnMap, standardTorusIntegerCombination, originalToStandardCircleLabel,
        Prod.fst_add, Prod.snd_add, neg_add, smul_add, add_smul, neg_smul] <;> abel
  · rw [hcomp, MulEquiv.trans_apply, originalNielsenRightMarkedEquiv_A, map_mul, hA, hB]
  · rw [hcomp, MulEquiv.trans_apply, originalNielsenRightMarkedEquiv_B, hB]

end Markov
