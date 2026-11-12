import T1FareyTraceTriples
import T1GeometricThreshold
import T1LengthVariable
import Markov.TracePlane

/-! The primitive sector dictionary uses the genuine geometric norm,
with the actual matrix trace and the literal full length in the paper. -/
noncomputable section
namespace Markov

theorem t1_fareyWord_coordinateSeeded (w : List Bool) :
    SeededFarey (1,0) (0,1) modularGeneratorA modularGeneratorB
      (t1_fareyWordDirections w).1 (t1_fareyWordDirections w).2
      (t1_fareyWordMatrices w).1 (t1_fareyWordMatrices w).2 := by
  induction w with
  | nil => exact SeededFarey.seed.left.left
  | cons b w ih => cases b with
    | false => exact ih.left
    | true => exact ih.right

theorem t1_fareyWord_geometric_length (w : List Bool) :
    t1_geometricLength (t1_fareyWordDirection w) =
      t1_markovLength (t1_fareyWordTriple w).2.2 := by
  have hp : NonnegativePrimitiveDirection (t1_fareyWordDirection w) :=
    (t1_fareyWord_holonomy w).left.right_nonnegativePrimitive
  have hseed := t1_fareyWord_coordinateSeeded w
  have hfricke := (t1_fareyWord_holonomy w).positiveFrickePair
  have ht := (t1_traceNumber_spec _ hfricke.trace_product hfricke.three_product).1
  have hm : primitiveSeedMatrix modularGeneratorA modularGeneratorB
      (t1_fareyWordDirection w) hp =
      (t1_fareyWordMatrices w).1 * (t1_fareyWordMatrices w).2 :=
    hseed.left.primitiveSeedMatrix_right hp
  change modularMcShaneRivinNorm (euclideanIntDirection (t1_fareyWordDirection w)) = _
  rw [modularMcShaneRivinNorm_primitive_trace_value _ hp.2.2,
    norm_intVector_positive _ hp,primitiveSeedLength,primitiveSeedTrace,
    hm,ht]
  simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,t1_markovLength,
    t1_fareyWordTriple]

theorem t1_markovLength_le_iff (r x : ℝ) (hr : 0 < r) (hx : 0 < x) :
    t1_markovLength r ≤ t1_markovLength x ↔ r ≤ x := by
  unfold t1_markovLength
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2),
    Real.arcosh_le_arcosh (by positivity) (by positivity)]
  constructor <;> intro h <;> linarith

theorem t1_fareyWord_geometric_cutoff_iff (w : List Bool) (x : ℝ) (hx : 0 < x) :
    t1_geometricLength (t1_fareyWordDirection w) ≤ t1_markovLength x ↔
      ((t1_fareyWordTriple w).2.2 : ℝ) ≤ x := by
  rw [t1_fareyWord_geometric_length]
  have ho := t1_fareyWordTriple_ordered w
  have hrN := ho.1.trans_le (ho.2.1.trans ho.2.2.1)
  exact t1_markovLength_le_iff _ x (by exact_mod_cast hrN) hx

end Markov
