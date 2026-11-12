import Markov.NormalizedCircleWinding
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! The actual loop-conjugacy dictionary for an explicitly supplied homotopy
of circle maps. The pinned map_trans_evalAt square homotopy is reused, then
actual based path cancellation supplies conjugacy. Existence of the homotopy
is never inferred from singular H1 or any classification assumption. -/

noncomputable section
universe u v
namespace Markov

/-- An explicitly supplied map homotopy conjugates every actual based loop
by its actual moving-basepoint path. Concatenation retains traversal order. -/
theorem continuousMapHomotopy_loop_conjugate
    {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X]
    {q0 q1 : C(A,X)} (H : q0.Homotopy q1) {x : A} (γ : Path x x) :
    (γ.map q0.continuous).Homotopic
      (((H.evalAt x).trans (γ.map q1.continuous)).trans (H.evalAt x).symm) := by
  have hn := Path.Homotopic.map_trans_evalAt H γ
  have hc : (((γ.map q0.continuous).trans (H.evalAt x)).trans (H.evalAt x).symm).Homotopic
      (γ.map q0.continuous) :=
    (Path.Homotopic.trans_assoc _ _ _).trans
      (((Path.Homotopic.refl _).hcomp (Path.Homotopic.trans_symm _)).trans
        (Path.Homotopic.trans_refl _))
  exact hc.symm.trans (hn.hcomp (Path.Homotopic.refl _))

/-- The actual path traced by the chosen circle basepoint under the supplied homotopy. -/
def normalizedCircleHomotopyBasePath
    {X : Type v} [TopologicalSpace X] {q0 q1 : C(NormalizedCircle,X)}
    (H : q0.Homotopy q1) : Path (q0 0) (q1 0) := H.evalAt 0

/-- Its pointwise formula is literally H(s,0). -/
@[simp] theorem normalizedCircleHomotopyBasePath_apply
    {X : Type v} [TopologicalSpace X] {q0 q1 : C(NormalizedCircle,X)}
    (H : q0.Homotopy q1) (s : unitInterval) :
    normalizedCircleHomotopyBasePath H s = H (s,0) := rfl

/-- Positive actual once-around loops of explicitly homotopic circle maps
are genuinely based path homotopic after the actual basepoint conjugation. -/
theorem normalizedCircleHomotopy_positiveLoop_conjugate
    {X : Type v} [TopologicalSpace X] {q0 q1 : C(NormalizedCircle,X)}
    (H : q0.Homotopy q1) :
    (normalizedCircleStandardLoop.map q0.continuous).Homotopic
      (((normalizedCircleHomotopyBasePath H).trans
        (normalizedCircleStandardLoop.map q1.continuous)).trans
          (normalizedCircleHomotopyBasePath H).symm) :=
  continuousMapHomotopy_loop_conjugate H normalizedCircleStandardLoop

/-- The same literal conjugacy in the actual path-homotopy groupoid.
No fundamental-group multiplication convention is silently substituted. -/
theorem normalizedCircleHomotopy_positiveLoop_quotient
    {X : Type v} [TopologicalSpace X] {q0 q1 : C(NormalizedCircle,X)}
    (H : q0.Homotopy q1) :
    Path.Homotopic.Quotient.mk (normalizedCircleStandardLoop.map q0.continuous) =
      ((Path.Homotopic.Quotient.mk (normalizedCircleHomotopyBasePath H)).trans
        (Path.Homotopic.Quotient.mk (normalizedCircleStandardLoop.map q1.continuous))).trans
          (Path.Homotopic.Quotient.mk (normalizedCircleHomotopyBasePath H)).symm := by
  simpa only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] using
    Path.Homotopic.Quotient.eq.mpr (normalizedCircleHomotopy_positiveLoop_conjugate H)

end Markov
