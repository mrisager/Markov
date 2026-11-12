import Markov.PrimitiveRaySummation
import Markov.TracePoisson
import Markov.TraceLemmaTen

/-! Exact primitive-ray regrouping of the actual trace-ball Poisson series.
The complete complex positive blocks are formed before taking their norms. -/

noncomputable section
namespace Markov

theorem euclideanIntDirection_zsmul (k : ℤ × ℤ) (m : ℤ) :
    euclideanIntDirection (m • k) = (m : ℝ) • euclideanIntDirection k := by
  simpa only [Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul] using
    euclideanIntDirection_integerRay k m

/-- The exact radial Fourier term uses the same rho_(SQ) scaling as the
full two-dimensional Poisson term. -/
theorem traceFourierLatticeTerm_integer_multiple (S Q : ℝ) (k : ℤ × ℤ) (m : ℤ) :
    traceFourierLatticeTerm S Q (m • k) =
      ((S ^ 2 : ℝ) : ℂ) * traceRadialFourierTerm S Q k m := by
  simp only [traceFourierLatticeTerm, traceRadialFourierTerm,
    euclideanIntDirection_zsmul, smul_smul, div_eq_mul_inv]
  rw [mul_comm Q⁻¹ (m : ℝ), mul_assoc]

theorem traceRadialBlock_eq_tsum_latticeTerms (S Q : ℝ) (k : ℤ × ℤ) :
    traceRadialBlock S Q k =
      ∑' m : ℕ, traceFourierLatticeTerm S Q (((m : ℤ) + 1) • k) := by
  simp_rw [traceFourierLatticeTerm_integer_multiple]
  rw [tsum_mul_left]
  rfl

/-- Norms of the actual complete complex primitive blocks are summable. -/
theorem traceRadialBlock_primitive_norm_summable (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) :
    Summable (fun k : PrimitiveIntegerRay => ‖traceRadialBlock S Q k.1‖) := by
  simp_rw [traceRadialBlock_eq_tsum_latticeTerms]
  exact primitiveRay_outer_norm_summable (traceFourierLatticeTerm_norm_summable S Q hS hQ)

theorem traceRadialBlock_primitive_summable (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) :
    Summable (fun k : PrimitiveIntegerRay => traceRadialBlock S Q k.1) :=
  (traceRadialBlock_primitive_norm_summable S Q hS hQ).of_norm

/-- The actual Poisson expansion grouped into signed primitive rays. The
signs remain in the outer index; there is no additional factor two. -/
theorem trace_smoothed_lattice_poisson_primitiveRays (S Q : ℝ)
    (hS : 0 < S) (hQ : 0 < Q) :
    (traceSmoothedLatticeCount S Q : ℂ) = (S ^ 2 * traceEuclideanArea : ℝ) +
      ∑' k : PrimitiveIntegerRay, traceRadialBlock S Q k.1 := by
  rw [trace_smoothed_lattice_poisson_nonzero S Q hS hQ]
  congr 1
  change (∑' n : NonzeroIntegerDirection, traceFourierLatticeTerm S Q n.1) = _
  rw [tsum_nonzero_eq_tsum_primitiveRay (traceFourierLatticeTerm_norm_summable S Q hS hQ)]
  exact tsum_congr (fun k => (traceRadialBlock_eq_tsum_latticeTerms S Q k.1).symm)

/-- Unlike the optional individual-frequency error, this bound retains the
entire collinear cancellation inside each actual radial block. -/
theorem trace_smoothed_lattice_discrepancy_primitiveRay_bound (S Q : ℝ)
    (hS : 0 < S) (hQ : 0 < Q) :
    |traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea| ≤
      ∑' k : PrimitiveIntegerRay, ‖traceRadialBlock S Q k.1‖ := by
  have hid : ((traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea : ℝ) : ℂ) =
      ∑' k : PrimitiveIntegerRay, traceRadialBlock S Q k.1 := by
    rw [Complex.ofReal_sub, trace_smoothed_lattice_poisson_primitiveRays S Q hS hQ]
    ring
  calc
    _ = ‖((traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea : ℝ) : ℂ)‖ :=
      (Complex.norm_real _).symm
    _ = ‖∑' k : PrimitiveIntegerRay, traceRadialBlock S Q k.1‖ := congrArg norm hid
    _ ≤ _ := norm_tsum_le_tsum_norm (traceRadialBlock_primitive_norm_summable S Q hS hQ)

end Markov
