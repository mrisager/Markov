import Markov.PrimitiveRayDecomposition
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

/-! Exact complex regrouping into signed primitive rays and strictly
positive multiples, justified by absolute convergence before any block norm. -/

noncomputable section

namespace Markov

/-- The ray decomposition ordered as a signed primitive ray and a natural
index whose actual positive multiplier is `m+1`. -/
def primitiveRayNatEquiv : NonzeroIntegerDirection ≃ PrimitiveIntegerRay × ℕ :=
  primitiveRayEquiv.trans ((Equiv.prodComm ℕ+ PrimitiveIntegerRay).trans
    (Equiv.prodCongr (Equiv.refl PrimitiveIntegerRay) Equiv.pnatEquivNat))

/-- The inverse map uses exactly the strictly positive integer multiplier. -/
theorem primitiveRayNatEquiv_symm_val (p : PrimitiveIntegerRay × ℕ) :
    (primitiveRayNatEquiv.symm p).1 = ((p.2 : ℤ) + 1) • p.1.1 := by
  change (primitiveRayEquiv.symm (Nat.succPNat p.2, p.1)).1 = _
  rw [primitiveRayEquiv_symm_val]
  ext <;> simp [Nat.succPNat, nsmul_eq_mul, zsmul_eq_mul, Nat.cast_add]

/-- The joint primitive-ray and positive-multiple series converges absolutely. -/
theorem primitiveRay_product_norm_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    Summable (fun p : PrimitiveIntegerRay × ℕ ↦ ‖f (((p.2 : ℤ) + 1) • p.1.1)‖) := by
  have hs : Summable (fun d : NonzeroIntegerDirection ↦ ‖f d.1‖) := hf.subtype _
  have hp := hs.comp_injective primitiveRayNatEquiv.symm.injective
  simpa only [primitiveRayNatEquiv_symm_val] using hp

/-- Every complete positive series on a fixed signed primitive ray converges absolutely. -/
theorem primitiveRay_inner_norm_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) (k : PrimitiveIntegerRay) :
    Summable (fun m : ℕ ↦ ‖f (((m : ℤ) + 1) • k.1)‖) :=
  (primitiveRay_product_norm_summable hf).prod_factor k

/-- In particular, each complete positive complex ray series converges. -/
theorem primitiveRay_inner_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) (k : PrimitiveIntegerRay) :
    Summable (fun m : ℕ ↦ f (((m : ℤ) + 1) • k.1)) :=
  (primitiveRay_inner_norm_summable hf k).of_norm

/-- The outer sum of the inner absolute sums converges. -/
theorem primitiveRay_outer_tsum_norm_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    Summable (fun k : PrimitiveIntegerRay ↦ ∑' m : ℕ, ‖f (((m : ℤ) + 1) • k.1)‖) :=
  (primitiveRay_product_norm_summable hf).prod

/-- Norms of the complete complex ray blocks are summable. -/
theorem primitiveRay_outer_norm_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    Summable (fun k : PrimitiveIntegerRay ↦ ‖∑' m : ℕ, f (((m : ℤ) + 1) • k.1)‖) :=
  (primitiveRay_outer_tsum_norm_summable hf).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_tsum_le_tsum_norm (primitiveRay_inner_norm_summable hf k))

/-- The outer series of complete complex blocks converges. -/
theorem primitiveRay_outer_summable {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    Summable (fun k : PrimitiveIntegerRay ↦ ∑' m : ℕ, f (((m : ℤ) + 1) • k.1)) :=
  (primitiveRay_outer_norm_summable hf).of_norm

/-- Exact regrouping of the nonzero lattice series into complete complex
positive-multiple blocks on signed primitive rays. -/
theorem tsum_nonzero_eq_tsum_primitiveRay {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    (∑' d : NonzeroIntegerDirection, f d.1) =
      ∑' k : PrimitiveIntegerRay, ∑' m : ℕ, f (((m : ℤ) + 1) • k.1) := by
  have hp := (primitiveRay_product_norm_summable hf).of_norm
  calc
    _ = ∑' p : PrimitiveIntegerRay × ℕ, f (((p.2 : ℤ) + 1) • p.1.1) := by
      simpa only [primitiveRayNatEquiv_symm_val] using
        (primitiveRayNatEquiv.symm.tsum_eq (fun d : NonzeroIntegerDirection ↦ f d.1)).symm
    _ = _ := hp.tsum_prod

/-- Removing exactly the zero mode from the full lattice sum gives the
same exact primitive-ray regrouping. -/
theorem tsum_sub_zero_eq_tsum_primitiveRay {f : ℤ × ℤ → ℂ}
    (hf : Summable (fun d : ℤ × ℤ ↦ ‖f d‖)) :
    (∑' d : ℤ × ℤ, f d) - f (0, 0) =
      ∑' k : PrimitiveIntegerRay, ∑' m : ℕ, f (((m : ℤ) + 1) • k.1) := by
  rw [← tsum_nonzero_eq_tsum_primitiveRay hf]
  have heq := hf.of_norm.sum_add_tsum_subtype_compl ({(0, 0)} : Finset (ℤ × ℤ))
  have hpred : (fun d : ℤ × ℤ ↦ d ∉ ({(0, 0)} : Finset (ℤ × ℤ))) =
      (fun d : ℤ × ℤ ↦ d ≠ (0, 0)) := by
    funext d
    apply propext
    simp
  change (∑ d ∈ ({(0, 0)} : Finset (ℤ × ℤ)), f d) +
      (∑' d : {d : ℤ × ℤ // d ∉ ({(0, 0)} : Finset (ℤ × ℤ))}, f d.1) =
      ∑' d : ℤ × ℤ, f d at heq
  rw [hpred] at heq
  simp only [Finset.sum_singleton] at heq
  exact sub_eq_iff_eq_add.mpr (heq.symm.trans (add_comm _ _))

end Markov
