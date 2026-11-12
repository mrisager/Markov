import Markov.FiniteAffineEnvelope
import Markov.FanSupport
import Mathlib.Analysis.Seminorm

/-! Finite signed support envelopes construct actual planar seminorms.
The quadrant interpolation theorem reduces full-plane gluing to local
ordered-piece data and two explicit axis inequalities. -/

noncomputable section
namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def absLinearSeminorm (f : E →ₗ[ℝ] ℝ) : Seminorm ℝ E :=
  Seminorm.of (fun x => |f x|)
    (fun x y => by simpa only [map_add] using abs_add_le (f x) (f y))
    (fun a x => by simp only [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs])

def prefixLinearSeminorm (f : ℕ → E →ₗ[ℝ] ℝ) : ℕ → Seminorm ℝ E
  | 0 => absLinearSeminorm (f 0)
  | n + 1 => prefixLinearSeminorm f n ⊔ absLinearSeminorm (f (n + 1))

theorem prefixLinearSeminorm_apply (f : ℕ → E →ₗ[ℝ] ℝ) (n : ℕ) (x : E) :
    prefixLinearSeminorm f n x = prefixEnvelope (fun i x => |f i x|) n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixLinearSeminorm, Seminorm.sup_apply, ih, prefixEnvelope]; rfl

def signedLinearSeminorm (f g : ℕ → E →ₗ[ℝ] ℝ) (n m : ℕ) : Seminorm ℝ E :=
  prefixLinearSeminorm f n ⊔ prefixLinearSeminorm g m

/-- Ordered affine pieces have no interior minimum: each value is at least
one of the two exterior-piece values. -/
theorem affinePiece_min_endpoints (a b r : ℕ → ℝ) (n i : ℕ) (x : ℝ) (hi : i ≤ n)
    (hslopes : ∀ j < n, a j ≤ a (j + 1))
    (hmatch : ∀ j < n, affinePiece a b j (r j) = affinePiece a b (j + 1) (r j))
    (hbreaks : ∀ j k, j ≤ k → k < n → r j ≤ r k) :
    min (affinePiece a b 0 x) (affinePiece a b n x) ≤ affinePiece a b i x := by
  by_cases hin : i = n
  · subst i; exact min_le_right _ _
  have hin' : i < n := by omega
  by_cases hx : x ≤ r i
  · have hchain : ∀ j, i ≤ j → j ≤ n → affinePiece a b j x ≤ affinePiece a b i x := by
      intro j hij
      induction j, hij using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ j hij ih =>
        intro hjn
        have hstep := affinePiece_le_left _ _ _ _ (r j) x (hslopes j (by omega))
          (hmatch j (by omega)) (hx.trans (hbreaks i j hij (by omega)))
        exact hstep.trans (ih (by omega))
    exact (min_le_right _ _).trans (hchain n hi le_rfl)
  · have hchain : ∀ j ≤ i, affinePiece a b 0 x ≤ affinePiece a b j x := by
      intro j hj
      induction j with
      | zero => exact le_rfl
      | succ j ih =>
        have hstep := affinePiece_le_right _ _ _ _ (r j) x (hslopes j (by omega))
          (hmatch j (by omega)) ((hbreaks j i (by omega) hin').trans (le_of_not_ge hx))
        exact (ih (by omega)).trans hstep
    exact (min_le_left _ _).trans (hchain i le_rfl)

/-- A signed support seminorm agrees with the prescribed envelope whenever
negative own pieces and both signs of opposite pieces are dominated. -/
theorem signedLinearSeminorm_eq_of_bounds (f g : ℕ → E →ₗ[ℝ] ℝ) (n m : ℕ) (x : E)
    (hmin : ∀ i ≤ n, min (f 0 x) (f n x) ≤ f i x)
    (hsum : 0 ≤ f 0 x + f n x)
    (hother : ∀ j ≤ m, g j x ≤ f n x ∧ -(g j x) ≤ f 0 x) :
    signedLinearSeminorm f g n m x = prefixEnvelope (fun i => f i) n x := by
  let U := prefixEnvelope (fun i => f i) n x
  have h0 : f 0 x ≤ U := le_prefixEnvelope (fun i => (f i : E → ℝ)) n 0 x (Nat.zero_le _)
  have hn : f n x ≤ U := le_prefixEnvelope (fun i => (f i : E → ℝ)) n n x le_rfl
  have hfabs : ∀ i ≤ n, |f i x| ≤ U := by
    intro i hi
    have hp := hmin i hi
    have hneg : -(f i x) ≤ U := by
      rcases le_total (f 0 x) (f n x) with hle | hle
      · rw [min_eq_left hle] at hp
        linarith
      · rw [min_eq_right hle] at hp
        linarith
    exact abs_le.mpr ⟨by linarith, le_prefixEnvelope (fun j => (f j : E → ℝ)) n i x hi⟩
  have hgabs : ∀ j ≤ m, |g j x| ≤ U := by
    intro j hj
    exact abs_le.mpr ⟨by linarith [(hother j hj).2], (hother j hj).1.trans hn⟩
  apply le_antisymm
  · change max (prefixLinearSeminorm f n x) (prefixLinearSeminorm g m x) ≤ U
    rw [prefixLinearSeminorm_apply, prefixLinearSeminorm_apply]
    exact max_le (prefixEnvelope_le _ n x U hfabs) (prefixEnvelope_le _ m x U hgabs)
  · apply prefixEnvelope_le _ n x
    intro i hi
    calc
      f i x ≤ |f i x| := le_abs_self _
      _ ≤ prefixLinearSeminorm f n x := by
        rw [prefixLinearSeminorm_apply]
        exact le_prefixEnvelope (fun j y => |f j y|) n i x hi
      _ ≤ signedLinearSeminorm f g n m x := le_max_left _ _

/-- Endpoint inequalities propagate throughout a nonnegative cone. -/
theorem linearMap_le_on_cone_of_endpoints (f g : E →ₗ[ℝ] ℝ) (a b : E)
    (ha : f a ≤ g a) (hb : f b ≤ g b) (x : E) (hx : x ∈ twoRayCone a b) : f x ≤ g x := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hx
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)

/-- Two local axis joins suffice to dominate the opposite family on a
quadrant. No norm existence or global fan convexity is assumed. -/
theorem signedLinearSeminorm_eq_on_quadrant
    (f g : ℕ → E →ₗ[ℝ] ℝ) (n m : ℕ) (a b : E) (L : ℝ)
    (hf0 : f 0 a = L) (hfn : f n b = L)
    (hg0 : g 0 b = L) (hgm : g m a = -L)
    (hga : ∀ j ≤ m, g m a ≤ g j a ∧ g j a ≤ g 0 a)
    (hgb : ∀ j ≤ m, g m b ≤ g j b ∧ g j b ≤ g 0 b)
    (haxis0 : g 0 a ≤ f n a) (haxis1 : -(f 0 b) ≤ g m b)
    (hmin : ∀ x ∈ twoRayCone a b, ∀ i ≤ n, min (f 0 x) (f n x) ≤ f i x)
    (x : E) (hx : x ∈ twoRayCone a b) :
    signedLinearSeminorm f g n m x = prefixEnvelope (fun i => f i) n x := by
  apply signedLinearSeminorm_eq_of_bounds f g n m x (hmin x hx)
  · obtain ⟨s, t, hs, ht, rfl⟩ := hx
    have ha : 0 ≤ f 0 a + f n a := by linarith [(hga 0 (Nat.zero_le _)).1]
    have hb : 0 ≤ f 0 b + f n b := by linarith [(hgb m le_rfl).2]
    have hsa := mul_nonneg hs ha
    have htb := mul_nonneg ht hb
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith
  · intro j hj
    constructor
    · exact linearMap_le_on_cone_of_endpoints (g j) (f n) a b
        ((hga j hj).2.trans haxis0) (by linarith [(hgb j hj).2]) x hx
    · have h := linearMap_le_on_cone_of_endpoints (-(g j)) (f 0) a b
        (by simp only [LinearMap.neg_apply]; linarith [(hga j hj).1])
        (by simp only [LinearMap.neg_apply]; linarith [(hgb j hj).1]) x hx
      exact h

/-- Ordered affine crossings imply the required exterior-piece lower bound
on a whole cone, by normalization to its affine section. -/
theorem linearFamily_min_on_cone (f : ℕ → E →ₗ[ℝ] ℝ) (n : ℕ) (a b : E) (r : ℕ → ℝ)
    (hslopes : ∀ j < n, f j b - f j a ≤ f (j + 1) b - f (j + 1) a)
    (hmatch : ∀ j < n,
      affinePiece (fun i => f i b - f i a) (fun i => f i a) j (r j) =
      affinePiece (fun i => f i b - f i a) (fun i => f i a) (j + 1) (r j))
    (hbreaks : ∀ j k, j ≤ k → k < n → r j ≤ r k)
    (x : E) (hx : x ∈ twoRayCone a b) (i : ℕ) (hi : i ≤ n) :
    min (f 0 x) (f n x) ≤ f i x := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hx
  by_cases hsum : s + t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0]
  · have hp : 0 < s + t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hsum)
    have he (j : ℕ) : f j (s • a + t • b) = (s + t) *
        affinePiece (fun k => f k b - f k a) (fun k => f k a) j (t / (s + t)) := by
      simp only [map_add, map_smul, smul_eq_mul, affinePiece]
      field_simp
      ring
    have hb := affinePiece_min_endpoints (fun j => f j b - f j a) (fun j => f j a)
      r n i (t / (s + t)) hi hslopes hmatch hbreaks
    rw [he 0, he n, he i, ← mul_min_of_nonneg _ _ hp.le]
    exact mul_le_mul_of_nonneg_left hb hp.le

theorem prefixLinearSeminorm_neg_apply (f : ℕ → E →ₗ[ℝ] ℝ) (n : ℕ) (x : E) :
    prefixLinearSeminorm (fun i => -(f i)) n x = prefixLinearSeminorm f n x := by
  simp only [prefixLinearSeminorm_apply, LinearMap.neg_apply, abs_neg]

theorem signedLinearSeminorm_swap_neg_apply (f g : ℕ → E →ₗ[ℝ] ℝ) (n m : ℕ) (x : E) :
    signedLinearSeminorm g (fun i => -(f i)) m n x = signedLinearSeminorm f g n m x := by
  change max (prefixLinearSeminorm g m x) (prefixLinearSeminorm (fun i => -(f i)) n x) =
    max (prefixLinearSeminorm f n x) (prefixLinearSeminorm g m x)
  rw [prefixLinearSeminorm_neg_apply, max_comm]

/-- The same two axis inequalities also give interpolation on the next
quadrant. Central evenness then covers the remaining two quadrants. -/
theorem signedLinearSeminorm_eq_on_next_quadrant
    (f g : ℕ → E →ₗ[ℝ] ℝ) (n m : ℕ) (a b : E) (L : ℝ)
    (hf0 : f 0 a = L) (hfn : f n b = L)
    (hg0 : g 0 b = L) (hgm : g m a = -L)
    (hfa : ∀ i ≤ n, f n a ≤ f i a ∧ f i a ≤ f 0 a)
    (hfb : ∀ i ≤ n, f 0 b ≤ f i b ∧ f i b ≤ f n b)
    (haxis0 : g 0 a ≤ f n a) (haxis1 : -(f 0 b) ≤ g m b)
    (hmin : ∀ x ∈ twoRayCone b (-a), ∀ j ≤ m, min (g 0 x) (g m x) ≤ g j x)
    (x : E) (hx : x ∈ twoRayCone b (-a)) :
    signedLinearSeminorm f g n m x = prefixEnvelope (fun j => g j) m x := by
  have h := signedLinearSeminorm_eq_on_quadrant g (fun i => -(f i)) m n b (-a) L
    hg0 (by simpa only [map_neg, neg_neg] using congrArg Neg.neg hgm)
    (by simpa only [LinearMap.neg_apply, map_neg, neg_neg] using hf0)
    (by simpa only [LinearMap.neg_apply] using congrArg Neg.neg hfn)
    (fun i hi => by
      simp only [LinearMap.neg_apply]
      constructor <;> linarith [(hfb i hi).1, (hfb i hi).2])
    (fun i hi => by simpa only [LinearMap.neg_apply, map_neg, neg_neg] using hfa i hi)
    (by simpa only [LinearMap.neg_apply] using haxis1)
    (by simpa only [LinearMap.neg_apply, map_neg, neg_neg] using haxis0)
    hmin x hx
  rw [signedLinearSeminorm_swap_neg_apply] at h
  exact h

end Markov
