import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! Convex gluing of finitely many affine pieces on the real line.
Ordered slopes and matching neighboring values make the prescribed pieces
agree with their global maximum on each cell. This is suitable for affine
slices of a finite planar fan; no fan or trace norm is assumed here. -/

namespace Markov

/-- The pointwise maximum of the first `n+1` functions. -/
def prefixEnvelope {E : Type*} (f : ℕ → E → ℝ) : ℕ → E → ℝ
  | 0 => f 0
  | n + 1 => fun x => max (prefixEnvelope f n x) (f (n + 1) x)

theorem prefixEnvelope_le {E : Type*} (f : ℕ → E → ℝ) (n : ℕ) (x : E) (z : ℝ)
    (h : ∀ j ≤ n, f j x ≤ z) : prefixEnvelope f n x ≤ z := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih => exact max_le (ih (fun j hj => h j (by omega))) (h _ le_rfl)

theorem le_prefixEnvelope {E : Type*} (f : ℕ → E → ℝ) (n i : ℕ) (x : E)
    (hi : i ≤ n) : f i x ≤ prefixEnvelope f n x := by
  induction n generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases hin : i ≤ n
    · exact (ih i hin).trans (le_max_left _ _)
    · have hi' : i = n + 1 := by omega
      subst i
      exact le_max_right _ _

/-- Increasing up to a selected piece and decreasing afterwards identifies
the pointwise maximum with that piece. -/
theorem prefixEnvelope_eq_of_adjacent {E : Type*} (f : ℕ → E → ℝ)
    (n i : ℕ) (x : E) (hi : i ≤ n)
    (hleft : ∀ j < i, f j x ≤ f (j + 1) x)
    (hright : ∀ j, i ≤ j → j < n → f (j + 1) x ≤ f j x) :
    prefixEnvelope f n x = f i x := by
  have hbefore : ∀ j ≤ i, f j x ≤ f i x := by
    intro j hji
    have hchain : ∀ m, j ≤ m → m ≤ i → f j x ≤ f m x := by
      intro m hjm
      induction m, hjm using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ m hjm ih =>
        intro hmi
        exact (ih (by omega)).trans (hleft m (by omega))
    exact hchain i hji le_rfl
  have hafter : ∀ j, i ≤ j → j ≤ n → f j x ≤ f i x := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hjn
      exact (hright j hij (by omega)).trans (ih (by omega))
  apply le_antisymm (prefixEnvelope_le f n x (f i x) ?_) (le_prefixEnvelope f n i x hi)
  intro j hj
  rcases le_total j i with hji | hij
  · exact hbefore j hji
  · exact hafter j hij hj

theorem prefixEnvelope_convexOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℕ → E → ℝ) (n : ℕ) (h : ∀ i ≤ n, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (prefixEnvelope f n) := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih => exact (ih (fun i hi => h i (by omega))).sup (h _ le_rfl)

/-- The affine line associated with one interval cell. -/
def affinePiece (a b : ℕ → ℝ) (i : ℕ) (x : ℝ) : ℝ := a i * x + b i

theorem affinePiece_convexOn (a b : ℕ → ℝ) (i : ℕ) :
    ConvexOn ℝ Set.univ (affinePiece a b i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β _ _ hab
  change a i * (α * x + β * y) + b i ≤
    α * (a i * x + b i) + β * (a i * y + b i)
  have he : a i * (α * x + β * y) + b i =
      α * (a i * x + b i) + β * (a i * y + b i) := by
    linear_combination -(b i) * hab
  exact he.le

theorem affinePiece_le_right (a b a' b' t x : ℝ) (ha : a ≤ a')
    (hmatch : a * t + b = a' * t + b') (hx : t ≤ x) : a * x + b ≤ a' * x + b' := by
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hx)
  nlinarith

theorem affinePiece_le_left (a b a' b' t x : ℝ) (ha : a ≤ a')
    (hmatch : a * t + b = a' * t + b') (hx : x ≤ t) : a' * x + b' ≤ a * x + b := by
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hx)
  nlinarith

/-- Exact cell identification, stated without endpoint-index conventions.
A cell lies after all preceding breakpoints and before all following ones. -/
theorem affineEnvelope_eq_on_cell (a b r : ℕ → ℝ) (n i : ℕ) (x : ℝ)
    (hi : i ≤ n)
    (hslopes : ∀ j < n, a j ≤ a (j + 1))
    (hmatch : ∀ j < n, affinePiece a b j (r j) = affinePiece a b (j + 1) (r j))
    (hleft : ∀ j < i, r j ≤ x)
    (hright : ∀ j, i ≤ j → j < n → x ≤ r j) :
    prefixEnvelope (affinePiece a b) n x = affinePiece a b i x := by
  apply prefixEnvelope_eq_of_adjacent (affinePiece a b) n i x hi
  · intro j hj
    exact affinePiece_le_right _ _ _ _ (r j) x (hslopes j (by omega))
      (hmatch j (by omega)) (hleft j hj)
  · intro j hij hjn
    exact affinePiece_le_left _ _ _ _ (r j) x (hslopes j hjn)
      (hmatch j hjn) (hright j hij hjn)

/-- The finite affine envelope is convex globally and realizes all prescribed
cells under the adjacent slope and matching conditions. -/
theorem finite_affine_gluing (a b r : ℕ → ℝ) (n : ℕ)
    (hslopes : ∀ j < n, a j ≤ a (j + 1))
    (hmatch : ∀ j < n, affinePiece a b j (r j) = affinePiece a b (j + 1) (r j)) :
    ConvexOn ℝ Set.univ (prefixEnvelope (affinePiece a b) n) ∧
      ∀ i ≤ n, ∀ x : ℝ, (∀ j < i, r j ≤ x) →
        (∀ j, i ≤ j → j < n → x ≤ r j) →
        prefixEnvelope (affinePiece a b) n x = affinePiece a b i x := by
  refine ⟨prefixEnvelope_convexOn _ n (fun i _ => affinePiece_convexOn a b i), ?_⟩
  intro i hi x hl hr
  exact affineEnvelope_eq_on_cell a b r n i x hi hslopes hmatch hl hr

/-- Ordered breakpoints reduce the cell conditions to its two endpoints;
the first and last cells are unbounded on their exterior side. -/
theorem affineEnvelope_eq_on_interval (a b r : ℕ → ℝ) (n i : ℕ) (x : ℝ)
    (hi : i ≤ n) (hr : Monotone r)
    (hslopes : ∀ j < n, a j ≤ a (j + 1))
    (hmatch : ∀ j < n, affinePiece a b j (r j) = affinePiece a b (j + 1) (r j))
    (hleft : i = 0 ∨ r (i - 1) ≤ x) (hright : i = n ∨ x ≤ r i) :
    prefixEnvelope (affinePiece a b) n x = affinePiece a b i x := by
  apply affineEnvelope_eq_on_cell a b r n i x hi hslopes hmatch
  · intro j hj
    rcases hleft with hi0 | hx
    · omega
    · exact (hr (by omega)).trans hx
  · intro j hij hjn
    rcases hright with hin | hx
    · omega
    · exact hx.trans (hr hij)

end Markov
