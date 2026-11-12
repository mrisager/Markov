import Markov.CanonicalTrace
import Markov.PrimitiveBirthCoverage

/-! Literal finite Farey paths in the fundamental positive half-quadrant.
Directions and integral matrices are computed by the same word. -/
namespace Markov

def t1_fareyWordDirections : List Bool → (ℤ × ℤ) × (ℤ × ℤ)
  | [] => ((1,0),(2,1))
  | false :: w => let (u,v) := t1_fareyWordDirections w; (u,u+v)
  | true :: w => let (u,v) := t1_fareyWordDirections w; (u+v,v)

def t1_fareyWordMatrices : List Bool → IntMatrixTwo × IntMatrixTwo
  | [] => (modularGeneratorA, modularGeneratorA * (modularGeneratorA * modularGeneratorB))
  | false :: w => let (M,N) := t1_fareyWordMatrices w; (M,M*N)
  | true :: w => let (M,N) := t1_fareyWordMatrices w; (M*N,N)

def t1_fareyWordDirection (w : List Bool) : ℤ × ℤ :=
  (t1_fareyWordDirections w).1 + (t1_fareyWordDirections w).2

theorem t1_fareyWord_holonomy (w : List Bool) :
    FareyHolonomy (t1_fareyWordDirections w).1 (t1_fareyWordDirections w).2
      (t1_fareyWordMatrices w).1 (t1_fareyWordMatrices w).2 := by
  induction w with
  | nil => exact FareyHolonomy.seed.left.left
  | cons b w ih => cases b with
    | false => exact ih.left
    | true => exact ih.right

theorem t1_fareyWord_seeded (w : List Bool) :
    SeededFarey (1,0) (2,1) modularGeneratorA (modularGeneratorA * (modularGeneratorA * modularGeneratorB))
      (t1_fareyWordDirections w).1 (t1_fareyWordDirections w).2
      (t1_fareyWordMatrices w).1 (t1_fareyWordMatrices w).2 := by
  induction w with
  | nil => exact SeededFarey.seed
  | cons b w ih => cases b with
    | false => exact ih.left
    | true => exact ih.right

theorem t1_fareyWord_cone (w : List Bool) :
    0 ≤ (t1_fareyWordDirections w).1.2 ∧
    2 * (t1_fareyWordDirections w).1.2 < (t1_fareyWordDirections w).1.1 ∧
    0 < (t1_fareyWordDirections w).2.2 ∧
    2 * (t1_fareyWordDirections w).2.2 ≤ (t1_fareyWordDirections w).2.1 := by
  induction w with
  | nil => norm_num [t1_fareyWordDirections]
  | cons b w ih =>
    rcases ih with ⟨h1,h2,h3,h4⟩
    cases b <;> simp only [t1_fareyWordDirections, Prod.fst_add, Prod.snd_add] at * <;> omega

theorem t1_fareyWordDirection_primitive (w : List Bool) :
    IsCoprime (t1_fareyWordDirection w).1 (t1_fareyWordDirection w).2 :=
  (t1_fareyWord_holonomy w).left.right_nonnegativePrimitive.2.2

theorem t1_fareyWordDirection_strict (w : List Bool) :
    0 < (t1_fareyWordDirection w).2 ∧
      2 * (t1_fareyWordDirection w).2 < (t1_fareyWordDirection w).1 := by
  have h := t1_fareyWord_cone w
  simp only [t1_fareyWordDirection, Prod.fst_add, Prod.snd_add]
  omega

theorem t1_seededFarey_exists_word {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1,0) (2,1) modularGeneratorA
      (modularGeneratorA * (modularGeneratorA * modularGeneratorB)) u v M N) :
    ∃ w : List Bool, t1_fareyWordDirections w = (u,v) ∧
      t1_fareyWordMatrices w = (M,N) := by
  induction h with
  | seed => exact ⟨[],rfl,rfl⟩
  | @left u v M N h ih =>
    obtain ⟨w,hw,hm⟩ := ih
    exact ⟨false::w, by simp only [t1_fareyWordDirections, hw],
      by simp only [t1_fareyWordMatrices, hm]⟩
  | @right u v M N h ih =>
    obtain ⟨w,hw,hm⟩ := ih
    exact ⟨true::w, by simp only [t1_fareyWordDirections, hw],
      by simp only [t1_fareyWordMatrices, hm]⟩

end Markov
