import Markov.FareyRefinement
import Mathlib.Data.List.GetD

/-! Natural-number indexing of the actual finite Farey frontiers. The
index bounds are explicit, so no default edge is used within the frontier. -/

namespace Markov

/-- The actual edge at a natural index; outside the frontier the seed is
used only to make the function total. -/
def indexedFareyEdge (n i : ℕ) : FareyEdge := (fareyFrontier n).getD i FareyEdge.seed

theorem fareyAdjacent_getD (es : List FareyEdge) (d : FareyEdge) (i : ℕ)
    (hi : i + 1 < es.length) : FareyAdjacent (es.getD i d) (es.getD (i + 1) d) es := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero =>
      cases es with
      | nil => simp at hi
      | cons f fs => exact Or.inl ⟨rfl, rfl⟩
    | succ i =>
      have hlt : i + 1 < es.length := by simp only [List.length_cons] at hi; omega
      simpa only [List.getD_cons_succ] using (ih i hlt).tail e

/-- Adjacent list edges share their actual endpoint when the list is a chain. -/
theorem FareyEdgeChain.adjacent_shared {es : List FareyEdge} {lo hi : ℤ × ℤ}
    (hchain : FareyEdgeChain lo hi es) {a b : FareyEdge} (h : FareyAdjacent a b es) :
    a.v = b.u := by
  induction es generalizing lo with
  | nil => exact False.elim h
  | cons e es ih =>
    cases es with
    | nil => exact False.elim h
    | cons f fs =>
      rcases h with ⟨rfl, rfl⟩ | ht
      · exact hchain.2.1.symm
      · exact ih hchain.2 ht

/-- The first edge of a nonempty chain starts at its prescribed boundary. -/
theorem FareyEdgeChain.first_getD {es : List FareyEdge} {lo hi : ℤ × ℤ}
    (hchain : FareyEdgeChain lo hi es) (hne : 0 < es.length) (d : FareyEdge) :
    (es.getD 0 d).u = lo := by
  cases es with
  | nil => simp at hne
  | cons e es => exact hchain.1

/-- An index certified to be last has the prescribed terminal endpoint. -/
theorem FareyEdgeChain.last_getD {es : List FareyEdge} {lo hi : ℤ × ℤ}
    (hchain : FareyEdgeChain lo hi es) (i : ℕ) (hlast : i + 1 = es.length) (d : FareyEdge) :
    (es.getD i d).v = hi := by
  induction es generalizing lo i with
  | nil => simp at hlast
  | cons e es ih =>
    cases i with
    | zero =>
      have hes : es = [] := by simpa using hlast.symm
      subst es
      exact hchain.2
    | succ i =>
      have hlen : i + 1 = es.length := by simp only [List.length_cons] at hlast; omega
      simpa only [List.getD_cons_succ] using ih hchain.2 i hlen

/-- Valid indexed edges are genuine members of the finite frontier. -/
theorem indexedFareyEdge_mem (n i : ℕ) (hi : i < 2 ^ n) :
    indexedFareyEdge n i ∈ fareyFrontier n := by
  have hlen : i < (fareyFrontier n).length := by rwa [fareyFrontier_length]
  rw [indexedFareyEdge, List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem _

/-- Every edge in a frontier has a valid index; there are no indexing holes. -/
theorem fareyFrontier_mem_exists_index (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    ∃ i : ℕ, i < 2 ^ n ∧ indexedFareyEdge n i = e := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  refine ⟨i, by simpa only [fareyFrontier_length] using hi, ?_⟩
  rw [indexedFareyEdge, List.getD_eq_getElem _ _ hi]
  exact heq

theorem indexedFareyEdge_adjacent (n i : ℕ) (hi : i + 1 < 2 ^ n) :
    FareyAdjacent (indexedFareyEdge n i) (indexedFareyEdge n (i + 1)) (fareyFrontier n) := by
  exact fareyAdjacent_getD _ _ i (by simpa only [fareyFrontier_length] using hi)

theorem indexedFareyEdge_shared_endpoint (n i : ℕ) (hi : i + 1 < 2 ^ n) :
    (indexedFareyEdge n i).v = (indexedFareyEdge n (i + 1)).u :=
  (fareyFrontier_chain n).adjacent_shared (indexedFareyEdge_adjacent n i hi)

theorem indexedFareyEdge_first (n : ℕ) : (indexedFareyEdge n 0).u = (1, 0) := by
  apply (fareyFrontier_chain n).first_getD
  rw [fareyFrontier_length]
  positivity

theorem indexedFareyEdge_last (n : ℕ) : (indexedFareyEdge n (2 ^ n - 1)).v = (0, 1) := by
  apply (fareyFrontier_chain n).last_getD
  rw [fareyFrontier_length]
  have hp : 0 < 2 ^ n := by positivity
  omega

/-- Every actual adjacent indexed corner has the checked birth/ray form. -/
theorem indexedFareyEdge_adjacent_birth (n i : ℕ) (hi : i + 1 < 2 ^ n) :
    ∃ (u v : ℤ × ℤ) (M N : IntMatrixTwo) (k : ℕ), FareyHolonomy u v M N ∧
      (indexedFareyEdge n i).v = u + v ∧ (indexedFareyEdge n (i + 1)).u = u + v ∧
      (indexedFareyEdge n i).u = k • (u + v) + u ∧
      (indexedFareyEdge n (i + 1)).v = k • (u + v) + v :=
  fareyFrontier_adjacent_birth n _ _ (indexedFareyEdge_adjacent n i hi)

end Markov
