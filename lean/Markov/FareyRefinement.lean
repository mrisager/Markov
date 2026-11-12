import Markov.FareyCoverage
import Markov.PrimitivePartner

/-! Actual finite Farey frontiers from the concrete seed. Every edge is
carried by its checked matrix witness. Refinement preserves old directions,
and every primitive nonnegative direction is eventually an endpoint. -/

namespace Markov

/-- An edge of the positive Farey tree with its actual integer matrices. -/
structure FareyEdge where
  u : ℤ × ℤ
  v : ℤ × ℤ
  M : IntMatrixTwo
  N : IntMatrixTwo
  holonomy : FareyHolonomy u v M N

def FareyEdge.seed : FareyEdge :=
  ⟨(1, 0), (0, 1), modularGeneratorA, modularGeneratorB, FareyHolonomy.seed⟩

def FareyEdge.left (e : FareyEdge) : FareyEdge :=
  ⟨e.u, e.u + e.v, e.M, e.M * e.N, e.holonomy.left⟩

def FareyEdge.right (e : FareyEdge) : FareyEdge :=
  ⟨e.u + e.v, e.v, e.M * e.N, e.N, e.holonomy.right⟩

def FareyEdge.refine (e : FareyEdge) : List FareyEdge := [e.left, e.right]

/-- The complete frontier after a fixed number of simultaneous mediant moves. -/
def fareyFrontier : ℕ → List FareyEdge
  | 0 => [FareyEdge.seed]
  | n + 1 => (fareyFrontier n).flatMap FareyEdge.refine

def fareyFrontierDirections (n : ℕ) : List (ℤ × ℤ) :=
  (fareyFrontier n).flatMap (fun e => [e.u, e.v])

theorem fareyFrontier_left_mem (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    e.left ∈ fareyFrontier (n + 1) := by
  exact List.mem_flatMap.mpr ⟨e, he, by simp [FareyEdge.refine]⟩

theorem fareyFrontier_right_mem (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n) :
    e.right ∈ fareyFrontier (n + 1) := by
  exact List.mem_flatMap.mpr ⟨e, he, by simp [FareyEdge.refine]⟩

/-- Every concrete tree witness is an edge of some finite simultaneous frontier. -/
theorem FareyHolonomy.exists_frontier {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : ∃ n : ℕ, (⟨u, v, M, N, h⟩ : FareyEdge) ∈ fareyFrontier n := by
  induction h with
  | seed => exact ⟨0, by simp [fareyFrontier, FareyEdge.seed]⟩
  | @left u v M N h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fareyFrontier_left_mem n ⟨u, v, M, N, h⟩ hn⟩
  | @right u v M N h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fareyFrontier_right_mem n ⟨u, v, M, N, h⟩ hn⟩

theorem fareyFrontier_endpoint_mem (n : ℕ) (e : FareyEdge) (he : e ∈ fareyFrontier n)
    (p : ℤ × ℤ) (hp : p = e.u ∨ p = e.v) : p ∈ fareyFrontierDirections n := by
  apply List.mem_flatMap.mpr
  exact ⟨e, he, by simpa using hp⟩

/-- Refining an edge preserves both of its old endpoint directions. -/
theorem fareyFrontierDirections_subset_succ (n : ℕ) :
    ∀ p ∈ fareyFrontierDirections n, p ∈ fareyFrontierDirections (n + 1) := by
  intro p hp
  obtain ⟨e, he, hp⟩ := List.mem_flatMap.mp hp
  simp at hp
  rcases hp with rfl | rfl
  · exact fareyFrontier_endpoint_mem (n + 1) e.left (fareyFrontier_left_mem n e he)
      e.u (Or.inl rfl)
  · exact fareyFrontier_endpoint_mem (n + 1) e.right (fareyFrontier_right_mem n e he)
      e.v (Or.inr rfl)

theorem fareyFrontierDirections_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ p ∈ fareyFrontierDirections n, p ∈ fareyFrontierDirections m := by
  induction hnm with
  | refl => exact fun _ hp => hp
  | @step m hm ih =>
    intro p hp
    exact fareyFrontierDirections_subset_succ m p (ih p hp)

/-- Every nonnegative primitive direction is present in a finite frontier. -/
theorem primitive_exists_frontier_direction (p : ℤ × ℤ)
    (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) (hp : IsCoprime p.1 p.2) :
    ∃ n : ℕ, p ∈ fareyFrontierDirections n := by
  obtain ⟨u, v, hu1, hu2, hv1, hv2, hd, hpv⟩ :=
    nonnegative_primitive_in_unimodular_pair p hp1 hp2 hp
  obtain ⟨M, N, h⟩ := exists_fareyHolonomy_of_nonnegative u v hu1 hu2 hv1 hv2 hd
  obtain ⟨n, hn⟩ := h.exists_frontier
  exact ⟨n, fareyFrontier_endpoint_mem n ⟨u, v, M, N, h⟩ hn p hpv⟩

/-- Once the direction appears, all later frontiers retain it. -/
theorem primitive_eventually_frontier_direction (p : ℤ × ℤ)
    (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) (hp : IsCoprime p.1 p.2) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → p ∈ fareyFrontierDirections m := by
  obtain ⟨n, hn⟩ := primitive_exists_frontier_direction p hp1 hp2 hp
  exact ⟨n, fun m hm => fareyFrontierDirections_mono hm p hn⟩

/-- Consecutive edges form an actual chain between the indicated endpoints. -/
def FareyEdgeChain : (ℤ × ℤ) → (ℤ × ℤ) → List FareyEdge → Prop
  | a, b, [] => a = b
  | a, b, e :: es => e.u = a ∧ FareyEdgeChain e.v b es

theorem FareyEdgeChain.refine (es : List FareyEdge) (a b : ℤ × ℤ)
    (h : FareyEdgeChain a b es) : FareyEdgeChain a b (es.flatMap FareyEdge.refine) := by
  induction es generalizing a with
  | nil => exact h
  | cons e es ih =>
    exact ⟨h.1, rfl, ih e.v h.2⟩

/-- Finite frontiers stay connected, with the coordinate axes as boundary. -/
theorem fareyFrontier_chain (n : ℕ) :
    FareyEdgeChain (1, 0) (0, 1) (fareyFrontier n) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact FareyEdgeChain.refine _ _ _ ih

/-- Real coordinates of an integral direction. -/
def refinementDirection (u : ℤ × ℤ) : ℝ × ℝ := (u.1, u.2)

theorem refinementDirection_add (u v : ℤ × ℤ) :
    refinementDirection (u + v) = refinementDirection u + refinementDirection v := by
  ext <;> simp [refinementDirection]

/-- The closed cone spanned by an edge's ordered primitive directions. -/
def InFareyCone (u v : ℤ × ℤ) (x : ℝ × ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • refinementDirection u + b • refinementDirection v

/-- Mediant subdivision preserves exactly the original closed cone. -/
theorem inFareyCone_refine (u v : ℤ × ℤ) (x : ℝ × ℝ) :
    InFareyCone u v x ↔ InFareyCone u (u + v) x ∨ InFareyCone (u + v) v x := by
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    by_cases hab : a ≤ b
    · right
      refine ⟨a, b - a, ha, sub_nonneg.mpr hab, ?_⟩
      rw [refinementDirection_add, hx]
      module
    · left
      refine ⟨a - b, b, sub_nonneg.mpr (le_of_not_ge hab), hb, ?_⟩
      rw [refinementDirection_add, hx]
      module
  · rintro (⟨a, b, ha, hb, hx⟩ | ⟨a, b, ha, hb, hx⟩)
    · refine ⟨a + b, b, add_nonneg ha hb, hb, ?_⟩
      rw [hx, refinementDirection_add]
      module
    · refine ⟨a, a + b, ha, add_nonneg ha hb, ?_⟩
      rw [hx, refinementDirection_add]
      module

/-- The union of edge cones is unchanged by simultaneous refinement. -/
theorem farey_refine_union_cones (es : List FareyEdge) (x : ℝ × ℝ) :
    (∃ e ∈ es.flatMap FareyEdge.refine, InFareyCone e.u e.v x) ↔
      ∃ e ∈ es, InFareyCone e.u e.v x := by
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨parent, hp, he⟩ := List.mem_flatMap.mp he
    simp [FareyEdge.refine] at he
    refine ⟨parent, hp, (inFareyCone_refine parent.u parent.v x).mpr ?_⟩
    rcases he with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro ⟨e, he, hx⟩
    rcases (inFareyCone_refine e.u e.v x).mp hx with hl | hr
    · refine ⟨e.left, List.mem_flatMap.mpr ⟨e, he, ?_⟩, hl⟩
      simp [FareyEdge.refine]
    · refine ⟨e.right, List.mem_flatMap.mpr ⟨e, he, ?_⟩, hr⟩
      simp [FareyEdge.refine]

/-- Every finite frontier actually covers the entire closed positive quadrant. -/
theorem fareyFrontier_covers_quadrant (n : ℕ) (x : ℝ × ℝ) :
    (∃ e ∈ fareyFrontier n, InFareyCone e.u e.v x) ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 := by
  induction n with
  | zero =>
    constructor
    · rintro ⟨e, he, a, b, ha, hb, hx⟩
      have he' : e = FareyEdge.seed := by simpa [fareyFrontier] using he
      subst e
      simp [FareyEdge.seed, refinementDirection] at hx
      simpa only [hx] using And.intro ha hb
    · rintro ⟨h1, h2⟩
      refine ⟨FareyEdge.seed, by simp [fareyFrontier], x.1, x.2, h1, h2, ?_⟩
      ext <;> simp [FareyEdge.seed, refinementDirection]
  | succ n ih => exact (farey_refine_union_cones (fareyFrontier n) x).trans ih

/-- Actual adjacency in an ordered finite edge list. -/
def FareyAdjacent (a b : FareyEdge) : List FareyEdge → Prop
  | e :: f :: es => (a = e ∧ b = f) ∨ FareyAdjacent a b (f :: es)
  | _ => False

theorem FareyAdjacent.tail {a b : FareyEdge} {es : List FareyEdge}
    (h : FareyAdjacent a b es) (e : FareyEdge) : FareyAdjacent a b (e :: es) := by
  cases es with
  | nil => exact False.elim h
  | cons f fs => exact Or.inr h

/-- Consecutive refined edges are either two children of one edge or the
right/left children of consecutive old edges. -/
theorem fareyAdjacent_refine_cases (es : List FareyEdge) (a b : FareyEdge)
    (h : FareyAdjacent a b (es.flatMap FareyEdge.refine)) :
    (∃ e ∈ es, a = e.left ∧ b = e.right) ∨
      (∃ e f, FareyAdjacent e f es ∧ a = e.right ∧ b = f.left) := by
  induction es with
  | nil => exact False.elim h
  | cons e es ih =>
    cases es with
    | nil =>
      have hh : a = e.left ∧ b = e.right := by
        simpa [FareyEdge.refine, FareyAdjacent] using h
      exact Or.inl ⟨e, by simp, hh⟩
    | cons f fs =>
      change (a = e.left ∧ b = e.right) ∨ (a = e.right ∧ b = f.left) ∨
        FareyAdjacent a b ((f :: fs).flatMap FareyEdge.refine) at h
      rcases h with hs | hb | hr
      · exact Or.inl ⟨e, by simp, hs⟩
      · exact Or.inr ⟨e, f, Or.inl ⟨rfl, rfl⟩, hb⟩
      · rcases ih hr with ⟨g, hg, ha, hb⟩ | ⟨g, g', hgg', ha, hb⟩
        · exact Or.inl ⟨g, by simp [hg], ha, hb⟩
        · exact Or.inr ⟨g, g', hgg'.tail e, ha, hb⟩

/-- Every finite frontier corner is a birth corner followed by equally many
ray moves on its two sides. In particular this characterizes all old corners. -/
theorem fareyFrontier_adjacent_birth (n : ℕ) (a b : FareyEdge)
    (h : FareyAdjacent a b (fareyFrontier n)) :
    ∃ (u v : ℤ × ℤ) (M N : IntMatrixTwo) (k : ℕ), FareyHolonomy u v M N ∧
      a.v = u + v ∧ b.u = u + v ∧
      a.u = k • (u + v) + u ∧ b.v = k • (u + v) + v := by
  induction n generalizing a b with
  | zero => exact False.elim h
  | succ n ih =>
    rcases fareyAdjacent_refine_cases (fareyFrontier n) a b h with hs | hb
    · obtain ⟨e, he, rfl, rfl⟩ := hs
      exact ⟨e.u, e.v, e.M, e.N, 0, e.holonomy, rfl, rfl, by simp [FareyEdge.left],
        by simp [FareyEdge.right]⟩
    · obtain ⟨e, f, hef, rfl, rfl⟩ := hb
      obtain ⟨u, v, M, N, k, hh, hev, hfu, heu, hfv⟩ := ih e f hef
      refine ⟨u, v, M, N, k + 1, hh, hev, hfu, ?_, ?_⟩
      · change e.u + e.v = (k + 1) • (u + v) + u
        rw [heu, hev, add_nsmul, one_nsmul]
        abel
      · change f.u + f.v = (k + 1) • (u + v) + v
        rw [hfu, hfv, add_nsmul, one_nsmul]
        abel

/-- Every refinement replaces exactly one edge by two. -/
theorem farey_refine_length (es : List FareyEdge) :
    (es.flatMap FareyEdge.refine).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [FareyEdge.refine, ih]; omega

theorem fareyFrontier_length (n : ℕ) : (fareyFrontier n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fareyFrontier, farey_refine_length, ih, pow_succ]
    omega

/-- Finite frontier labels are exactly of the required primitive arithmetic
kind; this uses their actual holonomy witnesses. -/
theorem fareyFrontier_direction_primitive (n : ℕ) (p : ℤ × ℤ)
    (hp : p ∈ fareyFrontierDirections n) : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ IsCoprime p.1 p.2 := by
  obtain ⟨e, _, hp⟩ := List.mem_flatMap.mp hp
  simp at hp
  rcases hp with rfl | rfl
  · exact ⟨e.holonomy.nonnegative_labels.1, e.holonomy.nonnegative_labels.2.1,
      e.holonomy.primitive_labels.1⟩
  · exact ⟨e.holonomy.nonnegative_labels.2.2.1, e.holonomy.nonnegative_labels.2.2.2,
      e.holonomy.primitive_labels.2⟩

/-- Exact arithmetic characterization of all finite-frontier directions. -/
theorem exists_frontier_direction_iff (p : ℤ × ℤ) :
    (∃ n : ℕ, p ∈ fareyFrontierDirections n) ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ IsCoprime p.1 p.2 := by
  constructor
  · rintro ⟨n, hn⟩
    exact fareyFrontier_direction_primitive n p hn
  · rintro ⟨h1, h2, hp⟩
    exact primitive_exists_frontier_direction p h1 h2 hp

end Markov
