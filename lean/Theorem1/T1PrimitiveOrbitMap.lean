import T1GeometricBoundaryOrbits
import T1SectorCounting

/-! The actual twelve-sector plus boundary map into the genuine primitive
geometric lattice count. The domain uses actual vectors and the original norm. -/
noncomputable section
open Classical
namespace Markov

def t1_boundaryOrbitFinset : Finset (ℤ × ℤ) := t1_shortOrbit ∪ t1_middleOrbit

theorem t1_boundaryOrbitFinset_card : t1_boundaryOrbitFinset.card = 12 := by
  rw [t1_boundaryOrbitFinset,Finset.card_union_of_disjoint t1_boundaryOrbits_disjoint,
    t1_shortOrbit_card,t1_middleOrbit_card]

theorem t1_mem_geometricPrimitiveCoordinates_norm (R : ℝ) (hR : 0 < R) (p : ℤ × ℤ) :
    p ∈ t1_geometricPrimitiveCoordinates R ↔ IsCoprime p.1 p.2 ∧ t1_geometricLength p ≤ R := by
  change (IsCoprime p.1 p.2 ∧ p ∈ modularMcShaneRivinCoordinateSet R) ↔ _
  rw [t1_mem_coordinate_norm_iff R hR]
  rfl

theorem t1_geometricSectorSet_finite (R : ℝ) (hR : 0 < R) :
    (t1_geometricSectorSet R).Finite := by
  apply (modularMcShaneRivinCoordinateSet_finite R hR).subset
  intro p hp
  exact (t1_mem_coordinate_norm_iff R hR p).mpr hp.2

def t1_primitiveOrbitDomain (x : ℝ) :=
  (Fin 6 × Bool × t1_geometricSectorSet (t1_markovLength x)) ⊕
    {p : ℤ × ℤ // p ∈ t1_boundaryOrbitFinset}

def t1_primitiveOrbitMap (x : ℝ) (hx : 2 ≤ x) :
    t1_primitiveOrbitDomain x → t1_geometricPrimitiveCoordinates (t1_markovLength x) := by
  intro a
  have hR : 0 < t1_markovLength x := t1_markovLength_pos x (by linarith)
  rcases a with ⟨k,b,p⟩ | p
  · refine ⟨t1_dihedralAction k b p.val,?_⟩
    apply (t1_mem_geometricPrimitiveCoordinates_norm _ hR _).mpr
    have hp := p.property.1.2.2
    refine ⟨(t1_dihedralAction_coprime_iff k b p.val).mpr hp,?_⟩
    rw [t1_geometricLength_dihedralAction k b p.val hp]
    exact p.property.2
  · refine ⟨p.val,?_⟩
    apply (t1_mem_geometricPrimitiveCoordinates_norm _ hR _).mpr
    exact t1_boundaryOrbits_length_le x hx p.val (Finset.mem_union.mp p.property)

theorem t1_primitiveOrbitMap_inl (x : ℝ) (hx : 2 ≤ x) (k : Fin 6) (b : Bool)
    (p : t1_geometricSectorSet (t1_markovLength x)) :
    (t1_primitiveOrbitMap x hx (Sum.inl (k,b,p))).val = t1_dihedralAction k b p.val := rfl

theorem t1_primitiveOrbitMap_inr (x : ℝ) (hx : 2 ≤ x)
    (p : {p : ℤ × ℤ // p ∈ t1_boundaryOrbitFinset}) :
    (t1_primitiveOrbitMap x hx (Sum.inr p)).val = p.val := rfl

end Markov
