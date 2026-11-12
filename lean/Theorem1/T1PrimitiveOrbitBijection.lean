import T1PrimitiveOrbitMap
import T1LatticeOrbitCoverage
import T1LatticeOrbitUnique

/-! The complete genuine twelve-sector plus twelve-boundary decomposition
of primitive points in the original geometric ball at the Markov cutoff. -/
noncomputable section
namespace Markov

theorem t1_primitiveOrbitMap_injective (x : ℝ) (hx : 2 ≤ x) :
    Function.Injective (t1_primitiveOrbitMap x hx) := by
  intro a b he
  have hv := congrArg Subtype.val he
  rcases a with ⟨k,c,p⟩ | p
  · rcases b with ⟨j,d,q⟩ | q
    · change t1_dihedralAction k c p.val = t1_dihedralAction j d q.val at hv
      have hu := t1_dihedralAction_strict_unique k j c d p.val q.val
        ⟨p.property.1.1,p.property.1.2.1⟩ ⟨q.property.1.1,q.property.1.2.1⟩ hv
      rcases hu with ⟨rfl,rfl,hpq⟩
      have hsub : p = q := Subtype.ext hpq
      subst q
      rfl
    · change t1_dihedralAction k c p.val = q.val at hv
      have hB : t1_dihedralAction k c p.val ∈ t1_shortOrbit ∪ t1_middleOrbit := by
        rw [hv]
        exact q.property
      have hn := t1_dihedralAction_strict_not_boundary k c p.val
        ⟨p.property.1.1,p.property.1.2.1⟩
      rcases Finset.mem_union.mp hB with hs | hm
      · exact (hn.1 hs).elim
      · exact (hn.2 hm).elim
  · rcases b with ⟨j,d,q⟩ | q
    · change p.val = t1_dihedralAction j d q.val at hv
      have hB : t1_dihedralAction j d q.val ∈ t1_shortOrbit ∪ t1_middleOrbit := by
        rw [← hv]
        exact p.property
      have hn := t1_dihedralAction_strict_not_boundary j d q.val
        ⟨q.property.1.1,q.property.1.2.1⟩
      rcases Finset.mem_union.mp hB with hs | hm
      · exact (hn.1 hs).elim
      · exact (hn.2 hm).elim
    · change p.val = q.val at hv
      exact congrArg Sum.inr (Subtype.ext hv)

theorem t1_primitiveOrbitMap_surjective (x : ℝ) (hx : 2 ≤ x) :
    Function.Surjective (t1_primitiveOrbitMap x hx) := by
  intro p
  have hR : 0 < t1_markovLength x := t1_markovLength_pos x (by linarith)
  have hp := (t1_mem_geometricPrimitiveCoordinates_norm _ hR p.val).mp p.property
  rcases t1_primitive_lattice_orbit_coverage p.val hp.1 with hs | hm | hi
  · exact ⟨Sum.inr ⟨p.val,Finset.mem_union.mpr (Or.inl hs)⟩,Subtype.ext rfl⟩
  · exact ⟨Sum.inr ⟨p.val,Finset.mem_union.mpr (Or.inr hm)⟩,Subtype.ext rfl⟩
  · obtain ⟨k,b,q,hq2,hq12,hcop,he⟩ := hi
    have hlen : t1_geometricLength q ≤ t1_markovLength x := by
      rw [← t1_geometricLength_dihedralAction k b q hcop,← he]
      exact hp.2
    let qs : t1_geometricSectorSet (t1_markovLength x) := ⟨q,⟨hq2,hq12,hcop⟩,hlen⟩
    exact ⟨Sum.inl (k,b,qs),Subtype.ext he.symm⟩

def t1_primitiveOrbitEquiv (x : ℝ) (hx : 2 ≤ x) :
    t1_primitiveOrbitDomain x ≃ t1_geometricPrimitiveCoordinates (t1_markovLength x) :=
  Equiv.ofBijective (t1_primitiveOrbitMap x hx)
    ⟨t1_primitiveOrbitMap_injective x hx,t1_primitiveOrbitMap_surjective x hx⟩

end Markov
