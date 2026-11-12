import T1BoundaryOrbits
import T1GeometricDihedral
import T1FareyGeometricLength

/-! Genuine lengths and primitiveness of both actual finite boundary
orbits. Their inclusion at the paper's length cutoff is proved explicitly. -/
noncomputable section
namespace Markov

theorem t1_geometricLength_short_seed : t1_geometricLength (1,0) = t1_markovLength 1 := by
  have hh : QuadrantWordTrace (1,0) 3 :=
    ⟨0,(1,0),(0,1),modularGeneratorA,modularGeneratorB,SeededFarey.seed,
      Or.inl ⟨rfl,modular_generators_det_trace.2.2.1.symm⟩⟩
  have he := t1_quadrantWordTrace_geometricLength (1,0) (by norm_num) 3 hh
  simpa only [t1_markovLength,Int.cast_ofNat,mul_one] using he

theorem t1_geometricLength_middle_seed : t1_geometricLength (2,1) = t1_markovLength 2 := by
  have hh : QuadrantWordTrace (2,1) 6 :=
    ⟨0,(1,0),(2,1),modularGeneratorA,modularGeneratorA*(modularGeneratorA*modularGeneratorB),
      SeededFarey.seed.left.left,Or.inr ⟨rfl,t1_fareyWord_seed_traces.2.1.symm⟩⟩
  have he := t1_quadrantWordTrace_geometricLength (2,1) (by norm_num) 6 hh
  norm_num [t1_markovLength] at he ⊢
  exact he

theorem t1_shortOrbit_primitive_length (p : ℤ × ℤ) (hp : p ∈ t1_shortOrbit) :
    IsCoprime p.1 p.2 ∧ t1_geometricLength p = t1_markovLength 1 := by
  rw [t1_shortOrbit_eq_turn_image] at hp
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  refine ⟨(t1_latticeTurn_coprime_iff k (1,0)).mpr (by norm_num),?_⟩
  rw [t1_geometricLength_turn k (1,0) (by norm_num),t1_geometricLength_short_seed]

theorem t1_middleOrbit_primitive_length (p : ℤ × ℤ) (hp : p ∈ t1_middleOrbit) :
    IsCoprime p.1 p.2 ∧ t1_geometricLength p = t1_markovLength 2 := by
  rw [t1_middleOrbit_eq_turn_image] at hp
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  refine ⟨(t1_latticeTurn_coprime_iff k (2,1)).mpr (by norm_num),?_⟩
  rw [t1_geometricLength_turn k (2,1) (by norm_num),t1_geometricLength_middle_seed]

theorem t1_markovLength_pos (x : ℝ) (hx : 1 ≤ x) : 0 < t1_markovLength x := by
  unfold t1_markovLength
  exact mul_pos (by norm_num) (Real.arcosh_pos (by linarith))

theorem t1_boundaryOrbits_length_le (x : ℝ) (hx : 2 ≤ x) (p : ℤ × ℤ)
    (hp : p ∈ t1_shortOrbit ∨ p ∈ t1_middleOrbit) :
    IsCoprime p.1 p.2 ∧ t1_geometricLength p ≤ t1_markovLength x := by
  have hx0 : 0 < x := by linarith
  rcases hp with hs | hm
  · obtain ⟨hc,hlen⟩ := t1_shortOrbit_primitive_length p hs
    refine ⟨hc,?_⟩
    rw [hlen,t1_markovLength_le_iff 1 x (by norm_num) hx0]
    linarith
  · obtain ⟨hc,hlen⟩ := t1_middleOrbit_primitive_length p hm
    refine ⟨hc,?_⟩
    rw [hlen,t1_markovLength_le_iff 2 x (by norm_num) hx0]
    exact hx

end Markov
