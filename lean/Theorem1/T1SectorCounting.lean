import T1SectorMarkovEquiv
import T1MarkovExceptionalCount

/-! The exact actual geometric sector count, before the full twelve-symmetry
orbit decomposition. The ball is defined by the genuine geometric norm. -/
noncomputable section
namespace Markov

def t1_geometricSectorSet (R : ℝ) : Set (ℤ × ℤ) :=
  {p | (0 < p.2 ∧ 2*p.2 < p.1 ∧ IsCoprime p.1 p.2) ∧ t1_geometricLength p ≤ R}

def t1_geometricSectorCount (R : ℝ) : ℕ := (t1_geometricSectorSet R).ncard

def t1_boundedSectorTripleEquiv (x : ℝ) (hx : 0 < x) :
    t1_geometricSectorSet (t1_markovLength x) ≃ t1_nonexceptionalTriplesUpTo x := by
  let es := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun p : ℤ × ℤ => 0 < p.2 ∧ 2*p.2 < p.1 ∧ IsCoprime p.1 p.2)
    (fun p => t1_geometricLength p ≤ t1_markovLength x)
  let et := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun t : ℕ × ℕ × ℕ => IsOrderedTriple t.1 t.2.1 t.2.2 ∧
      t ≠ (1,1,1) ∧ t ≠ (1,1,2))
    (fun t => (t.2.2 : ℝ) ≤ x)
  let e := Equiv.subtypeEquiv
    (p := fun p : t1_primitiveSector => t1_geometricLength p.val ≤ t1_markovLength x)
    (q := fun t : t1_nonexceptionalMarkovTriples => (t.val.2.2 : ℝ) ≤ x)
    t1_sectorTripleEquiv (fun p => t1_sectorTripleEquiv_cutoff p x hx)
  exact (es.symm.trans e).trans et

theorem t1_geometricSectorCount_eq_nonexceptional (x : ℝ) (hx : 0 < x) :
    t1_geometricSectorCount (t1_markovLength x) = (t1_nonexceptionalTriplesUpTo x).ncard :=
  Set.ncard_congr' (t1_boundedSectorTripleEquiv x hx)

theorem t1_geometricSectorCount_add_two (x : ℝ) (hx : 2 ≤ x) :
    t1_geometricSectorCount (t1_markovLength x) + 2 = countNat ⌊x⌋₊ := by
  rw [t1_geometricSectorCount_eq_nonexceptional x (by linarith)]
  exact t1_nonexceptionalTriplesUpTo_count x hx

theorem t1_geometricSectorCount_actual_markov_count (x : ℝ) (hx : 2 ≤ x) :
    count x = (t1_geometricSectorCount (t1_markovLength x) : ℝ) + 2 := by
  unfold count
  exact_mod_cast (t1_geometricSectorCount_add_two x hx).symm

end Markov
