import T1FareyMarkovWordMap
import T1FareyWordUnique
import T1FareyGeometricLength

/-! A genuine bijection from the primitive fundamental sector to actual
ordered Markov triples, with precisely the two small triples removed. -/
noncomputable section
namespace Markov

def t1_primitiveSector := {p : ℤ × ℤ //
  0 < p.2 ∧ 2*p.2 < p.1 ∧ IsCoprime p.1 p.2}

def t1_nonexceptionalMarkovTriples := {t : ℕ × ℕ × ℕ //
  IsOrderedTriple t.1 t.2.1 t.2.2 ∧ t ≠ (1,1,1) ∧ t ≠ (1,1,2)}

def t1_fareyWordSector (w : List Bool) : t1_primitiveSector :=
  ⟨t1_fareyWordDirection w, (t1_fareyWordDirection_strict w).1,
    (t1_fareyWordDirection_strict w).2,t1_fareyWordDirection_primitive w⟩

theorem t1_fareyWordSector_bijective : Function.Bijective t1_fareyWordSector := by
  constructor
  · intro w v he
    exact t1_fareyWordDirection_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨w,hw⟩ := t1_strict_sector_exists_farey_word p.val p.property.1
      p.property.2.1 p.property.2.2
    exact ⟨w,Subtype.ext hw⟩

def t1_wordSectorEquiv : List Bool ≃ t1_primitiveSector :=
  Equiv.ofBijective t1_fareyWordSector t1_fareyWordSector_bijective

theorem t1_fareyWordTriple_nonexceptional (w : List Bool) :
    t1_fareyWordTriple w ≠ (1,1,1) ∧ t1_fareyWordTriple w ≠ (1,1,2) := by
  have hs := (t1_fareyWordTriple_strict w).1
  constructor <;> intro he
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he
    simp only at h1 h2
    omega
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he
    simp only at h1 h2
    omega

def t1_fareyWordNonexceptionalTriple (w : List Bool) : t1_nonexceptionalMarkovTriples :=
  ⟨t1_fareyWordTriple w,t1_fareyWordTriple_ordered w,
    (t1_fareyWordTriple_nonexceptional w).1,(t1_fareyWordTriple_nonexceptional w).2⟩

theorem t1_fareyWordNonexceptionalTriple_bijective :
    Function.Bijective t1_fareyWordNonexceptionalTriple := by
  constructor
  · intro w v he
    exact t1_fareyWordTriple_injective (congrArg Subtype.val he)
  · rintro ⟨⟨p,q,r⟩,ht,hne1,hne2⟩
    rcases t1_ordered_markov_exception_or_farey_word p q r ht with h1 | h2 | ⟨w,hw⟩
    · exact (hne1 h1).elim
    · exact (hne2 h2).elim
    · exact ⟨w,Subtype.ext hw⟩

def t1_wordTripleEquiv : List Bool ≃ t1_nonexceptionalMarkovTriples :=
  Equiv.ofBijective t1_fareyWordNonexceptionalTriple t1_fareyWordNonexceptionalTriple_bijective

def t1_sectorTripleEquiv : t1_primitiveSector ≃ t1_nonexceptionalMarkovTriples :=
  t1_wordSectorEquiv.symm.trans t1_wordTripleEquiv

theorem t1_sectorTripleEquiv_length (p : t1_primitiveSector) :
    t1_geometricLength p.val = t1_markovLength (t1_sectorTripleEquiv p).val.2.2 := by
  let w := t1_wordSectorEquiv.symm p
  have hw : t1_wordSectorEquiv w = p := t1_wordSectorEquiv.apply_symm_apply p
  have hp : t1_fareyWordDirection w = p.val := congrArg Subtype.val hw
  rw [← hp,t1_fareyWord_geometric_length]
  rfl

theorem t1_sectorTripleEquiv_cutoff (p : t1_primitiveSector) (x : ℝ) (hx : 0 < x) :
    t1_geometricLength p.val ≤ t1_markovLength x ↔
      ((t1_sectorTripleEquiv p).val.2.2 : ℝ) ≤ x := by
  rw [t1_sectorTripleEquiv_length]
  have ho := (t1_sectorTripleEquiv p).property.1
  have hrN := ho.1.trans_le (ho.2.1.trans ho.2.2.1)
  exact t1_markovLength_le_iff _ x (by exact_mod_cast hrN) hx

end Markov
