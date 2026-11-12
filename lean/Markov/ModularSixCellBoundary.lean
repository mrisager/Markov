import Markov.ModularClosedAdmissibility

/-! Exact equivalence of points in the six closed translated standard cells.
The relation keeps the actual return word and its cyclic quotient label.
It does not construct a polygon quotient or a polygon homeomorphism. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The ten actual SL return matrices, with their existing central-sign convention. -/
def modularClosedReturnWordAt : Fin 10 → SL(2, ℤ) :=
  ![1, ModularGroup.T, ModularGroup.T⁻¹, ModularGroup.S,
    ModularGroup.T * ModularGroup.S, ModularGroup.T⁻¹ * ModularGroup.S,
    ModularGroup.S * ModularGroup.T, ModularGroup.S * ModularGroup.T⁻¹,
    ModularGroup.T * ModularGroup.S * ModularGroup.T,
    ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹]

/-- The actual quotient exponent, taken in the six-element residue interval. -/
def modularClosedReturnResidue : Fin 10 → Fin 6 :=
  ![0, 1, 5, 3, 4, 2, 4, 2, 5, 1]

theorem modularTraceProjectiveQuotientT_inv_eq_pow_five :
    modularTraceProjectiveQuotientT⁻¹ = modularTraceProjectiveQuotientT ^ 5 := by
  symm
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_succ]
  exact modularTraceProjectiveQuotientT_pow_six

theorem modularTraceProjectiveQuotientS_eq_T_pow_three :
    modularTraceProjectiveQuotientS = modularTraceProjectiveQuotientT ^ 3 := by
  rw [modularTraceProjectiveQuotientS_eq_inv_T_pow_three]
  symm
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_add]
  exact modularTraceProjectiveQuotientT_pow_six

theorem modularTraceProjectiveQuotientT_pow_mod_six (n : ℕ) :
    modularTraceProjectiveQuotientT ^ n =
      modularTraceProjectiveQuotientT ^ (n % 6) := by
  simpa only [modularTraceProjectiveQuotientT_orderOf] using
    (pow_mod_orderOf modularTraceProjectiveQuotientT n).symm

theorem modularClosedReturnWordAt_mem (i : Fin 10) :
    modularClosedReturnWordAt i ∈ modularClosedReturnWords := by
  classical
  fin_cases i <;> simp [modularClosedReturnWordAt, modularClosedReturnWords]

theorem modularClosedReturnWords_mem_iff (g : SL(2, ℤ)) :
    g ∈ modularClosedReturnWords ↔ ∃ i : Fin 10, modularClosedReturnWordAt i = g := by
  classical
  constructor
  · intro hg
    simp only [modularClosedReturnWords, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨1, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨2, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨3, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨4, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨5, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨6, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨7, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨8, by simpa [modularClosedReturnWordAt] using h.symm⟩
    · exact ⟨9, by simpa [modularClosedReturnWordAt] using h.symm⟩
  · rintro ⟨i, rfl⟩
    exact modularClosedReturnWordAt_mem i

/-- Exact cyclic labels of the ten actual words, without identifying
words that merely have the same quotient label. -/
theorem modularClosedReturnWordAt_quotient (i : Fin 10) :
    modularTraceProjectiveQuotientMap (modularClosedReturnWordAt i) =
      modularTraceProjectiveQuotientT ^ (modularClosedReturnResidue i).val := by
  have hS : modularTraceProjectiveQuotientMap ModularGroup.S =
      modularTraceProjectiveQuotientT ^ 3 :=
    modularTraceProjectiveQuotientS_eq_T_pow_three
  have hT : modularTraceProjectiveQuotientMap ModularGroup.T =
      modularTraceProjectiveQuotientT := rfl
  fin_cases i <;>
    simp [modularClosedReturnWordAt, modularClosedReturnResidue,
      hS, hT, modularTraceProjectiveQuotientT_inv_eq_pow_five] <;>
    try simp only [← pow_add]
  all_goals
    norm_num only [Nat.reduceAdd]
    first
    | rfl
    | (solve | group)
    | rw [modularTraceProjectiveQuotientT_pow_mod_six] <;> norm_num


/-- Projective cyclic labels forget the central matrix sign. -/
theorem modularTraceProjectiveQuotientMap_neg (g : SL(2, ℤ)) :
    modularTraceProjectiveQuotientMap (-g) = modularTraceProjectiveQuotientMap g := by
  exact congrArg (QuotientGroup.mk' modularTraceProjectiveSubgroup)
    ((modularIntegralProjectivization_eq_iff (-g) g).mpr (Or.inr rfl))

/-- The projective cyclic kernel is the union of the two central signs of the
actual special-linear trace subgroup. -/
theorem modularTraceProjectiveQuotientMap_eq_one_iff (g : SL(2, ℤ)) :
    modularTraceProjectiveQuotientMap g = 1 ↔
      g ∈ modularTraceSubgroup ∨ -g ∈ modularTraceSubgroup := by
  change (QuotientGroup.mk' modularTraceProjectiveSubgroup)
    (modularIntegralProjectivization g) = 1 ↔ _
  constructor
  · intro h
    exact (modularIntegralProjectivization_mem_trace_iff g).mp
      ((QuotientGroup.eq_one_iff (modularIntegralProjectivization g)).mp h)
  · intro h
    exact (QuotientGroup.eq_one_iff (modularIntegralProjectivization g)).mpr
      ((modularIntegralProjectivization_mem_trace_iff g).mpr h)

/-- An actual trace deck transformation has trivial cyclic label. -/
theorem modularTraceProjectiveQuotientMap_subgroup (g : modularTraceSubgroup) :
    modularTraceProjectiveQuotientMap g.val = 1 :=
  (modularTraceProjectiveQuotientMap_eq_one_iff g.val).mpr (Or.inl g.property)

/-- The residual matrix is `T⁻ˢ γ Tʳ`, so its label is `t⁻ˢ tʳ`.
Both central signs of the reverse residual matrix are retained. -/
theorem modularTraceSixCell_action_iff (r s : Fin 6) (z w : UpperHalfPlane) :
    (∃ γ : modularTraceSubgroup,
      γ • (ModularGroup.T ^ r.val • z) = ModularGroup.T ^ s.val • w) ↔
    ∃ h : SL(2, ℤ), h • z = w ∧
      modularTraceProjectiveQuotientMap h =
        (modularTraceProjectiveQuotientT ^ s.val)⁻¹ *
          modularTraceProjectiveQuotientT ^ r.val := by
  constructor
  · rintro ⟨γ, hγ⟩
    let h : SL(2, ℤ) := (ModularGroup.T ^ s.val)⁻¹ * γ.val * ModularGroup.T ^ r.val
    refine ⟨h, ?_, ?_⟩
    · have hγ' : γ.val • (ModularGroup.T ^ r.val • z) =
          ModularGroup.T ^ s.val • w := hγ
      dsimp only [h]
      rw [mul_smul, mul_smul, hγ', inv_smul_smul]
    · simp only [h, map_mul, map_inv, map_pow,
        modularTraceProjectiveQuotientMap_subgroup, mul_one]
      rfl
  · rintro ⟨h, hact, hlabel⟩
    let a : SL(2, ℤ) := ModularGroup.T ^ s.val * h * (ModularGroup.T ^ r.val)⁻¹
    have ha : modularTraceProjectiveQuotientMap a = 1 := by
      dsimp only [a]
      rw [map_mul, map_mul, map_pow, map_inv, map_pow]
      change (modularTraceProjectiveQuotientT ^ s.val *
        modularTraceProjectiveQuotientMap h) *
          (modularTraceProjectiveQuotientT ^ r.val)⁻¹ = 1
      rw [hlabel]
      group
    have hact' : a • (ModularGroup.T ^ r.val • z) =
        ModularGroup.T ^ s.val • w := by
      dsimp only [a]
      rw [mul_smul, mul_smul, inv_smul_smul, hact]
    rcases (modularTraceProjectiveQuotientMap_eq_one_iff a).mp ha with ha | ha
    · exact ⟨⟨a, ha⟩, hact'⟩
    · refine ⟨⟨-a, ha⟩, ?_⟩
      change (-a) • (ModularGroup.T ^ r.val • z) = ModularGroup.T ^ s.val • w
      rw [ModularGroup.SL_neg_smul]
      exact hact'

/-- Orbit equality in two translated cells is equivalent to the correctly
oriented residual matrix and cyclic label, before any domain assumptions. -/
theorem modularTraceSixCell_quotient_eq_iff (r s : Fin 6) (z w : UpperHalfPlane) :
    modularTraceQuotientMk (ModularGroup.T ^ r.val • z) =
      modularTraceQuotientMk (ModularGroup.T ^ s.val • w) ↔
    ∃ h : SL(2, ℤ), h • z = w ∧
      modularTraceProjectiveQuotientMap h =
        (modularTraceProjectiveQuotientT ^ s.val)⁻¹ *
          modularTraceProjectiveQuotientT ^ r.val := by
  constructor
  · intro heq
    apply (modularTraceSixCell_action_iff r s z w).mp
    exact (modularTraceQuotientMk_eq_iff _ _).mp heq.symm
  · intro h
    have hact := (modularTraceSixCell_action_iff r s z w).mpr h
    exact ((modularTraceQuotientMk_eq_iff _ _).mpr hact).symm

/-- Exact closed six-cell boundary equivalence. The word, its source-side or
corner condition, and the cyclic source/target residue are all retained. -/
theorem modularTraceSixCell_closed_quotient_eq_iff (r s : Fin 6)
    (z w : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hw : w ∈ ModularGroup.fd) :
    modularTraceQuotientMk (ModularGroup.T ^ r.val • z) =
      modularTraceQuotientMk (ModularGroup.T ^ s.val • w) ↔
    ∃ h ∈ modularClosedReturnWords,
      ModularClosedAdmissible h z ∧ h • z = w ∧
      modularTraceProjectiveQuotientMap h =
        (modularTraceProjectiveQuotientT ^ s.val)⁻¹ *
          modularTraceProjectiveQuotientT ^ r.val := by
  constructor
  · intro heq
    obtain ⟨a, hact, hlabel⟩ := (modularTraceSixCell_quotient_eq_iff r s z w).mp heq
    have hret : a • z ∈ ModularGroup.fd := hact.symm ▸ hw
    obtain ⟨h, hh, hah, hadm⟩ :=
      (modularClosedDomain_signed_return_iff a z hz).mp hret
    refine ⟨h, hh, hadm, ?_, ?_⟩
    · rcases hah with rfl | rfl
      · exact hact
      · simpa only [ModularGroup.SL_neg_smul] using hact
    · rcases hah with rfl | rfl
      · exact hlabel
      · simpa only [modularTraceProjectiveQuotientMap_neg] using hlabel
  · rintro ⟨h, _, _, hact, hlabel⟩
    exact (modularTraceSixCell_quotient_eq_iff r s z w).mpr ⟨h, hact, hlabel⟩

/-- A natural exponent label belongs to the source/target residue exactly when
adding it to the target cell index gives the source index modulo six. -/
theorem modularTraceSixCell_label_pow_iff (r s : Fin 6) (j : ℕ) :
    modularTraceProjectiveQuotientT ^ j =
      (modularTraceProjectiveQuotientT ^ s.val)⁻¹ *
        modularTraceProjectiveQuotientT ^ r.val ↔
      (s.val + j) % 6 = r.val := by
  rw [eq_inv_mul_iff_mul_eq, ← pow_add, pow_inj_mod,
    modularTraceProjectiveQuotientT_orderOf, Nat.mod_eq_of_lt r.isLt]

/-- The closed six-cell relation with an explicit word exponent and ordinary
modulo-six residue, preserving all side and corner conditions. -/
theorem modularTraceSixCell_closed_quotient_eq_iff_residue (r s : Fin 6)
    (z w : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hw : w ∈ ModularGroup.fd) :
    modularTraceQuotientMk (ModularGroup.T ^ r.val • z) =
      modularTraceQuotientMk (ModularGroup.T ^ s.val • w) ↔
    ∃ h ∈ modularClosedReturnWords, ∃ j : Fin 6,
      ModularClosedAdmissible h z ∧ h • z = w ∧
      modularTraceProjectiveQuotientMap h = modularTraceProjectiveQuotientT ^ j.val ∧
      (s.val + j.val) % 6 = r.val := by
  rw [modularTraceSixCell_closed_quotient_eq_iff r s z w hz hw]
  constructor
  · rintro ⟨h, hh, hadm, hact, hlabel⟩
    obtain ⟨j, hj⟩ := modularTraceQuotient_T_pow_representative h
    refine ⟨h, hh, j, hadm, hact, hj.symm, ?_⟩
    exact (modularTraceSixCell_label_pow_iff r s j.val).mp (hj.trans hlabel)
  · rintro ⟨h, hh, j, hadm, hact, hpow, hres⟩
    refine ⟨h, hh, hadm, hact, ?_⟩
    exact hpow.trans ((modularTraceSixCell_label_pow_iff r s j.val).mpr hres)

/-- The finite ten-word closed-cell equivalence, with the literal word table
and its exact modulo-six source/target condition. -/
theorem modularTraceSixCell_closed_quotient_eq_iff_word_index (r s : Fin 6)
    (z w : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hw : w ∈ ModularGroup.fd) :
    modularTraceQuotientMk (ModularGroup.T ^ r.val • z) =
      modularTraceQuotientMk (ModularGroup.T ^ s.val • w) ↔
    ∃ i : Fin 10,
      ModularClosedAdmissible (modularClosedReturnWordAt i) z ∧
      modularClosedReturnWordAt i • z = w ∧
      (s.val + (modularClosedReturnResidue i).val) % 6 = r.val := by
  rw [modularTraceSixCell_closed_quotient_eq_iff r s z w hz hw]
  constructor
  · rintro ⟨h, hh, hadm, hact, hlabel⟩
    obtain ⟨i, rfl⟩ := (modularClosedReturnWords_mem_iff h).mp hh
    refine ⟨i, hadm, hact, ?_⟩
    apply (modularTraceSixCell_label_pow_iff r s _).mp
    exact (modularClosedReturnWordAt_quotient i).symm.trans hlabel
  · rintro ⟨i, hadm, hact, hres⟩
    refine ⟨modularClosedReturnWordAt i, modularClosedReturnWordAt_mem i,
      hadm, hact, ?_⟩
    exact (modularClosedReturnWordAt_quotient i).trans
      ((modularTraceSixCell_label_pow_iff r s _).mpr hres)

end Markov
