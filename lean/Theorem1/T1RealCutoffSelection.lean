import T1GeometricCutoff

/-! An actual integer cutoff selected from real R,Y. The subtraction of
one ensures D+1 <= R/Y, with all floor and positivity bounds proved. -/
noncomputable section
namespace Markov

def t1_realCutoff (R Y : ℝ) : ℕ := ⌊R/Y⌋₊-1

theorem t1_realCutoff_bounds (R Y : ℝ) (hY : 0 < Y) (hRY : 4 ≤ R/Y) :
    0 < t1_realCutoff R Y ∧ R/(2*Y) ≤ (t1_realCutoff R Y : ℝ) ∧
      (t1_realCutoff R Y : ℝ)+1 ≤ R/Y := by
  have hu : 0 ≤ R/Y := by linarith
  have hN : 4 ≤ ⌊R/Y⌋₊ := (Nat.le_floor_iff hu).mpr (by norm_num; exact hRY)
  have hDcast : (t1_realCutoff R Y : ℝ) = (⌊R/Y⌋₊ : ℝ)-1 := by
    rw [t1_realCutoff,Nat.cast_sub (by omega),Nat.cast_one]
  have hfloor := Nat.floor_le hu
  have hlt := Nat.lt_floor_add_one (R/Y)
  refine ⟨by unfold t1_realCutoff; omega,?_,?_⟩
  · have hid : R/(2*Y) = (R/Y)/2 := by field_simp
    rw [hid,hDcast]
    linarith
  · rw [hDcast]
    linarith

theorem t1_realCutoff_radius (R Y : ℝ) (hY : 0 < Y) (hRY : 4 ≤ R/Y) :
    Y ≤ R / ((t1_realCutoff R Y : ℝ)+1) := by
  have hb := t1_realCutoff_bounds R Y hY hRY
  have hd : (0 : ℝ) < (t1_realCutoff R Y : ℝ)+1 := by positivity
  apply (le_div_iff₀ hd).mpr
  have hprod := (le_div_iff₀ hY).mp hb.2.2
  nlinarith

theorem t1_realCutoff_ratio (R Y : ℝ) (hY : 0 < Y) (hRY : 4 ≤ R/Y) :
    R / (t1_realCutoff R Y : ℝ) ≤ 2*Y := by
  have hb := t1_realCutoff_bounds R Y hY hRY
  have hd : (0 : ℝ) < (t1_realCutoff R Y : ℝ) := by exact_mod_cast hb.1
  apply (div_le_iff₀ hd).mpr
  have hprod := (div_le_iff₀ (show (0 : ℝ) < 2*Y by positivity)).mp hb.2.1
  nlinarith

end Markov
