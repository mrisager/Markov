import Mathlib

noncomputable section
namespace SquareSideNormalizer

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev SignedInterval := Set.Icc (-1 : ℝ) 1
abbrev Square := SignedInterval × SignedInterval

def h (s t : ℝ) : ℝ := (5 * t - 3 * s) / (5 - 3 * s * t)
def k (s t : ℝ) : ℝ := (5 * t + 3 * s) / (5 + 3 * s * t)

theorem h_den_pos {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    0 < 5 - 3 * s * t := by
  have hp : s * t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 hs.1).trans (by simpa using hs.2)
  nlinarith

theorem k_den_pos {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    0 < 5 + 3 * s * t := by
  have hp : -1 ≤ s * t := (show -1 ≤ -s by linarith [hs.2]).trans
    (by simpa using mul_le_mul_of_nonneg_left ht.1 hs.1)
  nlinarith

theorem h_mem {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    h s t ∈ Set.Icc (-1) 1 := by
  have hd := h_den_pos hs ht
  constructor
  · apply (le_div_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ 5 - 3*s by linarith [hs.2])
      (show 0 ≤ t+1 by linarith [ht.1])
    nlinarith
  · apply (div_le_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ 5 + 3*s by linarith [hs.1])
      (show 0 ≤ 1-t by linarith [ht.2])
    nlinarith

theorem k_mem {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    k s t ∈ Set.Icc (-1) 1 := by
  have hd := k_den_pos hs ht
  constructor
  · apply (le_div_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ 5 + 3*s by linarith [hs.1])
      (show 0 ≤ t+1 by linarith [ht.1])
    nlinarith
  · apply (div_le_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ 5 - 3*s by linarith [hs.2])
      (show 0 ≤ 1-t by linarith [ht.2])
    nlinarith

theorem h_k {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    h s (k s t) = t := by
  have hd := (k_den_pos hs ht).ne'
  have hu : k s t * (5 + 3*s*t) = 5*t + 3*s := div_mul_cancel₀ _ hd
  unfold h
  apply (div_eq_iff (h_den_pos hs (k_mem hs ht)).ne').2
  linear_combination hu

theorem k_h {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    k s (h s t) = t := by
  have hd := (h_den_pos hs ht).ne'
  have hu : h s t * (5 - 3*s*t) = 5*t - 3*s := div_mul_cancel₀ _ hd
  unfold k
  apply (div_eq_iff (k_den_pos hs (h_mem hs ht)).ne').2
  linear_combination hu


def hI (s : UnitInterval) (t : SignedInterval) : SignedInterval :=
  ⟨h s t, h_mem s.property t.property⟩

def kI (s : UnitInterval) (t : SignedInterval) : SignedInterval :=
  ⟨k s t, k_mem s.property t.property⟩

theorem continuous_hI : Continuous (fun p : UnitInterval × SignedInterval => hI p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : UnitInterval × SignedInterval =>
    (5 * (p.2 : ℝ) - 3 * (p.1 : ℝ)) / (5 - 3 * (p.1 : ℝ) * (p.2 : ℝ)))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    exact (h_den_pos p.1.property p.2.property).ne'

theorem continuous_kI : Continuous (fun p : UnitInterval × SignedInterval => kI p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : UnitInterval × SignedInterval =>
    (5 * (p.2 : ℝ) + 3 * (p.1 : ℝ)) / (5 + 3 * (p.1 : ℝ) * (p.2 : ℝ)))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    exact (k_den_pos p.1.property p.2.property).ne'

def intervalHomeomorph (s : UnitInterval) : SignedInterval ≃ₜ SignedInterval where
  toFun := hI s
  invFun := kI s
  left_inv t := Subtype.ext (k_h s.property t.property)
  right_inv t := Subtype.ext (h_k s.property t.property)
  continuous_toFun := continuous_hI.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := continuous_kI.comp (continuous_const.prodMk continuous_id)

def parameter (t : SignedInterval) : UnitInterval :=
  ⟨(1 - (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

theorem continuous_parameter : Continuous parameter := by
  apply Continuous.subtype_mk
  change Continuous (fun t : SignedInterval => (1 - (t : ℝ)) / 2)
  fun_prop

def horizontalHomeomorph : Square ≃ₜ Square where
  toFun p := (hI (parameter p.2) p.1, p.2)
  invFun p := (kI (parameter p.2) p.1, p.2)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (k_h (parameter p.2).property p.1.property)
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (h_k (parameter p.2).property p.1.property)
    · rfl
  continuous_toFun :=
    (continuous_hI.comp ((continuous_parameter.comp continuous_snd).prodMk continuous_fst)).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_kI.comp ((continuous_parameter.comp continuous_snd).prodMk continuous_fst)).prodMk
      continuous_snd

def verticalHomeomorph : Square ≃ₜ Square where
  toFun p := (p.1, hI (parameter p.1) p.2)
  invFun p := (p.1, kI (parameter p.1) p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (k_h (parameter p.1).property p.2.property)
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (h_k (parameter p.1).property p.2.property)
  continuous_toFun := continuous_fst.prodMk
    (continuous_hI.comp ((continuous_parameter.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (continuous_kI.comp ((continuous_parameter.comp continuous_fst).prodMk continuous_snd))

def squareHomeomorph : Square ≃ₜ Square := horizontalHomeomorph.trans verticalHomeomorph


def lo : SignedInterval := ⟨-1, by constructor <;> norm_num⟩
def hi : SignedInterval := ⟨1, by constructor <;> norm_num⟩
def zero : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def one : UnitInterval := ⟨1, by constructor <;> norm_num⟩

theorem h_zero (t : ℝ) : h 0 t = t := by simp [h]

theorem h_lo {s : ℝ} (hs : s ∈ Set.Icc 0 1) : h s (-1) = -1 := by
  unfold h
  apply (div_eq_iff (h_den_pos hs (show (-1 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)).ne').2
  ring

theorem h_hi {s : ℝ} (hs : s ∈ Set.Icc 0 1) : h s 1 = 1 := by
  unfold h
  apply (div_eq_iff (h_den_pos hs (show (1 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)).ne').2
  ring

@[simp] theorem parameter_lo : parameter lo = one := by ext; norm_num [parameter, lo, one]
@[simp] theorem parameter_hi : parameter hi = zero := by ext; norm_num [parameter, hi, zero]
@[simp] theorem hI_zero (t : SignedInterval) : hI zero t = t := by
  apply Subtype.ext
  exact h_zero t
@[simp] theorem hI_lo (s : UnitInterval) : hI s lo = lo := by
  apply Subtype.ext
  exact h_lo s.property
@[simp] theorem hI_hi (s : UnitInterval) : hI s hi = hi := by
  apply Subtype.ext
  exact h_hi s.property

@[simp] theorem square_top (a : SignedInterval) : squareHomeomorph (a, hi) = (a, hi) := by
  change (hI (parameter hi) a, hI (parameter (hI (parameter hi) a)) hi) = (a, hi)
  simp

@[simp] theorem square_right (b : SignedInterval) : squareHomeomorph (hi, b) = (hi, b) := by
  change (hI (parameter b) hi, hI (parameter (hI (parameter b) hi)) b) = (hi, b)
  simp

@[simp] theorem square_bottom (a : SignedInterval) :
    squareHomeomorph (a, lo) = (hI one a, lo) := by
  change (hI (parameter lo) a, hI (parameter (hI (parameter lo) a)) lo) = (hI one a, lo)
  simp

@[simp] theorem square_left (b : SignedInterval) :
    squareHomeomorph (lo, b) = (lo, hI one b) := by
  change (hI (parameter b) lo, hI (parameter (hI (parameter b) lo)) b) = (lo, hI one b)
  simp

def IsCorner (p : Square) : Prop := (p.1 = lo ∨ p.1 = hi) ∧ (p.2 = lo ∨ p.2 = hi)

theorem corner_fixed {p : Square} (hp : IsCorner p) : squareHomeomorph p = p := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨ha, hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem corner_iff (p : Square) : IsCorner p ↔ IsCorner (squareHomeomorph p) := by
  constructor
  · intro hp
    rwa [corner_fixed hp]
  · intro hp
    have he : squareHomeomorph (squareHomeomorph p) = squareHomeomorph p := corner_fixed hp
    have he' : squareHomeomorph p = p := squareHomeomorph.injective he
    rwa [he'] at hp

abbrev PuncturedSquare := {p : Square // ¬ IsCorner p}

def puncturedSquareHomeomorph : PuncturedSquare ≃ₜ PuncturedSquare :=
  squareHomeomorph.subtype (fun p => not_congr (corner_iff p))


theorem h_den_ge_two {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    2 ≤ 5 - 3 * s * t := by
  have hp : s * t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 hs.1).trans (by simpa using hs.2)
  nlinarith

theorem k_den_ge_two {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc (-1) 1) :
    2 ≤ 5 + 3 * s * t := by
  have hp : -1 ≤ s * t := (show -1 ≤ -s by linarith [hs.2]).trans
    (by simpa using mul_le_mul_of_nonneg_left ht.1 hs.1)
  nlinarith

@[simp] theorem hI_kI (s : UnitInterval) (t : SignedInterval) : hI s (kI s t) = t :=
  Subtype.ext (h_k s.property t.property)

@[simp] theorem kI_hI (s : UnitInterval) (t : SignedInterval) : kI s (hI s t) = t :=
  Subtype.ext (k_h s.property t.property)

theorem kI_one_coe (t : SignedInterval) :
    (kI one t : ℝ) = (5 * (t : ℝ) + 3) / (3 * (t : ℝ) + 5) := by
  change (5 * (t : ℝ) + 3*1) / (5 + 3*1*(t : ℝ)) = _
  congr 1 <;> ring

theorem square_bottom_paired (t : SignedInterval) :
    squareHomeomorph (kI one t, lo) = (t, lo) := by simp

theorem square_left_paired (t : SignedInterval) :
    squareHomeomorph (lo, kI one t) = (lo, t) := by simp

end SquareSideNormalizer

