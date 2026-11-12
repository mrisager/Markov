import Markov.SquareSideNormalizer
import Markov.PaperQuadrilateralSquareChart

noncomputable section
namespace SquareSideNormalizer

theorem isCorner_iff_mem_paperSquareCorners (p : Square) :
    IsCorner p ↔ ((p.1 : ℝ), (p.2 : ℝ)) ∈ Markov.paperSquareCorners := by
  simp only [IsCorner, Subtype.ext_iff, lo, hi, Markov.paperSquareCorners,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  tauto

def toPaperPuncturedSquare (p : PuncturedSquare) : Markov.paperPuncturedSquare :=
  ⟨((p.val.1 : ℝ), (p.val.2 : ℝ)), by
    rw [Markov.paperPuncturedSquare_eq_square_diff_corners]
    exact ⟨⟨abs_le.mpr p.val.1.property, abs_le.mpr p.val.2.property⟩,
      fun hc => p.property ((isCorner_iff_mem_paperSquareCorners p.val).mpr hc)⟩⟩

def fromPaperPuncturedSquare (p : Markov.paperPuncturedSquare) : PuncturedSquare :=
  ⟨(⟨p.val.1, abs_le.mp p.property.1⟩, ⟨p.val.2, abs_le.mp p.property.2.1⟩), by
    intro hc
    have hp := (Set.ext_iff.mp Markov.paperPuncturedSquare_eq_square_diff_corners p.val).mp p.property
    exact hp.2 ((isCorner_iff_mem_paperSquareCorners _).mp hc)⟩

def paperPuncturedSquareCoordinatesHomeomorph : PuncturedSquare ≃ₜ Markov.paperPuncturedSquare where
  toFun := toPaperPuncturedSquare
  invFun := fromPaperPuncturedSquare
  left_inv p := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.fst.subtype_val).prodMk
      (continuous_subtype_val.snd.subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.fst).subtype_mk _).prodMk
      ((continuous_subtype_val.snd).subtype_mk _)

def paperPuncturedSquareHomeomorph : Markov.paperPuncturedSquare ≃ₜ Markov.paperPuncturedSquare :=
  paperPuncturedSquareCoordinatesHomeomorph.symm.trans
    (puncturedSquareHomeomorph.trans paperPuncturedSquareCoordinatesHomeomorph)


theorem paper_normalizer_val (p : Markov.paperPuncturedSquare) :
    (paperPuncturedSquareHomeomorph p).val =
      (((squareHomeomorph (fromPaperPuncturedSquare p).val).1 : ℝ),
        ((squareHomeomorph (fromPaperPuncturedSquare p).val).2 : ℝ)) := rfl

theorem paper_normalizer_top (p : Markov.paperPuncturedSquare) (hp : p.val.2 = 1) :
    paperPuncturedSquareHomeomorph p = p := by
  let q := fromPaperPuncturedSquare p
  have hq : q.val.2 = hi := Subtype.ext hp
  have hq' : q.val = (q.val.1, hi) := Prod.ext rfl hq
  have he : squareHomeomorph q.val = q.val := by
    rw [hq']
    exact square_top _
  apply Subtype.ext
  rw [paper_normalizer_val]
  change (((squareHomeomorph q.val).1 : ℝ), ((squareHomeomorph q.val).2 : ℝ)) = p.val
  rw [he]
  rfl

theorem paper_normalizer_right (p : Markov.paperPuncturedSquare) (hp : p.val.1 = 1) :
    paperPuncturedSquareHomeomorph p = p := by
  let q := fromPaperPuncturedSquare p
  have hq : q.val.1 = hi := Subtype.ext hp
  have hq' : q.val = (hi, q.val.2) := Prod.ext hq rfl
  have he : squareHomeomorph q.val = q.val := by
    rw [hq']
    exact square_right _
  apply Subtype.ext
  rw [paper_normalizer_val]
  change (((squareHomeomorph q.val).1 : ℝ), ((squareHomeomorph q.val).2 : ℝ)) = p.val
  rw [he]
  rfl

theorem paper_normalizer_bottom (p : Markov.paperPuncturedSquare) (hp : p.val.2 = -1) :
    (paperPuncturedSquareHomeomorph p).val = (h 1 p.val.1, -1) := by
  let q := fromPaperPuncturedSquare p
  have hq : q.val.2 = lo := Subtype.ext hp
  have hq' : q.val = (q.val.1, lo) := Prod.ext rfl hq
  rw [paper_normalizer_val]
  change (((squareHomeomorph q.val).1 : ℝ), ((squareHomeomorph q.val).2 : ℝ)) = _
  rw [hq', square_bottom]
  rfl

theorem paper_normalizer_left (p : Markov.paperPuncturedSquare) (hp : p.val.1 = -1) :
    (paperPuncturedSquareHomeomorph p).val = (-1, h 1 p.val.2) := by
  let q := fromPaperPuncturedSquare p
  have hq : q.val.1 = lo := Subtype.ext hp
  have hq' : q.val = (lo, q.val.2) := Prod.ext hq rfl
  rw [paper_normalizer_val]
  change (((squareHomeomorph q.val).1 : ℝ), ((squareHomeomorph q.val).2 : ℝ)) = _
  rw [hq', square_left]
  rfl

theorem paper_normalizer_bottom_paired (p : Markov.paperPuncturedSquare) (t : ℝ)
    (ht : t ∈ Set.Icc (-1) 1)
    (hp : p.val = ((5*t+3)/(3*t+5), -1)) :
    (paperPuncturedSquareHomeomorph p).val = (t, -1) := by
  rw [paper_normalizer_bottom p (congrArg Prod.snd hp)]
  have hx : p.val.1 = k 1 t := by
    have hx := congrArg Prod.fst hp
    simpa [k, add_comm] using hx
  rw [hx, h_k (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ht]

theorem paper_normalizer_left_paired (p : Markov.paperPuncturedSquare) (t : ℝ)
    (ht : t ∈ Set.Icc (-1) 1)
    (hp : p.val = (-1, (5*t+3)/(3*t+5))) :
    (paperPuncturedSquareHomeomorph p).val = (-1, t) := by
  rw [paper_normalizer_left p (congrArg Prod.fst hp)]
  have hy : p.val.2 = k 1 t := by
    have hy := congrArg Prod.snd hp
    simpa [k, add_comm] using hy
  rw [hy, h_k (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ht]

end SquareSideNormalizer

