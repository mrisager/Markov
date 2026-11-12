import Markov.DiskArcChordHomotopy

/-! Endpoint distinctness forced by an actual transverse interior chord
intersection. This is concrete two-dimensional affine algebra, with no assumed
boundary order, arc-disjointness or matching structure. -/

noncomputable section
namespace Markov

private theorem chord_first_parameter_unique (f g : unitInterval → ℂ)
    (hd : (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re ≠ 0)
    (u v s t : unitInterval)
    (h : diskArcChord f u = diskArcChord g v)
    (h' : diskArcChord f s = diskArcChord g t) : (u:ℝ) = (s:ℝ) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  have hsr := congrArg Complex.re h'
  have hsi := congrArg Complex.im h'
  simp [diskArcChord] at hr hi hsr hsi
  have hdet : ((u:ℝ)-(s:ℝ))*((f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re) = 0 := by
    simp only [Complex.sub_re, Complex.sub_im]
    linear_combination (g 1).im*hr - (g 0).im*hr - (g 1).im*hsr + (g 0).im*hsr -
      (g 1).re*hi + (g 0).re*hi + (g 1).re*hsi - (g 0).re*hsi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_right hd)

/-- An actual transverse intersection strictly inside two endpoint chords
forces all cross-path endpoint values to be different. No disk/norm or arc
hypotheses are needed for this affine-algebra fact. -/
theorem diskArcChord_cross_endpoints_ne_of_transverse_interior_intersection
    (f g : unitInterval → ℂ)
    (hd : (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re ≠ 0)
    (u v : unitInterval) (hu0 : 0 < (u:ℝ)) (hu1 : (u:ℝ) < 1)
    (h : diskArcChord f u = diskArcChord g v) :
    ∀ s t : unitInterval, (s=0 ∨ s=1) → (t=0 ∨ t=1) → f s ≠ g t := by
  intro s t hs ht heq
  have hfs : diskArcChord f s = f s := by rcases hs with rfl | rfl <;> simp [diskArcChord]
  have hgt : diskArcChord g t = g t := by rcases ht with rfl | rfl <;> simp [diskArcChord]
  have hus := chord_first_parameter_unique f g hd u v s t h (hfs.trans (heq.trans hgt.symm))
  rcases hs with rfl | rfl
  · exact (ne_of_gt hu0) (by simpa only [show ((0:unitInterval):ℝ)=0 from rfl] using hus)
  · exact (ne_of_lt hu1) (by simpa only [show ((1:unitInterval):ℝ)=1 from rfl] using hus)

end Markov
