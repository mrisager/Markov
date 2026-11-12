import Markov.StandardTorusSquare
import Markov.NormalizedCircleWindingConjugation

noncomputable section
open Set Topology
namespace Markov

theorem normalizedCircleStandardLoop_surjective :
    Function.Surjective normalizedCircleStandardLoop := by
  intro u
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico u
  exact ⟨⟨t, ht.1, ht.2.le⟩, (normalizedCircleStandardLoop_apply _).trans he⟩

/-- The actual closed-interval circle quotient identifies just its two ends. -/
theorem normalizedCircleStandardLoop_eq_iff (t u : unitInterval) :
    normalizedCircleStandardLoop t = normalizedCircleStandardLoop u ↔
      t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
  have hproj (v : unitInterval) : normalizedCircleStandardLoop v =
      standardCircleSquareScalar (2*(v : ℝ)-1) := by
    rw [normalizedCircleStandardLoop_apply, standardCircleSquareScalar]
    congr 1
    ring
  have ht : 2*(t : ℝ)-1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  have hu : 2*(u : ℝ)-1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [u.property.1, u.property.2]
  rw [hproj t, hproj u, standardCircleSquareScalar_eq_iff ht hu]
  constructor
  · rintro (he | ⟨ht0, hu1⟩ | ⟨ht1, hu0⟩)
    · left
      apply Subtype.ext
      linarith
    · right; left
      exact ⟨Subtype.ext (by change (t : ℝ) = 0; linarith),
        Subtype.ext (by change (u : ℝ) = 1; linarith)⟩
    · right; right
      exact ⟨Subtype.ext (by change (t : ℝ) = 1; linarith),
        Subtype.ext (by change (u : ℝ) = 0; linarith)⟩
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Descend actual continuous interval homotopy data whose two parameter
edges agree, through the actual compact interval-to-circle quotient. -/
def normalizedCircleHomotopyOfIntervalData {X : Type*} [TopologicalSpace X]
    (f g : C(NormalizedCircle, X)) (H : C(unitInterval × unitInterval, X))
    (h0 : ∀ t, H (0, t) = f (normalizedCircleStandardLoop t))
    (h1 : ∀ t, H (1, t) = g (normalizedCircleStandardLoop t))
    (hend : ∀ s, H (s, 0) = H (s, 1)) : f.Homotopy g := by
  let q : C(unitInterval × unitInterval, unitInterval × NormalizedCircle) :=
    ⟨fun st => (st.1, normalizedCircleStandardLoop st.2), by fun_prop⟩
  have hq : IsQuotientMap q := by
    apply IsQuotientMap.of_surjective_continuous _ q.continuous
    rintro ⟨s, u⟩
    obtain ⟨t, ht⟩ := normalizedCircleStandardLoop_surjective u
    exact ⟨(s, t), Prod.ext rfl ht⟩
  have hfibre : Function.FactorsThrough H q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ he
    have hs : s = s' := congrArg Prod.fst he
    have ht : normalizedCircleStandardLoop t = normalizedCircleStandardLoop t' :=
      congrArg Prod.snd he
    subst s'
    rcases (normalizedCircleStandardLoop_eq_iff t t').mp ht with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hend s
    · exact (hend s).symm
  let K := hq.lift H hfibre
  have hK (s t : unitInterval) : K (s, normalizedCircleStandardLoop t) = H (s, t) := by
    exact congrArg (fun J : C(unitInterval × unitInterval, X) => J (s, t))
      (hq.lift_comp H hfibre)
  exact {
    toContinuousMap := K
    map_zero_left := fun u => by
      obtain ⟨t, rfl⟩ := normalizedCircleStandardLoop_surjective u
      exact (hK 0 t).trans (h0 t)
    map_one_left := fun u => by
      obtain ⟨t, rfl⟩ := normalizedCircleStandardLoop_surjective u
      exact (hK 1 t).trans (h1 t) }

/-- The genuine covering winding of the actual circle-map loop, translated
by its own actual value at zero. -/
def normalizedCircleMapWinding (f : C(NormalizedCircle, NormalizedCircle)) : ℤ :=
  normalizedCircleWinding
    (normalizedCircleTranslatedLoop (normalizedCircleStandardLoop.map f.continuous))

/-- Equal genuine circle windings give an actual free circle-map homotopy.
The actual basepoint path is included before interval-to-circle descent. -/
theorem normalizedCircleMap_homotopic_of_winding_eq
    (f g : C(NormalizedCircle, NormalizedCircle))
    (hw : normalizedCircleMapWinding f = normalizedCircleMapWinding g) : f.Homotopic g := by
  obtain ⟨H⟩ := (normalizedCircleWinding_homotopic_iff _ _).mp hw
  let a : Path (f 0) (g 0) := PathConnectedSpace.somePath (f 0) (g 0)
  let K : C(unitInterval × unitInterval, NormalizedCircle) :=
    ⟨fun st => a st.1 + H st, by fun_prop⟩
  apply Nonempty.intro
  apply normalizedCircleHomotopyOfIntervalData f g K
  · intro t
    change a 0 + H (0, t) = f (normalizedCircleStandardLoop t)
    have h0 : H (0, t) =
        normalizedCircleTranslatedLoop (normalizedCircleStandardLoop.map f.continuous) t :=
      H.map_zero_left t
    rw [a.source, h0]
    change f 0 + (f (normalizedCircleStandardLoop t)-f 0) = _
    abel
  · intro t
    change a 1 + H (1, t) = g (normalizedCircleStandardLoop t)
    have h1 : H (1, t) =
        normalizedCircleTranslatedLoop (normalizedCircleStandardLoop.map g.continuous) t :=
      H.map_one_left t
    rw [a.target, h1]
    change g 0 + (g (normalizedCircleStandardLoop t)-g 0) = _
    abel
  · intro s
    change a s + H (s, 0) = a s + H (s, 1)
    rw [H.source, H.target]

/-- The two genuine coordinate windings for a map into the filled torus. -/
def standardTorusCircleMapWinding (f : C(NormalizedCircle, StandardTorus)) : ℤ × ℤ :=
  (normalizedCircleMapWinding ⟨fun u => (f u).1, continuous_fst.comp f.continuous⟩,
    normalizedCircleMapWinding ⟨fun u => (f u).2, continuous_snd.comp f.continuous⟩)

/-- Equal two-coordinate winding gives a genuine circle-map homotopy in
the FILLED actual two-circle torus. No puncture avoidance is asserted. -/
theorem standardTorusCircleMap_homotopic_of_winding_eq
    (f g : C(NormalizedCircle, StandardTorus))
    (hw : standardTorusCircleMapWinding f = standardTorusCircleMapWinding g) :
    f.Homotopic g := by
  let f₁ : C(NormalizedCircle, NormalizedCircle) :=
    ⟨fun u => (f u).1, continuous_fst.comp f.continuous⟩
  let f₂ : C(NormalizedCircle, NormalizedCircle) :=
    ⟨fun u => (f u).2, continuous_snd.comp f.continuous⟩
  let g₁ : C(NormalizedCircle, NormalizedCircle) :=
    ⟨fun u => (g u).1, continuous_fst.comp g.continuous⟩
  let g₂ : C(NormalizedCircle, NormalizedCircle) :=
    ⟨fun u => (g u).2, continuous_snd.comp g.continuous⟩
  have h₁ : f₁.Homotopic g₁ := normalizedCircleMap_homotopic_of_winding_eq f₁ g₁
    (congrArg Prod.fst hw)
  have h₂ : f₂.Homotopic g₂ := normalizedCircleMap_homotopic_of_winding_eq f₂ g₂
    (congrArg Prod.snd hw)
  have hh := h₁.prodMk h₂
  have hf : f₁.prodMk f₂ = f := by ext u <;> rfl
  have hg : g₁.prodMk g₂ = g := by ext u <;> rfl
  rwa [hf, hg] at hh

end Markov
