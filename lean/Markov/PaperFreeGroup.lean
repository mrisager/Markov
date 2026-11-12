import Markov.PaperModularCommutators
import Mathlib.GroupTheory.CoprodI
import Mathlib.Tactic

/-! Ping-pong for the original paper matrices, giving an actual free group
basis of their generated subgroup. No surface or homology claim is made. -/
noncomputable section
open scoped MatrixGroups Pointwise Function
open Set
namespace Markov

def paperFreeGenerators : Fin 2 → SL(2, ℤ) := ![paperGeneratorASL, paperGeneratorBSL]

def paperPingPongX : Fin 2 → Set UpperHalfPlane :=
  ![{z | z.re ^ 2 + z.re + z.im ^ 2 ≤ 0},
    {z | z.re ^ 2 - z.re + z.im ^ 2 ≤ 0}]

def paperPingPongY : Fin 2 → Set UpperHalfPlane :=
  ![{z | 1 < z.re}, {z | z.re < -1}]

private theorem paperA_moebius (z : UpperHalfPlane) :
    ((paperGeneratorASL • z : UpperHalfPlane) : ℂ) = ((z : ℂ) - 1) / (2 - (z : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [paperGeneratorASL, paperGeneratorA, sub_eq_add_neg, add_comm]

private theorem paperB_moebius (z : UpperHalfPlane) :
    ((paperGeneratorBSL • z : UpperHalfPlane) : ℂ) = ((z : ℂ) + 1) / ((z : ℂ) + 2) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [paperGeneratorBSL, paperGeneratorB]

private theorem paperA_circle_identity (z : UpperHalfPlane) :
    (paperGeneratorASL • z).re ^ 2 + (paperGeneratorASL • z).re +
        (paperGeneratorASL • z).im ^ 2 =
      (z.re - 1) / ((2 - z.re) ^ 2 + z.im ^ 2) := by
  have hD : (2 - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (2 - z.re)]
  have hr := congrArg Complex.re (paperA_moebius z)
  have hi := congrArg Complex.im (paperA_moebius z)
  norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply] at hr hi
  change (paperGeneratorASL • z).re = _ at hr
  change (paperGeneratorASL • z).im = _ at hi
  rw [hr, hi]
  field_simp [hD, ← pow_two]
  ring

private theorem paperB_circle_identity (z : UpperHalfPlane) :
    (paperGeneratorBSL • z).re ^ 2 - (paperGeneratorBSL • z).re +
        (paperGeneratorBSL • z).im ^ 2 =
      -(z.re + 1) / ((z.re + 2) ^ 2 + z.im ^ 2) := by
  have hD : (z.re + 2) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (z.re + 2)]
  have hr := congrArg Complex.re (paperB_moebius z)
  have hi := congrArg Complex.im (paperB_moebius z)
  norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply] at hr hi
  change (paperGeneratorBSL • z).re = _ at hr
  change (paperGeneratorBSL • z).im = _ at hi
  rw [hr, hi]
  field_simp [hD, ← pow_two]
  ring

private theorem paperPingPongX_nonempty (i : Fin 2) : (paperPingPongX i).Nonempty := by
  fin_cases i
  · refine ⟨UpperHalfPlane.mk ⟨-1 / 2, 1 / 4⟩ (by norm_num), ?_⟩
    norm_num [paperPingPongX]
  · refine ⟨UpperHalfPlane.mk ⟨1 / 2, 1 / 4⟩ (by norm_num), ?_⟩
    norm_num [paperPingPongX]

private theorem paperPingPongX_disjoint : Pairwise (Disjoint on paperPingPongX) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hy := sq_pos_of_pos z.im_pos
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change z.re ^ 2 + z.re + z.im ^ 2 ≤ 0 at hz
    change z.re ^ 2 - z.re + z.im ^ 2 ≤ 0 at hz'
    nlinarith [sq_nonneg z.re]
  · change z.re ^ 2 - z.re + z.im ^ 2 ≤ 0 at hz
    change z.re ^ 2 + z.re + z.im ^ 2 ≤ 0 at hz'
    nlinarith [sq_nonneg z.re]
  · exact (hij rfl).elim

private theorem paperPingPongY_disjoint : Pairwise (Disjoint on paperPingPongY) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hz hz'
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change 1 < z.re at hz
    change z.re < -1 at hz'
    linarith
  · change z.re < -1 at hz
    change 1 < z.re at hz'
    linarith
  · exact (hij rfl).elim

private theorem paperPingPongX_bounds (i : Fin 2) (z : UpperHalfPlane)
    (hz : z ∈ paperPingPongX i) : -1 < z.re ∧ z.re < 1 := by
  have hy := sq_pos_of_pos z.im_pos
  fin_cases i
  · change z.re ^ 2 + z.re + z.im ^ 2 ≤ 0 at hz
    constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.re + 1)]
  · change z.re ^ 2 - z.re + z.im ^ 2 ≤ 0 at hz
    constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.re - 1)]

private theorem paperPingPongXY_disjoint (i j : Fin 2) :
    Disjoint (paperPingPongX i) (paperPingPongY j) := by
  apply Set.disjoint_left.mpr
  intro z hz hy
  have hb := paperPingPongX_bounds i z hz
  fin_cases j
  · change 1 < z.re at hy
    linarith
  · change z.re < -1 at hy
    linarith

private theorem paperPingPong_forward (i : Fin 2) :
    paperFreeGenerators i • (paperPingPongY i)ᶜ ⊆ paperPingPongX i := by
  rintro z ⟨w, hw, rfl⟩
  fin_cases i
  · change ¬ 1 < w.re at hw
    change (paperGeneratorASL • w).re ^ 2 + (paperGeneratorASL • w).re +
      (paperGeneratorASL • w).im ^ 2 ≤ 0
    rw [paperA_circle_identity]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · change ¬ w.re < -1 at hw
    change (paperGeneratorBSL • w).re ^ 2 - (paperGeneratorBSL • w).re +
      (paperGeneratorBSL • w).im ^ 2 ≤ 0
    rw [paperB_circle_identity]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

private theorem paperPingPong_backward (i : Fin 2) :
    (paperFreeGenerators i)⁻¹ • (paperPingPongX i)ᶜ ⊆ paperPingPongY i := by
  rintro z ⟨w, hw, rfl⟩
  by_contra hz
  have h := paperPingPong_forward i ⟨(paperFreeGenerators i)⁻¹ • w, hz, rfl⟩
  simp only [smul_inv_smul] at h
  exact hw h

/-- The actual two paper matrices satisfy the ping-pong criterion. -/
theorem paperFreeGenerators_lift_injective :
    Function.Injective (FreeGroup.lift paperFreeGenerators) := by
  exact FreeGroup.injective_lift_of_ping_pong paperFreeGenerators
    paperPingPongX paperPingPongY paperPingPongX_nonempty paperPingPongX_disjoint
    paperPingPongY_disjoint paperPingPongXY_disjoint paperPingPong_forward paperPingPong_backward

theorem paperFreeGenerators_range :
    Set.range paperFreeGenerators = {paperGeneratorASL, paperGeneratorBSL} := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [paperFreeGenerators]
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem paperFreeGenerators_lift_range :
    (FreeGroup.lift paperFreeGenerators).range = modularTraceSubgroup := by
  rw [FreeGroup.range_lift_eq_closure, paperFreeGenerators_range]
  exact paperTraceSubgroup_eq_modularTraceSubgroup

/-- The actual marked free-group map, restricted to the proved trace subgroup. -/
def paperFreeGroupLift : FreeGroup (Fin 2) →* modularTraceSubgroup :=
  (FreeGroup.lift paperFreeGenerators).codRestrict modularTraceSubgroup (by
    intro w
    rw [← paperFreeGenerators_lift_range]
    exact ⟨w, rfl⟩)

theorem paperFreeGroupLift_injective : Function.Injective paperFreeGroupLift := by
  intro x y hxy
  apply paperFreeGenerators_lift_injective
  exact congrArg Subtype.val hxy

theorem paperFreeGroupLift_surjective : Function.Surjective paperFreeGroupLift := by
  intro g
  have hg : g.val ∈ (FreeGroup.lift paperFreeGenerators).range := by
    rw [paperFreeGenerators_lift_range]
    exact g.property
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw

/-- The paper's two original matrices freely generate the actual trace subgroup. -/
def paperTraceFreeGroupEquiv : FreeGroup (Fin 2) ≃* modularTraceSubgroup :=
  MulEquiv.ofBijective paperFreeGroupLift
    ⟨paperFreeGroupLift_injective, paperFreeGroupLift_surjective⟩

/-- A genuine two-element free-group basis, with the original paper marking. -/
def paperTraceFreeGroupBasis : FreeGroupBasis (Fin 2) modularTraceSubgroup :=
  ⟨paperTraceFreeGroupEquiv.symm⟩

@[simp] theorem paperTraceFreeGroupBasis_zero :
    (paperTraceFreeGroupBasis 0 : SL(2, ℤ)) = paperGeneratorASL := by
  change (paperFreeGroupLift (FreeGroup.of 0) : SL(2, ℤ)) = paperGeneratorASL
  exact FreeGroup.lift_apply_of

@[simp] theorem paperTraceFreeGroupBasis_one :
    (paperTraceFreeGroupBasis 1 : SL(2, ℤ)) = paperGeneratorBSL := by
  change (paperFreeGroupLift (FreeGroup.of 1) : SL(2, ℤ)) = paperGeneratorBSL
  exact FreeGroup.lift_apply_of

instance modularTraceSubgroup_isFreeGroup : IsFreeGroup modularTraceSubgroup :=
  paperTraceFreeGroupBasis.isFreeGroup

end Markov
