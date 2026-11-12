import Markov.SupportAngleCompact
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

/-! Connectedness of the actual support graph and its continuous angle image.
For the canonical closed trace quarter-section this identifies all support
angles with their attained closed interval, and all normalized normals with
the corresponding circle arc. These are local statements about this section. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The supports at a fixed vector form a convex set, including when the
support at that vector is not unique. -/
theorem normingFunctionals_convex (x : E) : Convex ℝ (normingFunctionals x) := by
  intro f hf g hg a b ha hb hab
  constructor
  · calc
      ‖a • f + b • g‖ ≤ ‖a • f‖ + ‖b • g‖ := norm_add_le _ _
      _ = a * ‖f‖ + b * ‖g‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hf.1 ha)
          (mul_le_mul_of_nonneg_left hg.1 hb)
      _ = 1 := by simpa only [mul_one] using hab
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hf.2, hg.2, ← add_mul, hab, one_mul]

theorem normingFunctionals_isConnected (x : E) : IsConnected (normingFunctionals x) :=
  (normingFunctionals_convex x).isConnected (normingFunctionals_nonempty x)

/-- The compact graph of all supports over the interval is connected. Its
projection has nonempty convex fibres; no choice of a continuous support is
needed. -/
theorem basisSupportGraph_isConnected (B : Module.Basis (Fin 2) ℝ E) :
    IsConnected (basisSupportGraph B) := by
  let π : basisSupportGraph B → Set.Icc (0 : ℝ) 1 :=
    fun p => ⟨p.1.1, p.2.1⟩
  have hπ : Continuous π :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective π := by
    intro t
    obtain ⟨f, hf⟩ := normingFunctionals_nonempty (B 0 + t.1 • B 1)
    exact ⟨⟨(t.1, f), t.2, hf⟩, rfl⟩
  have hfibres : ∀ t, IsConnected (π ⁻¹' {t}) := by
    intro t
    letI : ConnectedSpace (normingFunctionals (B 0 + t.1 • B 1)) :=
      isConnected_iff_connectedSpace.mp (normingFunctionals_isConnected _)
    let j : normingFunctionals (B 0 + t.1 • B 1) → basisSupportGraph B :=
      fun f => ⟨(t.1, f.1), t.2, f.2⟩
    have hj : Continuous j :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have heq : Set.range j = π ⁻¹' {t} := by
      ext p
      constructor
      · rintro ⟨f, rfl⟩
        rfl
      · intro hp
        have ht : p.1.1 = t.1 := congrArg Subtype.val hp
        refine ⟨⟨p.1.2, ?_⟩, ?_⟩
        · simpa only [← ht] using p.2.2
        · apply Subtype.ext
          exact Prod.ext ht.symm rfl
    rw [← heq]
    exact isConnected_range hj
  letI : CompactSpace (basisSupportGraph B) :=
    isCompact_iff_compactSpace.mp (basisSupportGraph_isCompact B)
  letI : ConnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
  have hquot := hπ.isClosedMap.isQuotientMap hπ hsurj
  have hconn := preimage_connectedComponent_connected hfibres
    (fun _ => hquot.isClosed_preimage.symm) (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1)
  have huniv : IsConnected (Set.univ : Set (basisSupportGraph B)) := by
    simpa only [PreconnectedSpace.connectedComponent_eq_univ, Set.preimage_univ] using hconn
  exact isConnected_iff_connectedSpace.mpr (connectedSpace_iff_univ.mpr huniv)

/-- A common positive half-plane makes the angles of every actual support
a connected set. -/
theorem supportAnglesOn_closedRadial_isConnected_of_sum_pos
    (B C : Module.Basis (Fin 2) ℝ E)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ f ∈ normingFunctionals (B 0 + t • B 1),
      0 < f (C 0) + f (C 1)) :
    IsConnected (supportAnglesOn C (radialBasisSection B '' Set.Icc (0 : ℝ) 1)) := by
  rw [supportAnglesOn_closedRadial_eq_graph_image]
  apply (basisSupportGraph_isConnected B).image
  intro p hp
  exact ((supportAngle_continuousAt_of_sum_pos C p.2
    (hpos p.1 hp.1 p.2 hp.2)).comp continuous_snd.continuousAt).continuousWithinAt

theorem supportAnglesOn_closedRadial_eq_Icc_of_sum_pos
    (B C : Module.Basis (Fin 2) ℝ E)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ f ∈ normingFunctionals (B 0 + t • B 1),
      0 < f (C 0) + f (C 1)) :
    supportAnglesOn C (radialBasisSection B '' Set.Icc (0 : ℝ) 1) =
      Set.Icc (supportAngleLower C (radialBasisSection B '' Set.Icc (0 : ℝ) 1))
        (supportAngleUpper C (radialBasisSection B '' Set.Icc (0 : ℝ) 1)) :=
  eq_Icc_of_connected_compact
    (supportAnglesOn_closedRadial_isConnected_of_sum_pos B C hpos)
    (supportAnglesOn_closedRadial_isCompact_of_sum_pos B C hpos)

theorem trace_closedQuarter_supportAngles_isConnected :
    IsConnected (supportAnglesOn traceBasis
      (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1)) := by
  apply supportAnglesOn_closedRadial_isConnected_of_sum_pos traceBasis traceBasis
  intro t ht f hf
  simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht f hf

/-- Every intermediate angle between the actual attained extrema occurs
as an angle of an actual support on the closed trace quarter-section. -/
theorem trace_closedQuarter_supportAngles_eq_Icc :
    supportAnglesOn traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) =
      Set.Icc
        (supportAngleLower traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1))
        (supportAngleUpper traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1)) :=
  eq_Icc_of_connected_compact trace_closedQuarter_supportAngles_isConnected
    trace_closedQuarter_supportAngles_isCompact

/-- The genuine normalized normal set is exactly the circle arc between
its actual support-angle extrema, with both endpoint normal sets included. -/
theorem trace_closedQuarter_normals_eq_supportAngle_arc :
    normalsOn traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) =
      circleNormal '' Set.Icc
        (supportAngleLower traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1))
        (supportAngleUpper traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1)) := by
  rw [← trace_closedQuarter_supportAngles_eq_Icc]
  ext n
  constructor
  · rintro ⟨x, hx, f, hf, rfl⟩
    have hxne : x ≠ 0 := by
      obtain ⟨t, ht, rfl⟩ := hx
      exact norm_ne_zero_iff.mp (by rw [norm_radialBasisSection]; norm_num)
    exact ⟨supportAngle traceBasis f, ⟨x, hx, f, hf, rfl⟩,
      circleNormal_supportAngle traceBasis f (normingFunctional_ne_zero x hxne f hf)⟩
  · rintro ⟨θ, ⟨x, hx, f, hf, rfl⟩, rfl⟩
    have hxne : x ≠ 0 := by
      obtain ⟨t, ht, rfl⟩ := hx
      exact norm_ne_zero_iff.mp (by rw [norm_radialBasisSection]; norm_num)
    exact ⟨x, hx, f, hf,
      circleNormal_supportAngle traceBasis f (normingFunctional_ne_zero x hxne f hf)⟩

end Markov
