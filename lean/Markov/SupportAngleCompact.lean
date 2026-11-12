import Markov.NormalHalfPlane
import Markov.SupportAngleEnvelope

/-! Compactness and attained extrema of the actual support-angle set over
the closed canonical trace radial section. The continuous angle branch is
supplied by the proved common half-plane. No angular interval or normal-set
connectedness is assumed. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The parameter and all its norming supports, jointly over the closed
unit parameter interval. -/
def basisSupportGraph (B : Module.Basis (Fin 2) ℝ E) : Set (ℝ × StrongDual ℝ E) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    p.2 ∈ normingFunctionals (B 0 + p.1 • B 1)}

theorem basisSupportGraph_isClosed (B : Module.Basis (Fin 2) ℝ E) :
    IsClosed (basisSupportGraph B) := by
  have hpoint : Continuous (fun p : ℝ × StrongDual ℝ E => B 0 + p.1 • B 1) :=
    continuous_const.add (continuous_fst.smul continuous_const)
  have heval : Continuous (fun p : ℝ × StrongDual ℝ E => p.2 (B 0 + p.1 • B 1)) :=
    continuous_snd.clm_apply hpoint
  exact (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_le continuous_snd.norm continuous_const).inter
      (isClosed_eq heval hpoint.norm))

theorem basisSupportGraph_isCompact (B : Module.Basis (Fin 2) ℝ E) :
    IsCompact (basisSupportGraph B) := by
  letI : FiniteDimensional ℝ E := Module.Finite.of_basis B
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : StrongDual ℝ E) 1)).of_isClosed_subset
    (basisSupportGraph_isClosed B)
  intro p hp
  exact ⟨hp.1, by simpa using hp.2.1⟩

/-- The graph image describes angles of the actual unit-sphere section,
because radial normalization preserves every norming support. -/
theorem supportAnglesOn_closedRadial_eq_graph_image
    (B C : Module.Basis (Fin 2) ℝ E) :
    supportAnglesOn C (radialBasisSection B '' Set.Icc (0 : ℝ) 1) =
      (fun p : ℝ × StrongDual ℝ E => supportAngle C p.2) '' basisSupportGraph B := by
  ext θ
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
    refine ⟨(t, f), ⟨ht, ?_⟩, rfl⟩
    rwa [radialBasisSection,
      normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero B t)] at hf
  · rintro ⟨⟨t, f⟩, ⟨ht, hf⟩, rfl⟩
    refine ⟨radialBasisSection B t, ⟨t, ht, rfl⟩, f, ?_, rfl⟩
    rwa [radialBasisSection,
      normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero B t)]

theorem supportAnglesOn_closedRadial_nonempty
    (B C : Module.Basis (Fin 2) ℝ E) :
    (supportAnglesOn C (radialBasisSection B '' Set.Icc (0 : ℝ) 1)).Nonempty := by
  apply supportAnglesOn_nonempty
  exact ⟨radialBasisSection B 0, 0, by norm_num, rfl⟩

/-- Positivity gives a continuous angle on the compact joint support graph.
The conclusion concerns all actual supporting functionals. -/
theorem supportAnglesOn_closedRadial_isCompact_of_sum_pos
    (B C : Module.Basis (Fin 2) ℝ E)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ f ∈ normingFunctionals (B 0 + t • B 1),
      0 < f (C 0) + f (C 1)) :
    IsCompact (supportAnglesOn C (radialBasisSection B '' Set.Icc (0 : ℝ) 1)) := by
  rw [supportAnglesOn_closedRadial_eq_graph_image]
  apply (basisSupportGraph_isCompact B).image_of_continuousOn
  intro p hp
  exact ((supportAngle_continuousAt_of_sum_pos C p.2
    (hpos p.1 hp.1 p.2 hp.2)).comp continuous_snd.continuousAt).continuousWithinAt

/-- The actual trace quarter-section angle set is compact; the common
half-plane used for continuity has already been proved from the trace norm. -/
theorem trace_closedQuarter_supportAngles_isCompact :
    IsCompact (supportAnglesOn traceBasis
      (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1)) := by
  apply supportAnglesOn_closedRadial_isCompact_of_sum_pos traceBasis traceBasis
  intro t ht f hf
  simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht f hf

theorem trace_closedQuarter_supportAngleLower_mem :
    supportAngleLower traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) ∈
      supportAnglesOn traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) :=
  trace_closedQuarter_supportAngles_isCompact.sInf_mem
    (supportAnglesOn_closedRadial_nonempty traceBasis traceBasis)

theorem trace_closedQuarter_supportAngleUpper_mem :
    supportAngleUpper traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) ∈
      supportAnglesOn traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) :=
  trace_closedQuarter_supportAngles_isCompact.sSup_mem
    (supportAnglesOn_closedRadial_nonempty traceBasis traceBasis)

/-- A real parameter and an actual support attain the lower angle. -/
theorem trace_closedQuarter_supportAngleLower_attained :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ f ∈ normingFunctionals (radialBasisSection traceBasis t),
        supportAngle traceBasis f =
          supportAngleLower traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) := by
  obtain ⟨x, ⟨t, ht, rfl⟩, f, hf, he⟩ := trace_closedQuarter_supportAngleLower_mem
  exact ⟨t, ht, f, hf, he.symm⟩

/-- A real parameter and an actual support attain the upper angle. -/
theorem trace_closedQuarter_supportAngleUpper_attained :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ f ∈ normingFunctionals (radialBasisSection traceBasis t),
        supportAngle traceBasis f =
          supportAngleUpper traceBasis (radialBasisSection traceBasis '' Set.Icc (0 : ℝ) 1) := by
  obtain ⟨x, ⟨t, ht, rfl⟩, f, hf, he⟩ := trace_closedQuarter_supportAngleUpper_mem
  exact ⟨t, ht, f, hf, he.symm⟩

end Markov
