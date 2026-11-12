import Markov.Statements

/-! Transfer of primitive lattice estimates to Markov triple counts.
The statements take the required counting and error estimates as hypotheses. -/

open Filter Asymptotics

namespace Markov

/-- An explicit admissible choice in Theorem 13's last paragraph. -/
noncomputable def cutoffExponent (δ : ℝ) : ℝ := δ / (2 * (1 + δ))

theorem cutoffExponent_spec (δ : ℝ) (hδ : 0 < δ) :
    0 < cutoffExponent δ ∧ cutoffExponent δ < δ / (1 + δ) ∧
      1 - δ + cutoffExponent δ * (1 + δ) = 1 - δ / 2 := by
  have hp : 0 < 1 + δ := by linarith
  have heq : cutoffExponent δ = (δ / (1 + δ)) / 2 := by
    unfold cutoffExponent
    rw [div_div, mul_comm (1 + δ) 2]
  rw [heq]
  have hd : 0 < δ / (1 + δ) := div_pos hδ hp
  refine ⟨by positivity, by linarith, ?_⟩
  field_simp [hp.ne']
  ring

/-- The unconditional error scale in Theorem 1 is sublogarithmic. -/
theorem unconditionalScale_isLittleO_log : unconditionalScale =o[atTop] Real.log := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop
    (s := (3 : ℝ) / 10) ((1 : ℝ) / 10) (by norm_num)).tendsto_div_nhds_zero
  have hc := hsmall.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply isLittleO_of_tendsto
    (fun x hx => by simp [unconditionalScale, hx])
  apply hc.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx
  dsimp [unconditionalScale, Function.comp_def]
  field_simp [hx.ne']

theorem UnconditionalBound.sublogarithmic {C : ℝ} (h : UnconditionalBound C) :
    SublogarithmicBound C :=
  h.trans_isLittleO unconditionalScale_isLittleO_log

/-- Algebra at the end of the paper, including the exceptional-orbit `+1`. -/
theorem orbit_error_identity (M P A L ell : ℝ) (h : M = P / 12 + 1) :
    M - (A / 3) * ell ^ 2 =
      (P - A * L ^ 2) / 12 + (A / 12) * (L ^ 2 - (2 * ell) ^ 2) + 1 := by
  rw [h]
  ring

/-- Transfer the primitive-count error through the orbit identity and length change.
All three substantive inputs are visible as hypotheses. -/
theorem transfer_error_bound
    (M P L ell E : ℝ → ℝ) (A : ℝ)
    (horbit : ∀ᶠ x in atTop, M x = P (L x) / 12 + 1)
    (hprimitive : (fun x => P (L x) - A * L x ^ 2) =O[atTop] E)
    (hlength : (fun x => L x ^ 2 - (2 * ell x) ^ 2) =O[atTop] E)
    (hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] E) :
    (fun x => M x - (A / 3) * ell x ^ 2) =O[atTop] E := by
  have h := ((hprimitive.const_mul_left (1 / 12 : ℝ)).add
    (hlength.const_mul_left (A / 12))).add hone
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [horbit] with x hx
  have hi := orbit_error_identity (M x) (P (L x)) A (L x) (ell x) hx
  linarith [hi]

/-- The change of variables from the primitive lattice estimate
to the Markov count, using mathlib's asymptotic composition rule. -/
theorem compose_primitive_error (P L E : ℝ → ℝ) (A : ℝ)
    (hP : (fun R => P R - A * R ^ 2) =O[atTop] E)
    (hL : Tendsto L atTop atTop) :
    (fun x => P (L x) - A * L x ^ 2) =O[atTop] (fun x => E (L x)) :=
  hP.comp_tendsto hL

end Markov
