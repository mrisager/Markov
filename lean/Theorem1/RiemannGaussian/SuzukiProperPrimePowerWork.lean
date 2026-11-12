/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import T1ChebyshevPrimePowers

namespace RiemannGaussian

/-- The pinned proof of the same Chebyshev bound; no Suzuki machinery is needed here. -/
theorem chebyshevPsi_sub_theta_le_eighteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 18 * Real.sqrt x :=
  Markov.t1_chebyshev_prime_power_tail hx

end RiemannGaussian

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
