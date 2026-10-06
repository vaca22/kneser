import Kneser.ParabolicCoordinateJacobian
import Kneser.ParabolicOverlapGate

/-!
The genuine principal inverse has a nonzero finite-orbit spatial Jacobian
on the actual high imaginary gate.  Pullback of the canonical repelling
coordinate therefore has a local analytic inverse there.
-/

noncomputable section

namespace Kneser.FiniteGateJacobian

open Filter Set Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ParabolicCoordinateJacobian
open scoped Topology

def inverseOrbitSpatialJacobian (v : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => inverseOrbitSpatialJacobian v k / (1 - inverseOrbit v 0 k)

theorem inverse_gate_norm_lt_one (v : ℂ) (N : ℕ)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|)
    (k : ℕ) (hk : k ≤ N) : ‖inverseOrbit v 0 k‖ < 1 := by
  have hn := ParabolicOverlapGate.finite_orbit_gate_norm parabolicInverse
    Kneser.RepellingExponentialOrbit.inverse_step_error_bound v N hg k hk
  rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
  linarith

theorem hasDerivAt_inverseOrbit_spatial_of_gate (v : ℂ) (N : ℕ)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|) :
    ∀ k : ℕ, k ≤ N → HasDerivAt (fun w => inverseOrbit w 0 k)
      (inverseOrbitSpatialJacobian v k) v := by
  intro k
  induction k with
  | zero => intro _; exact hasDerivAt_id v
  | succ k ih =>
    intro hk
    have hp := ih (by omega)
    have hd := (hasDerivAt_parabolicInverse (inverseOrbit v 0 k)
      (inverse_gate_norm_lt_one v N hg k (by omega))).comp v hp
    change HasDerivAt (fun w => parabolicInverse (inverseOrbit w 0 k))
      (1 / (1 - inverseOrbit v 0 k) * inverseOrbitSpatialJacobian v k) v at hd
    convert hd using 1
    · funext w
      rw [inverseOrbit_succ, reflectedInverse_zero]
    · dsimp [inverseOrbitSpatialJacobian]
      ring

theorem inverseOrbitSpatialJacobian_ne_zero_of_gate (v : ℂ) (N : ℕ)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|) :
    ∀ k : ℕ, k ≤ N → inverseOrbitSpatialJacobian v k ≠ 0 := by
  intro k
  induction k with
  | zero => intro _; exact one_ne_zero
  | succ k ih =>
    intro hk
    have hn := inverse_gate_norm_lt_one v N hg k (by omega)
    have hden : 1 - inverseOrbit v 0 k ≠ 0 := by
      intro he
      have hval := sub_eq_zero.mp he
      rw [← hval] at hn
      norm_num at hn
    exact div_ne_zero (ih (by omega)) hden

theorem analyticAt_inverseOrbit_spatial_of_gate (v : ℂ) (N : ℕ)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|)
    (k : ℕ) (hk : k ≤ N) : AnalyticAt ℂ (fun w => inverseOrbit w 0 k) v := by
  exact (ParabolicOverlapGate.analyticAt_inverse_orbit_joint_of_gate v N hg k hk).comp
    (analyticAt_const.prod analyticAt_id)

def transportedRepellingCoordinate (N : ℕ) (u : ℂ) : ℂ :=
  -repellingCoordinate (inverseOrbit (-u) 0 N) + (N : ℂ)

/-- A true canonical coordinate with nonzero derivative at the entered
petal pulls back through the actual inverse orbit, with its derivative
given by the genuine finite-orbit Jacobian. -/
theorem transported_repelling_hasDerivAt (u : ℂ) (N : ℕ) (R : ℝ)
    (hc : CanonicalJacobian repellingCoordinate R)
    (hre : (inverseCoordinate u).re ≤ 1)
    (hN : R + 2 ≤ 3 * (N : ℝ) / 4)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|) :
    AnalyticAt ℂ (transportedRepellingCoordinate N) u ∧
      HasDerivAt (transportedRepellingCoordinate N)
        (deriv repellingCoordinate (inverseOrbit (-u) 0 N) *
          inverseOrbitSpatialJacobian (-u) N) u ∧
      deriv (transportedRepellingCoordinate N) u ≠ 0 := by
  have hneg : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  have hgn : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-u)).im| := by
    simpa [hneg] using hg
  have hentry := ParabolicOverlapGate.repelling_entry u N (R + 1) hre (by linarith) hg
  have hpetal : inverseOrbit (-u) 0 N ∈ ParabolicFatouHolomorphic.petal R := by
    rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
    change R < _
    linarith
  obtain ⟨ha, hdn, _⟩ := hc.2 _ hpetal
  have hia := analyticAt_inverseOrbit_spatial_of_gate (-u) N hgn N le_rfl
  have hit := hasDerivAt_inverseOrbit_spatial_of_gate (-u) N hgn N le_rfl
  have hjn := inverseOrbitSpatialJacobian_ne_zero_of_gate (-u) N hgn N le_rfl
  have hnegd := hit.comp u (hasDerivAt_id u).neg
  have hd := ((ha.hasStrictDerivAt.hasDerivAt.comp u hnegd).neg).add_const (N : ℂ)
  change HasDerivAt (transportedRepellingCoordinate N)
    (-(deriv repellingCoordinate (inverseOrbit (-u) 0 N) *
      (inverseOrbitSpatialJacobian (-u) N * -1))) u at hd
  have hformula : HasDerivAt (transportedRepellingCoordinate N)
      (deriv repellingCoordinate (inverseOrbit (-u) 0 N) *
        inverseOrbitSpatialJacobian (-u) N) u := by
    convert hd using 1
    ring
  have hian : AnalyticAt ℂ (fun w => inverseOrbit (-w) 0 N) u := hia.comp analyticAt_id.neg
  have hac : AnalyticAt ℂ (fun w => repellingCoordinate (inverseOrbit (-w) 0 N)) u :=
    ha.comp (f := fun w : ℂ => inverseOrbit (-w) 0 N) hian
  refine ⟨hac.neg.add analyticAt_const, hformula, ?_⟩
  rw [hformula.deriv]
  exact mul_ne_zero hdn hjn

/-- The actual high imaginary gate supports a transported canonical
repelling coordinate with nonzero Jacobian and a local analytic inverse.
The depth and finite length requirements are quantitative and derived
from the genuine maps. -/
theorem exists_transported_repelling_canonicalJacobian :
    ∃ R : ℝ, 64 ≤ R ∧ ∀ u : ℂ, ∀ N : ℕ,
      (inverseCoordinate u).re ≤ 1 → R + 2 ≤ 3 * (N : ℝ) / 4 →
      64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im| →
      AnalyticAt ℂ (transportedRepellingCoordinate N) u ∧
        deriv (transportedRepellingCoordinate N) u ≠ 0 ∧
        ∃ I : ℂ → ℂ, AnalyticAt ℂ I (transportedRepellingCoordinate N u) ∧
          I (transportedRepellingCoordinate N u) = u ∧
          (∀ᶠ v in 𝓝 u, I (transportedRepellingCoordinate N v) = v) ∧
          (∀ᶠ w in 𝓝 (transportedRepellingCoordinate N u),
            transportedRepellingCoordinate N (I w) = w) := by
  obtain ⟨R, hR, hc, _⟩ := exists_repelling_canonicalJacobian
  refine ⟨R, hR, ?_⟩
  intro u N hre hN hg
  obtain ⟨ha, _, hn⟩ := transported_repelling_hasDerivAt u N R hc hre hN hg
  exact ⟨ha, hn, exists_analytic_local_inverse _ u ha hn⟩

end Kneser.FiniteGateJacobian

end
