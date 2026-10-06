import Kneser.ActualGateAbel
import Kneser.HigherMovingPreparedCoordinate
import Kneser.ReflectedHigherMovingPreparedCoordinate
import Kneser.CommonQuadraticBaseline

/-! A fixed gate has one finite initial entry. Arbitrarily many later
petal iterates increase the depth without increasing that gate's height.
The complete finite parameter transport remains genuinely joint analytic. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.HigherGateSeeds

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.ActualBilateralGate Kneser.ActualGateAbel
open scoped Topology

def forwardSeed (N L : ℕ) (p : ℂ × ℂ) : ℂ := orbit (orbit p.2 p.1 N) p.1 L

def backwardSeed (N L : ℕ) (p : ℂ × ℂ) : ℂ := inverseOrbit (inverseOrbit (-p.2) p.1 N) p.1 L

theorem orbit_add (u s : ℂ) (N L : ℕ) :
    orbit u s (N + L) = orbit (orbit u s N) s L := by
  induction L with
  | zero => simp
  | succ L ih => simp only [Nat.add_succ, orbit_succ, ih]

theorem inverseOrbit_add (v s : ℂ) (N L : ℕ) :
    inverseOrbit v s (N + L) = inverseOrbit (inverseOrbit v s N) s L := by
  induction L with
  | zero => simp
  | succ L ih => simp only [Nat.add_succ, inverseOrbit_succ, ih]

theorem forwardSeed_eq (N L : ℕ) (p : ℂ × ℂ) :
    forwardSeed N L p = orbit p.2 p.1 (N + L) := (orbit_add ..).symm

theorem backwardSeed_eq (N L : ℕ) (p : ℂ × ℂ) :
    backwardSeed N L p = inverseOrbit (-p.2) p.1 (N + L) := (inverseOrbit_add ..).symm

theorem forwardSeed_analytic (N L : ℕ) (u : ℂ) :
    AnalyticAt ℂ (forwardSeed N L) (0, u) := by
  have he : forwardSeed N L = fun p : ℂ × ℂ => orbit p.2 p.1 (N + L) :=
    funext (forwardSeed_eq N L)
  rw [he]
  exact ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 (N + L)

theorem backwardSeed_analytic (N L : ℕ) (hN : (130 : ℝ) ≤ 3 * (N : ℝ) / 4)
    (u : ℂ) (hu : u ∈ gate 64 N) : AnalyticAt ℂ (backwardSeed N L) (0, u) := by
  have hp := gate_backward_entry u N 64 (by norm_num; exact hN) hu
  have hv : 64 ≤ (inverseCoordinate (inverseOrbit (-u) 0 N)).re := by
    have hh : (64 : ℝ) + 1 < (inverseCoordinate (inverseOrbit (-u) 0 N)).re := hp
    linarith
  have hsmall : ∀ j < L, ‖inverseOrbit (inverseOrbit (-u) 0 N) 0 j‖ < 1 := by
    intro j _
    rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
    have h := RepellingFatouCoordinate.inverse_iterate_norm_bound _ 64 (by norm_num) hv j
    apply lt_of_le_of_lt h
    apply (div_lt_iff₀ (by positivity : 0 < (64 : ℝ) + (j : ℝ) / 2)).mpr
    have hj := Nat.cast_nonneg (α := ℝ) j
    linarith
  exact (ReflectedHigherMovingOrbitDiscs.analyticAt_inverseOrbit_joint
    (inverseOrbit (-u) 0 N) 0 L (by norm_num) hsmall).comp_of_eq
      (analyticAt_fst.prod (analyticAt_backward_transport_joint u N hu)) rfl

theorem forwardSeed_depth (N L : ℕ) (hN : (130 : ℝ) ≤ 3 * (N : ℝ) / 4)
    (u : ℂ) (hu : u ∈ gate 64 N) :
    64 + (L : ℝ) / 2 ≤ (inverseCoordinate (forwardSeed N L (0, u))).re := by
  have hp := gate_forward_entry u N 64 (by norm_num; exact hN) hu
  have hv : 64 ≤ (inverseCoordinate (orbit u 0 N)).re := by
    have hh : (64 : ℝ) + 1 < (inverseCoordinate (orbit u 0 N)).re := hp
    linarith
  dsimp only [forwardSeed]
  rw [unfolding_orbit_zero_eq_iterate]
  have h := iterate_inverse_re (orbit u 0 N) (by linarith : 32 ≤ (inverseCoordinate (orbit u 0 N)).re) L
  linarith

theorem backwardSeed_depth (N L : ℕ) (hN : (130 : ℝ) ≤ 3 * (N : ℝ) / 4)
    (u : ℂ) (hu : u ∈ gate 64 N) :
    64 + (L : ℝ) / 2 ≤ (inverseCoordinate (backwardSeed N L (0, u))).re := by
  have hp := gate_backward_entry u N 64 (by norm_num; exact hN) hu
  have hv : 64 ≤ (inverseCoordinate (inverseOrbit (-u) 0 N)).re := by
    have hh : (64 : ℝ) + 1 < (inverseCoordinate (inverseOrbit (-u) 0 N)).re := hp
    linarith
  dsimp only [backwardSeed]
  rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
  exact RepellingFatouCoordinate.inverse_iterate_re _ 64 (by norm_num) hv L

/-- Finite Abel transport is uniform for an analytic moving compact family.
The positive-parameter identities are obtained from genuine local Abel
identities, and all later zero-parameter seeds remain in the same petal. -/
theorem forward_iterated_abel_uniform (Q : ℝ → ℂ → ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hQ : LocalAbel Q (fun s u => unfolding s u) R)
    (W : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hdeep : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W (0, u))).re) (L : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      Q s (orbit (W (s, u)) s L) = Q s (W (s, u)) + (L : ℂ) := by
  induction L with
  | zero => exact Filter.Eventually.of_forall (by intro s u hu; simp)
  | succ L ih =>
    let WL : ℂ × ℂ → ℂ := fun p => orbit (W p) p.1 L
    have hWL : ∀ u ∈ S, AnalyticAt ℂ WL (0, u) := by
      intro u hu
      exact (ParabolicOverlapGate.analyticAt_forward_orbit_joint (W (0, u)) 0 L).comp_of_eq
        (analyticAt_fst.prod (hW u hu)) rfl
    have hdL : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (WL (0, u))).re := by
      intro u hu
      dsimp only [WL]
      rw [unfolding_orbit_zero_eq_iterate]
      have h := iterate_inverse_re (W (0, u)) (by linarith [hdeep u hu]) L
      have hn := Nat.cast_nonneg (α := ℝ) L
      linarith [hdeep u hu]
    have hs := uniform_moving_local_property _ R hQ WL S hS hWL hdL
    filter_upwards [ih, hs] with s hih hs u hu
    rw [orbit_succ, hs u hu, hih u hu]
    push_cast
    ring

theorem backward_iterated_abel_uniform (Q : ℝ → ℂ → ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hQ : LocalAbel Q (fun s u => reflectedInverse s u) R)
    (W : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hdeep : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W (0, u))).re) (L : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      Q s (inverseOrbit (W (s, u)) s L) = Q s (W (s, u)) + (L : ℂ) := by
  induction L with
  | zero => exact Filter.Eventually.of_forall (by intro s u hu; simp)
  | succ L ih =>
    let WL : ℂ × ℂ → ℂ := fun p => inverseOrbit (W p) p.1 L
    have hWL : ∀ u ∈ S, AnalyticAt ℂ WL (0, u) := by
      intro u hu
      have hsmall : ∀ j < L, ‖inverseOrbit (W (0, u)) 0 j‖ < 1 := by
        intro j _
        rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
        have h := RepellingFatouCoordinate.inverse_iterate_norm_bound _ R hR
          (by linarith [hdeep u hu]) j
        apply lt_of_le_of_lt h
        apply (div_lt_iff₀ (by positivity : 0 < R + (j : ℝ) / 2)).mpr
        have hj := Nat.cast_nonneg (α := ℝ) j
        linarith
      exact (ReflectedHigherMovingOrbitDiscs.analyticAt_inverseOrbit_joint
        (W (0, u)) 0 L (by norm_num) hsmall).comp_of_eq
          (analyticAt_fst.prod (hW u hu)) rfl
    have hdL : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (WL (0, u))).re := by
      intro u hu
      dsimp only [WL]
      rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
      have h := RepellingFatouCoordinate.inverse_iterate_re (W (0, u)) (R + 2)
        (by linarith) (hdeep u hu) L
      have hn := Nat.cast_nonneg (α := ℝ) L
      linarith
    have hs := uniform_moving_local_property _ R hQ WL S hS hWL hdL
    filter_upwards [ih, hs] with s hih hs u hu
    rw [inverseOrbit_succ, hs u hu, hih u hu]
    push_cast
    ring

end Kneser.HigherGateSeeds
end
