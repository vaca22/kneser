import Kneser.ActualDeepCoordinateData
import Kneser.UniformFiniteCoordinateTransport
import Kneser.FiniteGateJacobian
import Kneser.RealNormalizationAnchor

/-!
The same actual preparation and the same finite length produce both
coordinates on a genuine overlap gate.  Their first-order error estimates
are uniform over each compact gate subset, and their canonical spatial
Jacobians are proved nonzero.
-/

noncomputable section

namespace Kneser.ActualBilateralGate

open Filter Set Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ReflectedOrbitChainCoefficient
open Kneser.PreparedActualFirstOrder Kneser.ReflectedPreparedFirstOrder
open Kneser.ParabolicFatouHolomorphic Kneser.ParabolicCoordinateJacobian
open Kneser.ActualDeepCoordinateData
open Kneser.PreparedSpatialHolomorphy
open scoped Topology

def gate (L : ℝ) (N : ℕ) : Set ℂ :=
  {u | |(inverseCoordinate u).re| ≤ L ∧
    64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|}

def forwardCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) (s : ℝ) : ℂ :=
  actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u s N) s - (N : ℂ)

def backwardCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) (s : ℝ) : ℂ :=
  -actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) s N) s + (N : ℂ)

def forwardCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) : ℂ :=
  actualPreparedCoefficient U H e₁ e₂ A B Γ (orbit u 0 N) +
    deriv attractingCoordinate (orbit u 0 N) * orbitTangent u N

def backwardCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) : ℂ :=
  -(actualInversePreparedCoefficient U H e₁ e₂ A B Γ (inverseOrbit (-u) 0 N) +
    deriv repellingCoordinate (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N)

structure BilateralGateData (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R L : ℝ) (N : ℕ) : Prop where
  length : R + L + 2 ≤ 3 * (N : ℝ) / 4
  canonical : ∀ u ∈ gate L N,
    forwardCoordinate U H e₁ e₂ A B Γ N u 0 = attractingCoordinate (orbit u 0 N) - (N : ℂ) ∧
    backwardCoordinate U H e₁ e₂ A B Γ N u 0 = -repellingCoordinate (inverseOrbit (-u) 0 N) + (N : ℂ)
  spatial : ∀ u ∈ gate L N,
    AnalyticAt ℂ (fun v => forwardCoordinate U H e₁ e₂ A B Γ N v 0) u ∧
    deriv (fun v => forwardCoordinate U H e₁ e₂ A B Γ N v 0) u ≠ 0 ∧
    AnalyticAt ℂ (fun v => backwardCoordinate U H e₁ e₂ A B Γ N v 0) u ∧
    deriv (fun v => backwardCoordinate U H e₁ e₂ A B Γ N v 0) u ≠ 0
  uniform : ∀ S : Set ℂ, IsCompact S → S ⊆ gate L N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖forwardCoordinate U H e₁ e₂ A B Γ N u s - forwardCoordinate U H e₁ e₂ A B Γ N u 0 -
        (s : ℂ) * forwardCoefficient U H e₁ e₂ A B Γ N u‖ ≤ C * s ^ (6 / 5 : ℝ) ∧
      ‖backwardCoordinate U H e₁ e₂ A B Γ N u s - backwardCoordinate U H e₁ e₂ A B Γ N u 0 -
        (s : ℂ) * backwardCoefficient U H e₁ e₂ A B Γ N u‖ ≤ C * s ^ (6 / 5 : ℝ)
  positive : ∀ S : Set ℂ, IsCompact S → S ⊆ gate L N →
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      AnalyticAt ℂ (fun v => forwardCoordinate U H e₁ e₂ A B Γ N v s) u ∧
      AnalyticAt ℂ (fun v => backwardCoordinate U H e₁ e₂ A B Γ N v s) u
  coefficient : ∀ u ∈ gate L N,
    AnalyticAt ℂ (forwardCoefficient U H e₁ e₂ A B Γ N) u ∧
    AnalyticAt ℂ (backwardCoefficient U H e₁ e₂ A B Γ N) u

theorem analyticAt_forwardTangent (u : ℂ) (N : ℕ) :
    AnalyticAt ℂ (fun v => orbitTangent v N) u := by
  induction N with
  | zero => exact analyticAt_const
  | succ N ih =>
    have ha := (differentiable_orbit_spatial 0 N).analyticAt u
    exact (ha.cexp.mul ih).sub ((analyticAt_const.add ha).mul ha.cexp)

theorem analyticAt_inverseTangent_of_gate (v : ℂ) (N : ℕ)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|) :
    ∀ k : ℕ, k ≤ N → AnalyticAt ℂ (fun w => inverseOrbitTangent w k) v := by
  intro k
  induction k with
  | zero => intro _; exact analyticAt_const
  | succ k ih =>
    intro hk
    have ha := FiniteGateJacobian.analyticAt_inverseOrbit_spatial_of_gate v N hg k (by omega)
    have hb := FiniteGateJacobian.analyticAt_inverseOrbit_spatial_of_gate v N hg (k + 1) hk
    have hn := FiniteGateJacobian.inverse_gate_norm_lt_one v N hg k (by omega)
    have hd : 1 - inverseOrbit v 0 k ≠ 0 := by
      intro he
      rw [← sub_eq_zero.mp he] at hn
      norm_num at hn
    exact (((ih (by omega)).div (analyticAt_const.sub ha) hd).add hb).sub analyticAt_const

/-- Spatial holomorphy of finite analytic transport holds on a common
positive parameter interval over each compact initial set. The required
bounded target petal is derived from the compact zero-parameter image. -/
theorem moving_spatial_holomorphy (Q : ℝ → ℂ → ℂ) (W : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 0 < R)
    (hQ : ∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ → DifferentiableOn ℂ (Q s) (boundedPetal R Z))
    (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hw : ∀ u ∈ S, W (0, u) ∈ petal (R + 1)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      AnalyticAt ℂ (fun v => Q s (W (s, v))) u := by
  have hi : ContinuousOn (fun u => inverseCoordinate (W (0, u))) S := by
    intro u hu
    have hne : W (0, u) ≠ 0 := by
      intro he
      have hp := hw u hu
      simp [petal, he, inverseCoordinate] at hp
      linarith
    have hc : ContinuousAt (fun v => W (0, v)) u :=
      ((hW u hu).comp_of_eq (f := fun v : ℂ => (0, v))
        (analyticAt_const.prod analyticAt_id) rfl).continuousAt
    exact (continuousAt_const.div hc hne).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hi
  let Z := max 0 B + 1
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hwB : ∀ u ∈ S, W (0, u) ∈ boundedPetal R Z := by
    intro u hu
    exact ⟨hw u hu, (hB u hu).trans_lt (by dsimp [Z]; linarith [le_max_right 0 B])⟩
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, ∀ u ∈ S,
      AnalyticAt ℂ W (s, u) ∧ W (s, u) ∈ boundedPetal R Z := by
    apply hS.eventually_forall_of_forall_eventually
    intro u hu
    exact (hW u hu).eventually_analyticAt.and
      ((hW u hu).continuousAt.eventually ((boundedPetal_isOpen hR).mem_nhds (hwB u hu)))
  have hnearReal : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      AnalyticAt ℂ W (s, u) ∧ W (s, u) ∈ boundedPetal R Z :=
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hnear
  obtain ⟨s₀, hs₀, hpos⟩ := hQ Z hZ
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
    (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  filter_upwards [hnearReal, hsmall, hpositive] with s hs hss hsp u hu
  obtain ⟨hWa, hWin⟩ := hs u hu
  have hQa := (hpos s hsp hss).analyticAt ((boundedPetal_isOpen hR).mem_nhds hWin)
  have hWsp : AnalyticAt ℂ (fun v => W (s, v)) u :=
    hWa.comp_of_eq (f := fun v : ℂ => ((s : ℂ), v)) (analyticAt_const.prod analyticAt_id) rfl
  exact hQa.comp (f := fun v : ℂ => W (s, v)) hWsp

theorem reflected_gate {L : ℝ} (u : ℂ) (N : ℕ) (hu : u ∈ gate L N) :
    64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-u)).im| := by
  have he : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  simpa only [he, Complex.neg_im, abs_neg] using hu.2

theorem gate_forward_entry {L : ℝ} (u : ℂ) (N : ℕ) (R : ℝ)
    (hN : R + L + 2 ≤ 3 * (N : ℝ) / 4) (hu : u ∈ gate L N) :
    orbit u 0 N ∈ petal (R + 1) := by
  have he := ParabolicOverlapGate.finite_orbit_gate_bound parabolicMap
    Kneser.ParabolicExponentialOrbit.inverse_step_error_bound u N hu.2 N le_rfl
  have hre := (Complex.abs_re_le_norm
    (inverseCoordinate ((parabolicMap^[N]) u) - (inverseCoordinate u + (N : ℂ)))).trans he
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at hre
  have hlow := (abs_le.mp hre).1
  have hinit := (abs_le.mp hu.1).1
  rw [unfolding_orbit_zero_eq_iterate]
  change R + 1 < _
  linarith

theorem gate_backward_entry {L : ℝ} (u : ℂ) (N : ℕ) (R : ℝ)
    (hN : R + L + 2 ≤ 3 * (N : ℝ) / 4) (hu : u ∈ gate L N) :
    inverseOrbit (-u) 0 N ∈ petal (R + 1) := by
  have hneg : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  have he := ParabolicOverlapGate.finite_orbit_gate_bound parabolicInverse
    Kneser.RepellingExponentialOrbit.inverse_step_error_bound (-u) N (reflected_gate u N hu) N le_rfl
  have hre := (Complex.abs_re_le_norm
    (inverseCoordinate ((parabolicInverse^[N]) (-u)) - (inverseCoordinate (-u) + (N : ℂ)))).trans he
  simp only [hneg, Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.natCast_re] at hre
  have hlow := (abs_le.mp hre).1
  have hinit := (abs_le.mp hu.1).2
  rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
  change R + 1 < _
  linarith

theorem analyticAt_backward_transport_joint {L : ℝ} (u : ℂ) (N : ℕ) (hu : u ∈ gate L N) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => inverseOrbit (-p.2) p.1 N) (0, u) := by
  exact (ParabolicOverlapGate.analyticAt_inverse_orbit_joint_of_gate (-u) N
    (reflected_gate u N hu) N le_rfl).comp_of_eq
      (f := fun p : ℂ × ℂ => (p.1, -p.2))
        (analyticAt_fst.prod analyticAt_snd.neg) rfl

theorem forward_transport_parameter_derivative {L : ℝ}
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (N : ℕ)
    (hN : R + L + 2 ≤ 3 * (N : ℝ) / 4) (u : ℂ) (hu : u ∈ gate L N) :
    deriv (fun z : ℂ => actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u z N) 0) 0 =
      deriv attractingCoordinate (orbit u 0 N) * orbitTangent u N := by
  have hp := gate_forward_entry u N R hN hu
  have h := (hd.attracting_analytic _ hp).hasStrictDerivAt.hasDerivAt.comp 0
    (hasDerivAt_orbit_parameter_zero u N)
  have he := h.deriv
  change deriv (fun z : ℂ => actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u z N) 0) 0 =
    deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) (orbit u 0 N) * orbitTangent u N at he
  rwa [hd.attracting_derivative _ hp] at he

theorem backward_transport_parameter_derivative {L : ℝ}
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (N : ℕ)
    (hN : R + L + 2 ≤ 3 * (N : ℝ) / 4) (u : ℂ) (hu : u ∈ gate L N) :
    deriv (fun z : ℂ => actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) z N) 0) 0 =
      deriv repellingCoordinate (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N := by
  have hp := gate_backward_entry u N R hN hu
  have h := (hd.repelling_analytic _ hp).hasStrictDerivAt.hasDerivAt.comp 0
    (ParabolicOverlapGate.hasDerivAt_inverse_orbit_parameter_of_gate (-u) N
      (reflected_gate u N hu) N le_rfl)
  have he := h.deriv
  change deriv (fun z : ℂ => actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) z N) 0) 0 =
    deriv (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)
      (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N at he
  rwa [hd.repelling_derivative _ hp] at he

theorem bilateral_gate_data_of_deep {L : ℝ}
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (N : ℕ)
    (hN : R + L + 2 ≤ 3 * (N : ℝ) / 4) : BilateralGateData U H e₁ e₂ A B Γ R L N := by
  have hR := hd.depth
  have hV : IsOpen (petal (R + 1)) := petal_isOpen (by linarith)
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨congrArg (fun z : ℂ => z - (N : ℂ))
      (hd.attracting_canonical _ (gate_forward_entry u N R hN hu)),
      congrArg (fun z : ℂ => -z + (N : ℂ))
        (hd.repelling_canonical _ (gate_backward_entry u N R hN hu))⟩
  · intro u hu
    have hpA := gate_forward_entry u N R hN hu
    have hpB := gate_backward_entry u N R hN hu
    have haA := hd.attracting_analytic _ hpA
    have haB := hd.repelling_analytic _ hpB
    have hia : AnalyticAt ℂ (fun v => orbit v 0 N) u :=
      (ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 N).comp_of_eq
        (f := fun v : ℂ => (0, v)) (analyticAt_const.prod analyticAt_id) rfl
    have hib : AnalyticAt ℂ (fun v => inverseOrbit (-v) 0 N) u :=
      (analyticAt_backward_transport_joint u N hu).comp_of_eq
        (f := fun v : ℂ => (0, v)) (analyticAt_const.prod analyticAt_id) rfl
    have hforward : HasDerivAt (fun v => orbit v 0 N)
        (RealNormalizationAnchor.forwardSpatialJacobian u N) u := by
      simpa only [unfolding_orbit_zero_eq_iterate] using RealNormalizationAnchor.hasDerivAt_parabolic_iterate u N
    have hbackward := (FiniteGateJacobian.hasDerivAt_inverseOrbit_spatial_of_gate (-u) N
      (reflected_gate u N hu) N le_rfl).comp u (hasDerivAt_id u).neg
    have hda := (haA.hasStrictDerivAt.hasDerivAt.comp u hforward).sub_const (N : ℂ)
    have hdb := ((haB.hasStrictDerivAt.hasDerivAt.comp u hbackward).neg).add_const (N : ℂ)
    change HasDerivAt (fun v => forwardCoordinate U H e₁ e₂ A B Γ N v 0)
      (deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) (orbit u 0 N) *
        RealNormalizationAnchor.forwardSpatialJacobian u N) u at hda
    change HasDerivAt (fun v => backwardCoordinate U H e₁ e₂ A B Γ N v 0)
      (-(deriv (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)
        (inverseOrbit (-u) 0 N) * (FiniteGateJacobian.inverseOrbitSpatialJacobian (-u) N * -1))) u at hdb
    have hdnA : deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) (orbit u 0 N) ≠ 0 := by
      rw [hd.attracting_derivative _ hpA]
      exact (hd.attracting_jacobian.2 _ (by change R < _; change R + 1 < _ at hpA; linarith)).2.1
    have hdnB : deriv (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0) (inverseOrbit (-u) 0 N) ≠ 0 := by
      rw [hd.repelling_derivative _ hpB]
      exact (hd.repelling_jacobian.2 _ (by change R < _; change R + 1 < _ at hpB; linarith)).2.1
    refine ⟨(haA.comp (f := fun v : ℂ => orbit v 0 N) hia).sub analyticAt_const, ?_,
      (haB.comp (f := fun v : ℂ => inverseOrbit (-v) 0 N) hib).neg.add analyticAt_const, ?_⟩
    · rw [hda.deriv]
      exact mul_ne_zero hdnA (RealNormalizationAnchor.forwardSpatialJacobian_ne_zero u N)
    · rw [hdb.deriv]
      exact neg_ne_zero.mpr (mul_ne_zero hdnB (mul_ne_zero
        (FiniteGateJacobian.inverseOrbitSpatialJacobian_ne_zero_of_gate (-u) N
          (reflected_gate u N hu) N le_rfl) (by norm_num)))
  · intro S hS hSgate
    obtain ⟨CA, hCA, hEA⟩ := UniformFiniteCoordinateTransport.uniform_moving_evaluation
      (fun s v => actualPreparedCoordinate U H e₁ e₂ A B Γ v s)
      (actualPreparedCoefficient U H e₁ e₂ A B Γ)
      (fun p => orbit p.2 p.1 N) S (petal (R + 1)) hS hV
      (fun u _ => ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 N)
      (fun u hu => gate_forward_entry u N R hN (hSgate hu))
      hd.attracting_analytic hd.attracting_coefficient_analytic hd.attracting_error
    obtain ⟨CB, hCB, hEB⟩ := UniformFiniteCoordinateTransport.uniform_moving_evaluation
      (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
      (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
      (fun p => inverseOrbit (-p.2) p.1 N) S (petal (R + 1)) hS hV
      (fun u hu => analyticAt_backward_transport_joint u N (hSgate hu))
      (fun u hu => gate_backward_entry u N R hN (hSgate hu))
      hd.repelling_analytic hd.repelling_coefficient_analytic hd.repelling_error
    refine ⟨CA + CB, by positivity, ?_⟩
    have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
    filter_upwards [hEA, hEB, hpos] with s hsA hsB hsp u hu
    have hq : 0 ≤ s ^ (6 / 5 : ℝ) := (Real.rpow_pos_of_pos hsp _).le
    have ha := hsA u hu
    have hb := hsB u hu
    simp only [forward_transport_parameter_derivative U H e₁ e₂ A B Γ R hd N hN u (hSgate hu)] at ha
    simp only [backward_transport_parameter_derivative U H e₁ e₂ A B Γ R hd N hN u (hSgate hu)] at hb
    have heA : forwardCoordinate U H e₁ e₂ A B Γ N u s - forwardCoordinate U H e₁ e₂ A B Γ N u 0 -
        (s : ℂ) * forwardCoefficient U H e₁ e₂ A B Γ N u =
      actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u s N) s -
        actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u 0 N) 0 -
        (s : ℂ) * (actualPreparedCoefficient U H e₁ e₂ A B Γ (orbit u 0 N) +
          deriv attractingCoordinate (orbit u 0 N) * orbitTangent u N) := by
      dsimp [forwardCoordinate, forwardCoefficient]
      ring
    have heB : backwardCoordinate U H e₁ e₂ A B Γ N u s - backwardCoordinate U H e₁ e₂ A B Γ N u 0 -
        (s : ℂ) * backwardCoefficient U H e₁ e₂ A B Γ N u =
      -(actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) s N) s -
        actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) 0 N) 0 -
        (s : ℂ) * (actualInversePreparedCoefficient U H e₁ e₂ A B Γ (inverseOrbit (-u) 0 N) +
          deriv repellingCoordinate (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N)) := by
      dsimp [backwardCoordinate, backwardCoefficient]
      ring
    rw [heA, heB, norm_neg]
    exact ⟨ha.trans (mul_le_mul_of_nonneg_right (by linarith) hq),
      hb.trans (mul_le_mul_of_nonneg_right (by linarith) hq)⟩
  · intro S hS hSgate
    have ha := moving_spatial_holomorphy
      (fun s u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
      (fun p => orbit p.2 p.1 N) R (by linarith) hd.attracting_positive S hS
      (fun u _ => ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 N)
      (fun u hu => gate_forward_entry u N R hN (hSgate hu))
    have hb := moving_spatial_holomorphy
      (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
      (fun p => inverseOrbit (-p.2) p.1 N) R (by linarith) hd.repelling_positive S hS
      (fun u hu => analyticAt_backward_transport_joint u N (hSgate hu))
      (fun u hu => gate_backward_entry u N R hN (hSgate hu))
    filter_upwards [ha, hb] with s hsA hsB u hu
    exact ⟨(hsA u hu).sub analyticAt_const, (hsB u hu).neg.add analyticAt_const⟩
  · intro u hu
    have hpA := gate_forward_entry u N R hN hu
    have hpB := gate_backward_entry u N R hN hu
    have hia : AnalyticAt ℂ (fun v => orbit v 0 N) u :=
      (differentiable_orbit_spatial 0 N).analyticAt u
    have hib : AnalyticAt ℂ (fun v => inverseOrbit (-v) 0 N) u :=
      (analyticAt_backward_transport_joint u N hu).comp_of_eq
        (f := fun v : ℂ => (0, v)) (analyticAt_const.prod analyticAt_id) rfl
    have hcanA := (hd.attracting_jacobian.2 (orbit u 0 N)
      (by change R < _; change R + 1 < _ at hpA; linarith)).1.deriv
    have hcanB := (hd.repelling_jacobian.2 (inverseOrbit (-u) 0 N)
      (by change R < _; change R + 1 < _ at hpB; linarith)).1.deriv
    have hDA := (hd.attracting_coefficient_analytic _ hpA).comp (f := fun v : ℂ => orbit v 0 N) hia
    have hDB := (hd.repelling_coefficient_analytic _ hpB).comp (f := fun v : ℂ => inverseOrbit (-v) 0 N) hib
    have hTA := analyticAt_forwardTangent u N
    have hTB : AnalyticAt ℂ (fun v => inverseOrbitTangent (-v) N) u :=
      (analyticAt_inverseTangent_of_gate (-u) N (reflected_gate u N hu) N le_rfl).comp analyticAt_id.neg
    exact ⟨hDA.add ((hcanA.comp (f := fun v : ℂ => orbit v 0 N) hia).mul hTA),
      (hDB.add ((hcanB.comp (f := fun v : ℂ => inverseOrbit (-v) 0 N) hib).mul hTB)).neg⟩

/-- The two compact-uniform gate expansions and the canonical nonzero
spatial Jacobians are built from one actual preparation, with one common
finite length. -/
theorem exists_actual_bilateral_gate :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          ∀ L : ℝ, 0 < L → ∃ N : ℕ, BilateralGateData U H e₁ e₂ A B Γ R L N := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd⟩ := exists_actual_deep_coordinate_data
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, ?_⟩
  intro L _hL
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (R + L + 2) / 3)
  have hN' : R + L + 2 ≤ 3 * (N : ℝ) / 4 := by linarith
  exact ⟨N, bilateral_gate_data_of_deep U H e₁ e₂ A B Γ R hd N hN'⟩

end Kneser.ActualBilateralGate

end
