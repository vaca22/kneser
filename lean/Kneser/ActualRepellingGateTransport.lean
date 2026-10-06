import Kneser.ActualAttractingGateTransport
import Kneser.ParabolicCoordinateJacobian

/-!
The actual reflected inverse series extends to the same high imaginary
overlap gate. The fixed preparation is an input only in the intermediate
lemma; the final bilateral endpoint constructs it once for both sides.
-/

noncomputable section

namespace Kneser.ActualRepellingGateTransport

open Filter Set Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ReflectedPreparedFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.ParabolicFatouHolomorphic Kneser.ParabolicOverlapGate
open Kneser.PreparedSpatialHolomorphy Kneser.RepellingExponentialOrbit
open Kneser.QuantitativeHornExpansion Kneser.ParabolicCoordinateJacobian
open scoped Topology

def transportedCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) (s : ℝ) : ℂ :=
  -actualInversePreparedCoordinate U H e₁ e₂ A B Γ (inverseOrbit (-u) s N) s + (N : ℂ)

def transportedCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) : ℂ :=
  -(actualInversePreparedCoefficient U H e₁ e₂ A B Γ (inverseOrbit (-u) 0 N) +
    deriv repellingCoordinate (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N)

theorem repelling_gate_transport_of_data
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ)
    (R₁ : ℝ) (_hR₁ : 0 < R₁)
    (hexp : ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R₁)
    (hcanonical : ∀ v : ℂ, R₁ + 1 ≤ (inverseCoordinate v).re →
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 = repellingCoordinate v) :
    ∃ R : ℝ, ∃ N : ℕ, 64 ≤ R ∧ R + 3 ≤ 3 * (N : ℝ) / 4 ∧
      ∀ u : ℂ, |(inverseCoordinate u).re| ≤ 1 →
        64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im| →
        transportedCoordinate U H e₁ e₂ A B Γ N u 0 =
          -repellingCoordinate (inverseOrbit (-u) 0 N) + (N : ℂ) ∧
        HasDerivWithinAt (transportedCoordinate U H e₁ e₂ A B Γ N u)
          (transportedCoefficient U H e₁ e₂ A B Γ N u) (Ici 0) 0 ∧
        PowerExpansion (transportedCoordinate U H e₁ e₂ A B Γ N u)
          (transportedCoefficient U H e₁ e₂ A B Γ N u) (6 / 5) := by
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hEven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  obtain ⟨R₂, _hR₂, hcoef⟩ :=
    ReflectedCoefficientSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoefficient
      U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ
        (fun x v => hEven (x, v))
  obtain ⟨R₃, _hR₃, hcanonJac, _hdev⟩ := exists_repelling_canonicalJacobian
  let R : ℝ := max 64 (max R₁ (max R₂ R₃))
  have hR : 64 ≤ R := le_max_left _ _
  have h₁ : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : R₂ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRpos : 0 < R := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (R + 3) / 3)
  have hN' : R + 3 ≤ 3 * (N : ℝ) / 4 := by linarith
  have hV : IsOpen (petal (R + 1)) := petal_isOpen (by linarith)
  have herror : ∀ S : Set ℂ, IsCompact S → S ⊆ petal (R + 1) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • actualInversePreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (6 / 5 : ℝ) := by
    intro S hS hp
    obtain ⟨C, CD, hC, _hCD, _hb, _hsum, heq, he6, _he10, _hderiv⟩ := hexp S hS
      (fun v hv => by have h := hp hv; change R + 1 < _ at h; linarith)
    refine ⟨C, hC, ?_⟩
    filter_upwards [he6] with s hs v hv
    rw [heq v hv]
    exact hs v hv
  have hAanalytic : ∀ v ∈ petal (R + 1),
      AnalyticAt ℂ (fun w => actualInversePreparedCoordinate U H e₁ e₂ A B Γ w 0) v ∧
        deriv (fun w => actualInversePreparedCoordinate U H e₁ e₂ A B Γ w 0) v =
          deriv repellingCoordinate v := by
    intro v hv
    have hp : v ∈ petal R₃ := by change R₃ < _; change R + 1 < _ at hv; linarith
    have heq : repellingCoordinate =ᶠ[𝓝 v]
        (fun w => actualInversePreparedCoordinate U H e₁ e₂ A B Γ w 0) := by
      filter_upwards [hV.mem_nhds hv] with w hw
      exact (hcanonical w (by change R + 1 < _ at hw; linarith)).symm
    exact ⟨(hcanonJac.2 v hp).1.congr heq, heq.symm.deriv_eq⟩
  refine ⟨R, N, hR, hN', ?_⟩
  intro u hu hg
  have hneg : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  have hg' : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-u)).im| := by
    simpa only [hneg, Complex.neg_im, abs_neg] using hg
  let w : ℝ → ℂ := fun s => inverseOrbit (-u) s N
  have hw : HasDerivWithinAt w (inverseOrbitTangent (-u) N) (Ici 0) 0 :=
    (hasDerivAt_inverse_orbit_parameter_of_gate (-u) N hg' N le_rfl).comp_ofReal.hasDerivWithinAt
  have hzero : inverseOrbit (-u) 0 N = (parabolicInverse^[N]) (-u) := by
    have hf : reflectedInverse 0 = parabolicInverse := funext reflectedInverse_zero
    rw [inverseOrbit, hf]
  have hentry : R + 2 ≤ (inverseCoordinate (w 0)).re := by
    rw [show w 0 = (parabolicInverse^[N]) (-u) by simpa only [w, Complex.ofReal_zero] using hzero]
    exact repelling_entry u N (R + 2) (abs_le.mp hu).2 (by linarith) hg
  have hwV : w 0 ∈ petal (R + 1) := by change R + 1 < _; linarith
  obtain ⟨CD, _hCD, _hb, hcoefHol, _hc, hcont, _huni, _habs⟩ :=
    hcoef R h₂ (‖inverseCoordinate (w 0)‖ + 1) (by positivity)
  have hwBounded : w 0 ∈ boundedPetal R (‖inverseCoordinate (w 0)‖ + 1) :=
    ⟨by linarith, by linarith⟩
  have hwComplex : AnalyticAt ℂ (fun s : ℂ => inverseOrbit (-u) s N) 0 :=
    (analyticAt_inverse_orbit_joint_of_gate (-u) N hg' N le_rfl).comp_of_eq
      (f := fun s : ℂ => (s, -u)) (analyticAt_id.prod analyticAt_const) rfl
  have hDanalytic := hcoefHol.analyticAt ((boundedPetal_isOpen hRpos).mem_nhds hwBounded)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hwV)
  let S : Set ℂ := Metric.closedBall (w 0) (r / 2)
  obtain ⟨C, hC, hUniform⟩ := herror S (isCompact_closedBall _ _)
    ((Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hball)
  have hwS : ∀ᶠ s : ℝ in 𝓝[>] 0, w s ∈ S :=
    hw.Ioi_of_Ici.continuousWithinAt.eventually
      (Metric.closedBall_mem_nhds _ (by positivity : 0 < r / 2))
  have he := QuantitativeGateTransition.analytic_moving_evaluation_powerExpansion
    (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
    (actualInversePreparedCoefficient U H e₁ e₂ A B Γ) S (fun s => inverseOrbit (-u) s N) (6 / 5) C
    (by norm_num) (by norm_num) hC hwComplex (hAanalytic (w 0) hwV).1 hDanalytic hwS
    (by simpa only [Complex.real_smul] using hUniform)
  have he' : PowerExpansion (fun s => actualInversePreparedCoordinate U H e₁ e₂ A B Γ (w s) s)
      (actualInversePreparedCoefficient U H e₁ e₂ A B Γ (w 0) +
        deriv repellingCoordinate (w 0) * inverseOrbitTangent (-u) N) (6 / 5) := by
    have hd0 : deriv (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)
        (inverseOrbit (-u) 0 N) = deriv repellingCoordinate (inverseOrbit (-u) 0 N) := by
      simpa only [w, Complex.ofReal_zero] using (hAanalytic (w 0) hwV).2
    simpa only [Complex.ofReal_zero, hd0, w,
      (hasDerivAt_inverse_orbit_parameter_of_gate (-u) N hg' N le_rfl).deriv] using he
  have hex : PowerExpansion (transportedCoordinate U H e₁ e₂ A B Γ N u)
      (transportedCoefficient U H e₁ e₂ A B Γ N u) (6 / 5) := by
    have h := ActualAttractingGateTransport.powerExpansion_sub_const _ _ (-(N : ℂ)) _
      (he'.const_mul (-1))
    change PowerExpansion
      (fun s : ℝ => -actualInversePreparedCoordinate U H e₁ e₂ A B Γ
        (inverseOrbit (-u) s N) s + (N : ℂ))
      (-(actualInversePreparedCoefficient U H e₁ e₂ A B Γ (inverseOrbit (-u) 0 N) +
        deriv repellingCoordinate (inverseOrbit (-u) 0 N) * inverseOrbitTangent (-u) N))
      (6 / 5)
    simpa only [neg_one_mul, sub_neg_eq_add, w, Complex.ofReal_zero,
      Kneser.ActualRepellingGateTransport.transportedCoordinate,
      Kneser.ActualRepellingGateTransport.transportedCoefficient] using h
  exact ⟨by simpa only [transportedCoordinate, w, Complex.ofReal_zero] using
      congrArg (fun z : ℂ => -z + (N : ℂ)) (hcanonical (w 0) (by linarith)),
    hex.hasDerivWithinAt (by norm_num), hex⟩

end Kneser.ActualRepellingGateTransport

end
