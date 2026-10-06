import Kneser.FiniteCoordinateTransport
import Kneser.ParabolicOverlapGate
import Kneser.BilateralFirstOrder
import Kneser.ParabolicFatouHolomorphic
import Kneser.QuantitativeGateTransition

/-!
The actual attracting first coefficient extends to an actual high imaginary
overlap gate by a finite genuine exponential orbit. No gate-membership,
moving-orbit remainder or differentiability hypothesis is assumed.
-/

noncomputable section

namespace Kneser.ActualAttractingGateTransport

open Filter Set Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.ParabolicFatouHolomorphic Kneser.ParabolicOverlapGate
open Kneser.PreparedSpatialHolomorphy
open scoped Topology
open Kneser.QuantitativeHornExpansion

def canonicalAttracting (u : ℂ) : ℂ :=
  correctedCoordinate parabolicMap ParabolicFatouCoordinate.model
    (coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u

def transportedCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) (s : ℝ) : ℂ :=
  actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit u s N) s - (N : ℂ)

def transportedCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (u : ℂ) : ℂ :=
  actualPreparedCoefficient U H e₁ e₂ A B Γ (orbit u 0 N) +
    deriv canonicalAttracting (orbit u 0 N) * orbitTangent u N

theorem powerExpansion_sub_const (f : ℝ → ℂ) (d c : ℂ) (q : ℝ)
    (hf : PowerExpansion f d q) : PowerExpansion (fun s => f s - c) d q := by
  obtain ⟨C, hC, he⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [he] with s hs
  have h : (f s - c) - (f 0 - c) - (s : ℂ) * d = f s - f 0 - (s : ℂ) * d := by ring
  rw [h]
  exact hs

/-- The same genuine preparation supplies the deep-petal series and the
parameter derivative of its finite extension on an actual overlap gate. -/
theorem attracting_gate_transport_of_data
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ)
    (R₁ : ℝ) (_hR₁ : 0 < R₁)
    (hexp : BilateralFirstOrder.AttractingCompactFirstOrder U H e₁ e₂ A B Γ R₁)
    (hcanonical : ∀ u : ℂ, R₁ + 1 ≤ (inverseCoordinate u).re →
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 = canonicalAttracting u) :
      ∃ R : ℝ, ∃ N : ℕ, 32 ≤ R ∧ R + 3 ≤ 3 * (N : ℝ) / 4 ∧
        ∀ u : ℂ, |(inverseCoordinate u).re| ≤ 1 →
          64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im| →
          transportedCoordinate U H e₁ e₂ A B Γ N u 0 =
            canonicalAttracting (orbit u 0 N) - (N : ℂ) ∧
          HasDerivWithinAt (transportedCoordinate U H e₁ e₂ A B Γ N u)
            (transportedCoefficient U H e₁ e₂ A B Γ N u) (Ici 0) 0 ∧
          PowerExpansion (transportedCoordinate U H e₁ e₂ A B Γ N u)
            (transportedCoefficient U H e₁ e₂ A B Γ N u) (6 / 5) := by
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hEven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  obtain ⟨R₂, hR₂, hcoef⟩ :=
    PreparedCoefficientSpatialHolomorphy.exists_holomorphic_actualPreparedCoefficient
      U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ
        (fun x v => hEven (x, v))
  obtain ⟨R₃, C₃, hR₃, _hC₃, hhol, _huniform, _habel⟩ :=
    ParabolicFatouHolomorphic.exists_holomorphic_attracting_coordinate
  let R : ℝ := max 32 (max R₁ (max R₂ R₃))
  have hR : 32 ≤ R := le_max_left _ _
  have h₁ : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : R₂ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRpos : 0 < R := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (R + 3) / 3)
  have hN' : R + 3 ≤ 3 * (N : ℝ) / 4 := by linarith
  have hV : IsOpen (petal (R + 1)) := petal_isOpen (by linarith)
  have herror : ∀ S : Set ℂ, IsCompact S → S ⊆ petal (R + 1) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualPreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualPreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • actualPreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (6 / 5 : ℝ) := by
    intro S hS hp
    obtain ⟨_hsum, heq, C, hC, he6, _he10, _hderiv⟩ := hexp S hS
      (fun v hv => by have h := hp hv; change R + 1 < _ at h; linarith)
    refine ⟨C, hC, ?_⟩
    filter_upwards [he6] with s hs v hv
    rw [heq v hv]
    exact hs v hv
  have hAdiff : ∀ v ∈ petal (R + 1),
      HasDerivAt (fun w => actualPreparedCoordinate U H e₁ e₂ A B Γ w 0)
        (deriv canonicalAttracting v) v := by
    intro v hv
    have hp : v ∈ petal R₃ := by change R₃ < _; change R + 1 < _ at hv; linarith
    have heq : (fun w => actualPreparedCoordinate U H e₁ e₂ A B Γ w 0) =ᶠ[𝓝 v]
        canonicalAttracting := by
      filter_upwards [hV.mem_nhds hv] with w hw
      exact hcanonical w (by change R + 1 < _ at hw; linarith)
    exact ((hhol v hp).differentiableAt ((petal_isOpen (by linarith)).mem_nhds hp)).hasDerivAt
      |>.congr_of_eventuallyEq heq
  have hAanalytic : ∀ v ∈ petal (R + 1),
      AnalyticAt ℂ (fun w => actualPreparedCoordinate U H e₁ e₂ A B Γ w 0) v := by
    intro v hv
    have hp : v ∈ petal R₃ := by change R₃ < _; change R + 1 < _ at hv; linarith
    have heq : canonicalAttracting =ᶠ[𝓝 v]
        (fun w => actualPreparedCoordinate U H e₁ e₂ A B Γ w 0) := by
      filter_upwards [hV.mem_nhds hv] with w hw
      exact (hcanonical w (by change R + 1 < _ at hw; linarith)).symm
    exact (hhol.analyticAt ((petal_isOpen (by linarith)).mem_nhds hp)).congr heq
  refine ⟨R, N, hR, hN', ?_⟩
  intro u hu hg
  let w : ℝ → ℂ := fun s => orbit u s N
  have hw : HasDerivWithinAt w (orbitTangent u N) (Ici 0) 0 :=
    (hasDerivAt_orbit_parameter_zero u N).comp_ofReal.hasDerivWithinAt
  have hentry : R + 2 ≤ (inverseCoordinate (w 0)).re := by
    simpa only [w, Complex.ofReal_zero, unfolding_orbit_zero_eq_iterate] using
      attracting_entry u N (R + 2) (abs_le.mp hu).1 (by linarith) hg
  have hwV : w 0 ∈ petal (R + 1) := by change R + 1 < _; linarith
  obtain ⟨CD, _hCD, _hb, hcoefHol, _hc, hcont, _huni, _habs⟩ :=
    hcoef R h₂ (‖inverseCoordinate (w 0)‖ + 1) (by positivity)
  have hwBounded : w 0 ∈ boundedPetal R (‖inverseCoordinate (w 0)‖ + 1) :=
    ⟨by linarith, by linarith⟩
  have hd := FiniteCoordinateTransport.hasDerivWithinAt_moving_composition_of_compact_expansion
    (fun s v => actualPreparedCoordinate U H e₁ e₂ A B Γ v s)
    (actualPreparedCoefficient U H e₁ e₂ A B Γ) (petal (R + 1)) hV herror w
    (orbitTangent u N) (deriv canonicalAttracting (w 0)) hw hwV
      (hcont (w 0) hwBounded) (hAdiff (w 0) hwV)
  have hwComplex : AnalyticAt ℂ (fun s : ℂ => orbit u s N) 0 :=
    (analyticAt_forward_orbit_joint u 0 N).comp_of_eq
      (f := fun s : ℂ => (s, u)) (analyticAt_id.prod analyticAt_const) rfl
  have hDanalytic := hcoefHol.analyticAt ((boundedPetal_isOpen hRpos).mem_nhds hwBounded)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hwV)
  let S : Set ℂ := Metric.closedBall (w 0) (r / 2)
  have hS : IsCompact S := isCompact_closedBall _ _
  obtain ⟨C, hC, hUniform⟩ := herror S hS
    ((Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hball)
  have hwS : ∀ᶠ s : ℝ in 𝓝[>] 0, w s ∈ S :=
    hw.Ioi_of_Ici.continuousWithinAt.eventually
      (Metric.closedBall_mem_nhds _ (by positivity : 0 < r / 2))
  have he := QuantitativeGateTransition.analytic_moving_evaluation_powerExpansion
    (fun s v => actualPreparedCoordinate U H e₁ e₂ A B Γ v s)
    (actualPreparedCoefficient U H e₁ e₂ A B Γ) S (fun s => orbit u s N) (6 / 5) C
    (by norm_num) (by norm_num) hC hwComplex (hAanalytic (w 0) hwV) hDanalytic hwS
    (by simpa only [Complex.real_smul] using hUniform)
  have he' : PowerExpansion (fun s => actualPreparedCoordinate U H e₁ e₂ A B Γ (w s) s)
      (transportedCoefficient U H e₁ e₂ A B Γ N u) (6 / 5) := by
    have hd0 : deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) (orbit u 0 N) =
        deriv canonicalAttracting (orbit u 0 N) := by
      simpa only [w, Complex.ofReal_zero] using (hAdiff (w 0) hwV).deriv
    simpa only [Complex.ofReal_zero, hd0,
      (hasDerivAt_orbit_parameter_zero u N).deriv, w, transportedCoefficient] using he
  refine ⟨?_, ?_, powerExpansion_sub_const _ _ (N : ℂ) _ he'⟩
  · exact congrArg (fun z : ℂ => z - (N : ℂ))
      (hcanonical (w 0) (by linarith))
  · exact hd.sub_const (N : ℂ)

/-- Actual germs, orbit entry, canonical normalization and a quantitative
parameter expansion are all constructed at the final existence endpoint. -/
theorem exists_actual_attracting_gate_derivative :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R : ℝ, ∃ N : ℕ, 32 ≤ R ∧ R + 3 ≤ 3 * (N : ℝ) / 4 ∧
        ∀ u : ℂ, |(inverseCoordinate u).re| ≤ 1 →
          64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im| →
          transportedCoordinate U H e₁ e₂ A B Γ N u 0 =
            canonicalAttracting (orbit u 0 N) - (N : ℂ) ∧
          HasDerivWithinAt (transportedCoordinate U H e₁ e₂ A B Γ N u)
            (transportedCoefficient U H e₁ e₂ A B Γ N u) (Ici 0) 0 ∧
          PowerExpansion (transportedCoordinate U H e₁ e₂ A B Γ N u)
            (transportedCoefficient U H e₁ e₂ A B Γ N u) (6 / 5) := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R₁, hR₁, hexp, _hrep,
    hcanonical, _hrepCanonical⟩ := BilateralFirstOrder.exists_actual_bilateral_explicit_first_order
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata,
    attracting_gate_transport_of_data U H e₁ e₂ A B K F Γ hdata R₁ hR₁ hexp hcanonical⟩

end Kneser.ActualAttractingGateTransport

end
