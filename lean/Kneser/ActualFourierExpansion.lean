import Kneser.ActualQuantitativeGateTransition
import Kneser.ActualTransitionPeriodicity
import Kneser.DiscGateFourier

/-!
Actual integer Fourier corrections, derived end to end from the genuine
exponential unfolding.  One preparation, actual finite gate, constructed
moving inverse and real normalization anchor supply every mode.  This
endpoint proves the integrals and coefficient algebra; global Kneser
sewing and its exponentially small coefficient comparison are separate.
-/

noncomputable section
namespace Kneser.ActualFourierExpansion

open Filter Set Metric Kneser.GateFourierDerivative Kneser.QuantitativeHornExpansion
open Kneser.ActualQuantitativeGateTransition Kneser.ActualDeepCoordinateData
open Kneser.ReflectedOrbitChainCoefficient Kneser.ActualGateAbel
open scoped Topology

/-- Every series used by the actual transition coefficient is absolutely
convergent, including the orbit of the real normalization anchor. -/
structure AbsoluteGateCoefficientData (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) : Prop where
  attracting_absolute : ∀ w ∈ ball (0 : ℂ) 4,
    Summable (fun k => ‖Kneser.ActualOrbitChainCoefficient.explicitTerm A B Γ
      (Kneser.ExponentialUnfolding.orbit (chartPoint Y (V 0 w)) 0 N) k‖)
  repelling_absolute : ∀ w ∈ ball (0 : ℂ) 4,
    Summable (fun k => ‖Kneser.ReflectedOrbitChainCoefficient.explicitTerm A B Γ
      (Kneser.RepellingExponentialOrbit.inverseOrbit (-(chartPoint Y (V 0 w))) 0 N) k‖)
  anchor_absolute : Summable (fun k => ‖Kneser.ActualOrbitChainCoefficient.explicitTerm A B Γ
    (Kneser.ExponentialUnfolding.orbit Kneser.RealNormalizationAnchor.normalizationAnchor 0 M) k‖)
  attracting_explicit : ∀ w ∈ ball (0 : ℂ) 4,
    Kneser.ActualBilateralGate.forwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) =
      deriv (fun s => Kneser.ExponentialModelTime.preparedModelTime U H e₁ e₂ s
        (Kneser.ExponentialUnfolding.orbit (chartPoint Y (V 0 w)) 0 N)) 0 +
      (∑' k : ℕ, Kneser.ActualOrbitChainCoefficient.explicitTerm A B Γ
        (Kneser.ExponentialUnfolding.orbit (chartPoint Y (V 0 w)) 0 N) k) +
      deriv Kneser.ParabolicCoordinateJacobian.attractingCoordinate
        (Kneser.ExponentialUnfolding.orbit (chartPoint Y (V 0 w)) 0 N) *
        Kneser.ExponentialUnfolding.orbitTangent (chartPoint Y (V 0 w)) N
  repelling_explicit : ∀ w ∈ ball (0 : ℂ) 4,
    Kneser.ActualBilateralGate.backwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) =
      -(deriv (fun s => Kneser.ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s
          (Kneser.RepellingExponentialOrbit.inverseOrbit (-(chartPoint Y (V 0 w))) 0 N)) 0 +
        (∑' k : ℕ, Kneser.ReflectedOrbitChainCoefficient.explicitTerm A B Γ
          (Kneser.RepellingExponentialOrbit.inverseOrbit (-(chartPoint Y (V 0 w))) 0 N) k) +
        deriv Kneser.ParabolicCoordinateJacobian.repellingCoordinate
          (Kneser.RepellingExponentialOrbit.inverseOrbit (-(chartPoint Y (V 0 w))) 0 N) *
          Kneser.ReflectedOrbitChainCoefficient.inverseOrbitTangent (-(chartPoint Y (V 0 w))) N)
  anchor_explicit : Kneser.ActualNormalizationAnchorExpansion.anchorCoefficient U H e₁ e₂ A B Γ M =
    deriv (fun s => Kneser.ExponentialModelTime.preparedModelTime U H e₁ e₂ s
      (Kneser.ExponentialUnfolding.orbit Kneser.RealNormalizationAnchor.normalizationAnchor 0 M)) 0 +
    (∑' k : ℕ, Kneser.ActualOrbitChainCoefficient.explicitTerm A B Γ
      (Kneser.ExponentialUnfolding.orbit Kneser.RealNormalizationAnchor.normalizationAnchor 0 M) k) +
    deriv Kneser.ParabolicCoordinateJacobian.attractingCoordinate
      (Kneser.ExponentialUnfolding.orbit Kneser.RealNormalizationAnchor.normalizationAnchor 0 M) *
      Kneser.ExponentialUnfolding.orbitTangent Kneser.RealNormalizationAnchor.normalizationAnchor M

theorem absolute_gate_coefficients_of_deep
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V := by
  have hpoint (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :
      chartPoint Y (V 0 w) ∈ Kneser.ActualBilateralGate.gate 64 N :=
    chartPoint_in_gate N Y ht.height (V 0 w)
      (closedBall_subset_closedBall (by norm_num) (ht.inverse_zero w hw).1)
  have ha (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :=
    Kneser.ActualBilateralGate.gate_forward_entry _ N R ht.bilateral.length (hpoint w hw)
  have hr (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :=
    Kneser.ActualBilateralGate.gate_backward_entry _ N R ht.bilateral.length (hpoint w hw)
  refine ⟨(fun w hw => hd.attracting_absolute _ (ha w hw)),
    (fun w hw => hd.repelling_absolute _ (hr w hw)),
    hd.attracting_absolute _ ht.anchor_entry, ?_, ?_, ?_⟩
  · intro w hw
    dsimp only [Kneser.ActualBilateralGate.forwardCoefficient]
    rw [hd.attracting_explicit _ (ha w hw)]
  · intro w hw
    dsimp only [Kneser.ActualBilateralGate.backwardCoefficient]
    rw [hd.repelling_explicit _ (hr w hw)]
  · dsimp only [Kneser.ActualNormalizationAnchorExpansion.anchorCoefficient]
    rw [hd.attracting_explicit _ ht.anchor_entry]

structure FourierExpansionData (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (Vroot p Rp : ℂ → ℂ) : Prop where
  root_analytic : AnalyticAt ℂ Vroot 0
  root_zero : Vroot 0 = 0
  root_equation : ∀ᶠ x in 𝓝 0, Kneser.ExponentialCuspParameter.cuspParameter (Vroot x) = x ^ 2
  parameter_analytic : AnalyticAt ℂ p 0
  parameter_zero : p 0 = 0
  parameter_derivative : HasDerivAt p 2 0
  parameter_multiplier : ∀ x, p (x ^ 2) = -Complex.log (1 + Vroot x) * Complex.log (1 + Vroot (-x))
  parameter_remainder_analytic : AnalyticAt ℂ Rp 0
  parameter_second_order : ∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * Rp s
  fourier : ∀ n : ℤ, PowerExpansion (fun s => gateFourierCoefficient n 0 (T s))
    (gateCorrectionCoefficient n 0 D) (6 / 5)
  raw : ∀ n : ℤ, PowerExpansion (Kneser.realHornCoefficient n
    (fun t => gateFourierCoefficient n 0 (T t))
    (fun t => gateFourierCoefficient 0 0 (T t)))
    (Complex.exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 (T 0)) *
      (gateCorrectionCoefficient n 0 D - Kneser.fourierFrequency n *
        gateFourierCoefficient n 0 (T 0) * gateCorrectionCoefficient 0 0 D)) (6 / 5)
  logarithm : ∀ n : ℤ, gateFourierCoefficient n 0 (T 0) ≠ 0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖Complex.log (Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n 0 (T t))
        (fun t => gateFourierCoefficient 0 0 (T t)) s) -
        Kneser.hornKappa n (gateFourierCoefficient n 0 (T 0))
          (gateCorrectionCoefficient n 0 D) (gateCorrectionCoefficient 0 0 D) * p (s : ℂ)‖ ≤
        C * ‖p (s : ℂ)‖ ^ (6 / 5 : ℝ)


/-- The actual transition derivative is the ratio of the two genuine
physical coordinate Jacobians; the constructed inverse's derivative
is proved from its actual inverse equation. -/
theorem transition_derivative_ratio
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :
    deriv (transitionValue U H e₁ e₂ A B Γ N M Y V 0) w =
      deriv (fun u => Kneser.ActualBilateralGate.forwardCoordinate U H e₁ e₂ A B Γ N u 0)
        (chartPoint Y (V 0 w)) /
      deriv (fun u => Kneser.ActualBilateralGate.backwardCoordinate U H e₁ e₂ A B Γ N u 0)
        (chartPoint Y (V 0 w)) := by
  let F := repellingChart U H e₁ e₂ A B Γ N Y 0
  let A₀ := attractingChart U H e₁ e₂ A B Γ N Y 0
  have hclosed : V 0 w ∈ closedBall (0 : ℂ) 64 := by
    have hn : ‖V 0 w‖ ≤ 16 := by simpa [mem_closedBall, dist_zero_right] using (ht.inverse_zero w hw).1
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hpoint := chartPoint_in_gate N Y ht.height (V 0 w) hclosed
  have hchart := chartPoint_analytic N Y ht.height (V 0 w) hclosed
  have hFa : AnalyticAt ℂ F (V 0 w) :=
    ((ht.bilateral.spatial _ hpoint).2.2.1.comp_of_eq hchart rfl).sub analyticAt_const
  have hAa : AnalyticAt ℂ A₀ (V 0 w) :=
    (ht.bilateral.spatial _ hpoint).1.comp_of_eq hchart rfl
  have hVa := ht.inverse_zero_analytic w hw
  have hEq : (fun z => F (V 0 z)) =ᶠ[𝓝 w] (fun z : ℂ => z) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact (ht.inverse_zero z hz).2
  have hcomp := (hFa.hasStrictDerivAt.hasDerivAt.comp w hVa.hasStrictDerivAt.hasDerivAt).deriv
  change deriv (fun z => F (V 0 z)) w = deriv F (V 0 w) * deriv (V 0) w at hcomp
  have hunit : deriv F (V 0 w) * deriv (V 0) w = 1 := by
    have hid := (hasDerivAt_id w).deriv
    change deriv (fun z : ℂ => z) w = 1 at hid
    rw [hEq.deriv_eq, hid] at hcomp
    exact hcomp.symm
  have hratio := chart_derivative_ratio U H e₁ e₂ A B Γ R Y N ht.bilateral ht.height (V 0 w) hclosed
  have hne : deriv F (V 0 w) ≠ 0 := hratio.1
  have hVd : deriv (V 0) w = 1 / deriv F (V 0 w) := by
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using hunit
  have hT := ((hAa.hasStrictDerivAt.hasDerivAt.comp w hVa.hasStrictDerivAt.hasDerivAt).sub_const
    (Kneser.ActualNormalizationAnchorExpansion.anchorValue U H e₁ e₂ A B Γ M 0)).deriv
  change deriv (transitionValue U H e₁ e₂ A B Γ N M Y V 0) w =
    deriv A₀ (V 0 w) * deriv (V 0) w at hT
  rw [hT, hVd]
  simpa only [A₀, F, div_eq_mul_inv, one_div, one_mul] using hratio.2

/-- The explicit coefficient has exactly the manuscript's physical chain
formula: attracting correction minus the true anchor correction minus
T₀′ times the reflected repelling correction. -/
theorem correction_eq_physical_formula
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :
    transitionCorrection U H e₁ e₂ A B Γ N M Y V w =
      Kneser.ActualBilateralGate.forwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) -
      Kneser.ActualNormalizationAnchorExpansion.anchorCoefficient U H e₁ e₂ A B Γ M -
      deriv (transitionValue U H e₁ e₂ A B Γ N M Y V 0) w *
        Kneser.ActualBilateralGate.backwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) := by
  have hclosed : V 0 w ∈ closedBall (0 : ℂ) 64 := by
    have hn : ‖V 0 w‖ ≤ 16 := by simpa [mem_closedBall, dist_zero_right] using (ht.inverse_zero w hw).1
    simp only [mem_closedBall, dist_zero_right]
    linarith
  rw [transition_derivative_ratio U H e₁ e₂ A B Γ R N M Y V ht w hw,
    transitionCorrection, (chart_derivative_ratio U H e₁ e₂ A B Γ R Y N ht.bilateral ht.height _ hclosed).2]
  dsimp [attractingChartCoefficient, repellingChartCoefficient]
  ring

/-- All Fourier inputs, including integrability on the whole unit gate,
are consequences of the actual constructed transition certificate. -/
theorem exists_fourier_data_of_transition
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    ∃ Vroot p Rp : ℂ → ℂ,
      FourierExpansionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
        (transitionCorrection U H e₁ e₂ A B Γ N M Y V) Vroot p Rp := by
  obtain ⟨C, hC, hUniform⟩ := ht.uniform
  let T := transitionValue U H e₁ e₂ A B Γ N M Y V
  let D := transitionCorrection U H e₁ e₂ A B Γ N M Y V
  obtain ⟨Vroot, p, Rp, hVr, hVr0, hroot, hpa, hp0, hpd, hmult, hRpa, hp2, hlog⟩ :=
    DiscGateFourier.exists_actual_parameter_gate_expansion T D (6 / 5) C
      (by norm_num) (by norm_num) hC ht.transition_zero ht.transition_positive ht.correction_analytic hUniform
  exact ⟨Vroot, p, Rp, hVr, hVr0, hroot, hpa, hp0, hpd, hmult, hRpa, hp2,
    DiscGateFourier.gateFourier_powerExpansion_of_disc T D (6 / 5) C hC
      ht.transition_zero ht.transition_positive ht.correction_analytic hUniform,
    DiscGateFourier.raw_horn_gate_powerExpansion T D (6 / 5) C (by norm_num) (by norm_num) hC
      ht.transition_zero ht.transition_positive ht.correction_analytic hUniform,
    hlog⟩

/-- Unconditional actual one-sided Fourier expansion for every integer
mode. Preparation, dynamics, gate containment, inverse stability and
normalization are constructed, not hypotheses of this final theorem. -/
theorem exists_actual_fourier_expansion :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
            ∃ Vroot p Rp : ℂ → ℂ,
              FourierExpansionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
                (transitionCorrection U H e₁ e₂ A B Γ N M Y V) Vroot p Rp := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht⟩ :=
    exists_actual_deep_abel_transition_data
  obtain ⟨Vroot, p, Rp, hf⟩ := exists_fourier_data_of_transition U H e₁ e₂ A B Γ R N M Y V ht
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht, Vroot, p, Rp, hf⟩

/-- The first-order gate chain is closed for one actual preparation: the
same witnesses provide absolute orbit formulas, actual translation,
periodic correction, and all integer Fourier asymptotics. This endpoint
does not assert global horn identification or Kneser sewing. -/
theorem exists_actual_periodic_fourier_expansion :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
            AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V ∧
            (∀ w ∈ ball (0 : ℂ) 2,
              transitionValue U H e₁ e₂ A B Γ N M Y V 0 (w + 1) =
                transitionValue U H e₁ e₂ A B Γ N M Y V 0 w + 1) ∧
            (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ w ∈ ball (0 : ℂ) 2,
              transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) =
                transitionValue U H e₁ e₂ A B Γ N M Y V s w + 1) ∧
            (∀ w ∈ ball (0 : ℂ) 2,
              transitionCorrection U H e₁ e₂ A B Γ N M Y V (w + 1) =
                transitionCorrection U H e₁ e₂ A B Γ N M Y V w) ∧
            ∃ Vroot p Rp : ℂ → ℂ,
              FourierExpansionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
                (transitionCorrection U H e₁ e₂ A B Γ N M Y V) Vroot p Rp := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht⟩ :=
    exists_actual_deep_abel_transition_data
  obtain ⟨Vroot, p, Rp, hf⟩ := exists_fourier_data_of_transition U H e₁ e₂ A B Γ R N M Y V ht
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht,
    absolute_gate_coefficients_of_deep U H e₁ e₂ A B Γ R N M Y V hd ht,
    (fun w hw => (ActualTransitionPeriodicity.transition_zero_translation
      U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl w hw).1),
    (ActualTransitionPeriodicity.eventually_transition_translation
      U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl).mono
        (fun s hs w hw => (hs w hw).1),
    ActualTransitionPeriodicity.correction_periodic U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl,
    Vroot, p, Rp, hf⟩

end Kneser.ActualFourierExpansion
end
