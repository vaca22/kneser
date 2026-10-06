import Kneser.QuantitativeHornExpansion
import Kneser.ExponentialMultiplierSecondOrder

/-!
Fourier extraction from a constructed common image disc. Spatial
holomorphy derives the real gate integrability, and eventual positive
parameter holomorphy suffices; there is no assumption for remote parameters.
-/

noncomputable section
namespace Kneser.DiscGateFourier

open Set Metric Filter MeasureTheory Kneser.GateFourierDerivative
open Kneser.QuantitativeHornExpansion
open scoped Topology

theorem real_gate_mem_disc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    gatePoint 0 x ∈ ball (0 : ℂ) 4 := by
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero, mem_ball,
    dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
  linarith [hx.2]

theorem intervalIntegrable_of_disc_analytic (n : ℤ) (f : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ f (ball (0 : ℂ) 4)) :
    IntervalIntegrable (fun x => f (gatePoint 0 x) * gateWeight n 0 x) volume 0 1 := by
  have hf : ContinuousOn (fun x : ℝ => f (gatePoint 0 x)) (Icc (0 : ℝ) 1) := by
    intro x hx
    have hg : ContinuousAt (fun y : ℝ => gatePoint 0 y) x := by
      simpa only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero] using
        Complex.continuous_ofReal.continuousAt
    exact ((ha _ (real_gate_mem_disc x hx)).continuousAt.comp hg).continuousWithinAt
  have hw : Continuous (fun x : ℝ => gateWeight n 0 x) := by
    simpa only [gateWeight, gatePoint, Complex.ofReal_zero, mul_zero, add_zero,
      Pi.mul_apply] using
      (continuous_const.mul Complex.continuous_ofReal).cexp
  exact (hf.mul hw.continuousOn).intervalIntegrable_of_Icc (by norm_num)

/-- Actual uniform disc remainders give all integer Fourier coefficients
and their quantitative first corrections on the genuine horizontal gate. -/
theorem gateFourier_powerExpansion_of_disc (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (q C : ℝ) (hC : 0 ≤ C)
    (hT0 : AnalyticOnNhd ℂ (T 0) (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4))
    (hD : AnalyticOnNhd ℂ D (ball (0 : ℂ) 4))
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 4,
      ‖T s z - T 0 z - (s : ℂ) * D z‖ ≤ C * s ^ q) :
    ∀ n : ℤ, PowerExpansion (fun s => gateFourierCoefficient n 0 (T s))
      (gateCorrectionCoefficient n 0 D) q := by
  intro n
  have hInt0 := intervalIntegrable_of_disc_analytic n (fun z => T 0 z - z)
    (fun z hz => (hT0 z hz).sub analyticAt_id)
  have hIntD := intervalIntegrable_of_disc_analytic n D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hT, hUniform] with s hs hsu
  have hInts := intervalIntegrable_of_disc_analytic n (fun z => T s z - z)
    (fun z hz => (hs z hz).sub analyticAt_id)
  rw [coefficient_remainder_eq_integral n 0 s T D hInts hInt0 hIntD]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C * s ^ q)
    (f := fun x => (T s (gatePoint 0 x) - T 0 (gatePoint 0 x) -
      (s : ℂ) * D (gatePoint 0 x)) * gateWeight n 0 x) (by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
      rw [norm_mul, norm_gateWeight]
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact hsu _ (real_gate_mem_disc x hx'))
  simpa using h

/-- Logarithmic normalization is a consequence of the actual gate integral
expansions. Only the naturally necessary nonvanishing of the selected
unperturbed Fourier coefficient remains a condition. -/
theorem log_normalized_gate_powerExpansion (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (q C : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hT0 : AnalyticOnNhd ℂ (T 0) (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4))
    (hD : AnalyticOnNhd ℂ D (ball (0 : ℂ) 4))
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 4,
      ‖T s z - T 0 z - (s : ℂ) * D z‖ ≤ C * s ^ q)
    (n : ℤ) (hB : gateFourierCoefficient n 0 (T 0) ≠ 0) :
    PowerExpansion (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
      (fun t => gateFourierCoefficient n 0 (T t))
      (fun t => gateFourierCoefficient 0 0 (T t)) s))
      (2 * Kneser.hornKappa n (gateFourierCoefficient n 0 (T 0))
        (gateCorrectionCoefficient n 0 D) (gateCorrectionCoefficient 0 0 D)) q := by
  have hp := gateFourier_powerExpansion_of_disc T D q C hC hT0 hT hD hUniform
  exact (horn_powerExpansions n (fun t => gateFourierCoefficient n 0 (T t))
    (fun t => gateFourierCoefficient 0 0 (T t)) (gateFourierCoefficient n 0 (T 0))
    (-gateFourierCoefficient 0 0 (T 0)) (gateCorrectionCoefficient n 0 D)
    (gateCorrectionCoefficient 0 0 D) q hq hq2 rfl (by simp) hB (hp n) (hp 0)).2


/-- Exponential normalization retains the explicit correction for every
integer mode, even when its unperturbed coefficient vanishes. -/
theorem raw_horn_gate_powerExpansion (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (q C : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hT0 : AnalyticOnNhd ℂ (T 0) (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4))
    (hD : AnalyticOnNhd ℂ D (ball (0 : ℂ) 4))
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 4,
      ‖T s z - T 0 z - (s : ℂ) * D z‖ ≤ C * s ^ q) :
    ∀ n : ℤ, PowerExpansion (Kneser.realHornCoefficient n
      (fun t => gateFourierCoefficient n 0 (T t))
      (fun t => gateFourierCoefficient 0 0 (T t)))
      (Complex.exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 (T 0)) *
        (gateCorrectionCoefficient n 0 D - Kneser.fourierFrequency n *
          gateFourierCoefficient n 0 (T 0) * gateCorrectionCoefficient 0 0 D)) q := by
  have hp := gateFourier_powerExpansion_of_disc T D q C hC hT0 hT hD hUniform
  intro n
  simpa only [mul_neg, neg_mul] using raw_horn_powerExpansion n
    (fun t => gateFourierCoefficient n 0 (T t)) (fun t => gateFourierCoefficient 0 0 (T t))
    (gateFourierCoefficient n 0 (T 0)) (-gateFourierCoefficient 0 0 (T 0))
    (gateCorrectionCoefficient n 0 D) (gateCorrectionCoefficient 0 0 D) q hq hq2
    rfl (by simp) (hp n) (hp 0)

/-- The actual multiplier parameter, including its genuine quadratic
coefficient, is shared by every nonvanishing mode's logarithmic expansion. -/
theorem exists_actual_parameter_gate_expansion (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (q C : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hT0 : AnalyticOnNhd ℂ (T 0) (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4))
    (hD : AnalyticOnNhd ℂ D (ball (0 : ℂ) 4))
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 4,
      ‖T s z - T 0 z - (s : ℂ) * D z‖ ≤ C * s ^ q) :
    ∃ V p R : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, Kneser.ExponentialCuspParameter.cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      AnalyticAt ℂ R 0 ∧ (∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * R s) ∧
      ∀ n : ℤ, gateFourierCoefficient n 0 (T 0) ≠ 0 →
        ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖Complex.log (Kneser.realNormalizedHornCoefficient n
            (fun t => gateFourierCoefficient n 0 (T t))
            (fun t => gateFourierCoefficient 0 0 (T t)) s) -
            Kneser.hornKappa n (gateFourierCoefficient n 0 (T 0))
              (gateCorrectionCoefficient n 0 D) (gateCorrectionCoefficient 0 0 D) * p (s : ℂ)‖ ≤
            Cp * ‖p (s : ℂ)‖ ^ q := by
  obtain ⟨V, p, R, hVa, hV0, hsquare, hpa, hp0, hpd, hproduct, hRa, hR⟩ :=
    Kneser.ExponentialMultiplierSecondOrder.exists_actual_multiplier_second_order
  refine ⟨V, p, R, hVa, hV0, hsquare, hpa, hp0, hpd, hproduct, hRa, hR, ?_⟩
  intro n hB
  have he := log_normalized_gate_powerExpansion T D q C hq hq2 hC hT0 hT hD hUniform n hB
  have hzero : Complex.log (Kneser.realNormalizedHornCoefficient n
      (fun t => gateFourierCoefficient n 0 (T t))
      (fun t => gateFourierCoefficient 0 0 (T t)) 0) = 0 := by
    rw [Kneser.realNormalizedHornCoefficient_zero n
      (fun t => gateFourierCoefficient n 0 (T t)) (fun t => gateFourierCoefficient 0 0 (T t))
      (gateFourierCoefficient n 0 (T 0)) (-gateFourierCoefficient 0 0 (T 0))
      rfl (by simp) hB, Complex.log_one]
  exact log_remainder_in_actual_parameter _ _ q hq hq2 hzero he p hpa hp0 hpd

end Kneser.DiscGateFourier
end
