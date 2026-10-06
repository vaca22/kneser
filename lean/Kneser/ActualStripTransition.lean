import Kneser.ActualFourierExpansion
import Kneser.LocalPeriodicStrip

/-!
The genuine moving transition and correction extend from the constructed
inverse chart to a complete horizontal cylinder strip. The whole-strip
uniform remainder, integer translation, and all actual Fourier coefficients
are proved with the same preparation and normalization witnesses.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualStripTransition

open Filter Set Metric Kneser.ActualQuantitativeGateTransition
open Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.ActualFourierExpansion Kneser.LocalPeriodicStrip
open Kneser.GateFourierDerivative
open scoped Topology

structure StripTransitionData (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) : Prop where
  zero_analytic : AnalyticOnNhd ℂ (lift (T 0)) strip
  positive_analytic : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (lift (T s)) strip
  correction_analytic : AnalyticOnNhd ℂ (periodize D) strip
  uniform : ∃ C ≥ 0, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ strip,
    ‖lift (T s) z - lift (T 0) z - (s : ℂ) * periodize D z‖ ≤ C * s ^ (6 / 5 : ℝ)
  zero_height : ∀ n : ℤ, ∀ Y : ℝ, |Y| < 1 →
    gateFourierCoefficient n Y (lift (T 0)) = gateFourierCoefficient n 0 (T 0)
  positive_height : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ n : ℤ, ∀ Y : ℝ, |Y| < 1 →
    gateFourierCoefficient n Y (lift (T s)) = gateFourierCoefficient n 0 (T s)

theorem strip_data_of_transition
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (hl : LocalAbelData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    StripTransitionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
      (transitionCorrection U H e₁ e₂ A B Γ N M Y V) := by
  let T := transitionValue U H e₁ e₂ A B Γ N M Y V
  let D := transitionCorrection U H e₁ e₂ A B Γ N M Y V
  have hp0 : ∀ z ∈ ball (0 : ℂ) 2, T 0 (z + 1) = T 0 z + 1 :=
    fun z hz => (ActualTransitionPeriodicity.transition_zero_translation
      U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl z hz).1
  have hps : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 2, T s (z + 1) = T s z + 1 :=
    (ActualTransitionPeriodicity.eventually_transition_translation
      U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl).mono fun s hs z hz => (hs z hz).1
  have hpD : ∀ z ∈ ball (0 : ℂ) 2, D (z + 1) = D z :=
    ActualTransitionPeriodicity.correction_periodic U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl
  obtain ⟨C, hC, hU⟩ := ht.uniform
  refine ⟨lift_analytic _ ht.transition_zero hp0, ?_,
    periodize_analytic _ ht.correction_analytic hpD, ⟨C, hC, ?_⟩,
    (fun n y hy => gateFourier_height_eq_zero n _ ht.transition_zero hp0 y hy), ?_⟩
  · filter_upwards [ht.transition_positive, hps] with s ha hp
    exact lift_analytic _ ha hp
  · filter_upwards [hU] with s hs
    intro z hz
    rw [lift_remainder]
    exact hs _ (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4) (reduced_mem_ball z hz))
  · filter_upwards [ht.transition_positive, hps] with s ha hp
    exact fun n y hy => gateFourier_height_eq_zero n _ ha hp y hy

theorem fourier_data_lift (T : ℝ → ℂ → ℂ) (D Vroot p Rp : ℂ → ℂ)
    (hf : FourierExpansionData T D Vroot p Rp) :
    FourierExpansionData (fun s => lift (T s)) (periodize D) Vroot p Rp := by
  refine ⟨hf.root_analytic, hf.root_zero, hf.root_equation, hf.parameter_analytic,
    hf.parameter_zero, hf.parameter_derivative, hf.parameter_multiplier,
    hf.parameter_remainder_analytic, hf.parameter_second_order, ?_, ?_, ?_⟩
  · simpa only [gateFourier_zero_lift_eq, gateCorrection_zero_periodize_eq] using hf.fourier
  · simpa only [gateFourier_zero_lift_eq, gateCorrection_zero_periodize_eq] using hf.raw
  · simpa only [gateFourier_zero_lift_eq, gateCorrection_zero_periodize_eq] using hf.logarithm

/-- An unconditional actual cylinder-strip endpoint. The fixed-width strip
extends across every real coordinate; this is not yet the parameter-growing
strip used in global Kneser sewing. -/
theorem exists_actual_strip_fourier_expansion :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
            AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V ∧
            StripTransitionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
              (transitionCorrection U H e₁ e₂ A B Γ N M Y V) ∧
            ∃ Vroot p Rp : ℂ → ℂ,
              FourierExpansionData
                (fun s => lift (transitionValue U H e₁ e₂ A B Γ N M Y V s))
                (periodize (transitionCorrection U H e₁ e₂ A B Γ N M Y V)) Vroot p Rp := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht⟩ :=
    exists_actual_deep_abel_transition_data
  obtain ⟨Vroot, p, Rp, hf⟩ := exists_fourier_data_of_transition U H e₁ e₂ A B Γ R N M Y V ht
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht,
    absolute_gate_coefficients_of_deep U H e₁ e₂ A B Γ R N M Y V hd ht,
    strip_data_of_transition U H e₁ e₂ A B Γ R N M Y V hd hl ht,
    Vroot, p, Rp, fourier_data_lift _ _ _ _ _ hf⟩

end Kneser.ActualStripTransition
end
