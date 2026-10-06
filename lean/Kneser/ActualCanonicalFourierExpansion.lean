import Kneser.CanonicalBasinExtension
import Kneser.ActualStripTransition

/-!
The unconditional integer-mode expansion is attached to the actual global
parabolic basin coordinates and the manuscript's real anchor. All finite
chart choices are constructed from the same preparation, with a proved
fixed-center shift in the repelling coordinate.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualCanonicalFourierExpansion

open Filter Set Metric Kneser.ReflectedOrbitChainCoefficient
open Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualFourierExpansion
open Kneser.ActualStripTransition Kneser.CanonicalBasinExtension
open Kneser.LocalPeriodicStrip
open scoped Topology

theorem exists_actual_canonical_strip_fourier_expansion :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧ CanonicalSeedData R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
            AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V ∧
            StripTransitionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
              (transitionCorrection U H e₁ e₂ A B Γ N M Y V) ∧
            (∀ w ∈ ball (0 : ℂ) 4,
              transitionValue U H e₁ e₂ A B Γ N M Y V 0 w =
                globalAttracting R (chartPoint Y (V 0 w)) -
                  globalAttracting R RealNormalizationAnchor.normalizationAnchor ∧
              globalRepelling R (chartPoint Y (V 0 w)) =
                FullCanonicalImageGate.canonicalGateInZeta N (chartCenter Y) + w) ∧
            ∃ Vroot p Rp : ℂ → ℂ,
              FourierExpansionData (fun s => lift (transitionValue U H e₁ e₂ A B Γ N M Y V s))
                (periodize (transitionCorrection U H e₁ e₂ A B Γ N M Y V)) Vroot p Rp := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R₀, hd₀, hl₀⟩ := exists_actual_deep_abel_data
  let R := R₀ + 2
  have hs : CanonicalSeedData R := canonical_seed_of_deep U H e₁ e₂ A B Γ R₀ hd₀ hl₀
  have hd : DeepCoordinateData U H e₁ e₂ A B Γ R := hd₀.mono (by dsimp [R]; linarith)
  have hl : LocalAbelData U H e₁ e₂ A B Γ R := hl₀.mono (by dsimp [R]; linarith)
  obtain ⟨N, M, Y, V, ht⟩ := exists_transition_data_of_deep U H e₁ e₂ A B Γ R hd
  obtain ⟨Vroot, p, Rp, hf⟩ := exists_fourier_data_of_transition U H e₁ e₂ A B Γ R N M Y V ht
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, hs, N, M, Y, V, ht,
    absolute_gate_coefficients_of_deep U H e₁ e₂ A B Γ R N M Y V hd ht,
    strip_data_of_transition U H e₁ e₂ A B Γ R N M Y V hd hl ht,
    transition_zero_eq_global U H e₁ e₂ A B Γ R R N M Y V hs le_rfl hd ht,
    Vroot, p, Rp, fourier_data_lift _ _ _ _ _ hf⟩

end Kneser.ActualCanonicalFourierExpansion
end
