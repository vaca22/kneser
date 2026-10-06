import Kneser.ActualCanonicalFourierExpansion
import Kneser.LocalStripFourierDecay

/-!
The same genuinely constructed transition has an absolutely convergent
Fourier representation throughout the interior strip. Its coefficients are
the actual gate integrals from the first-order theorem, with exponential
decay proved from the actual analytic gate, both at zero and for small
positive parameters.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualStripFourierRepresentation

open Filter Set Metric Kneser.ReflectedOrbitChainCoefficient
open Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualFourierExpansion
open Kneser.ActualStripTransition Kneser.CanonicalBasinExtension
open Kneser.LocalPeriodicStrip Kneser.GateFourierDerivative
open scoped Topology

def Representation (T : ℂ → ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧
    (∀ n : ℤ, ‖gateFourierCoefficient n 0 T‖ ≤ M * Real.exp (-Real.pi * |(n : ℝ)|)) ∧
    ∀ z : ℂ, |z.im| < 1 / 2 →
      HasSum (fun n : ℤ => gateFourierCoefficient n 0 T *
        Complex.exp (Kneser.fourierFrequency n * z)) (lift T z - z)

structure RepresentationData (T : ℝ → ℂ → ℂ) : Prop where
  zero : Representation (T 0)
  positive : ∀ᶠ s : ℝ in 𝓝[>] 0, Representation (T s)

theorem representation_data_of_transition
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (hl : LocalAbelData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    RepresentationData (transitionValue U H e₁ e₂ A B Γ N M Y V) := by
  have hp0 := fun z hz => (ActualTransitionPeriodicity.transition_zero_translation
    U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl z hz).1
  refine ⟨LocalStripFourierDecay.exists_actual_germ_fourier_representation _ ht.transition_zero hp0, ?_⟩
  filter_upwards [ht.transition_positive,
    ActualTransitionPeriodicity.eventually_transition_translation
      U H e₁ e₂ A B Γ R Y N M V ht hd.depth hl] with s ha hp
  exact LocalStripFourierDecay.exists_actual_germ_fourier_representation _ ha
    (fun z hz => (hp z hz).1)

theorem exists_actual_canonical_fourier_representation :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧ CanonicalSeedData R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
            AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V ∧
            StripTransitionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
              (transitionCorrection U H e₁ e₂ A B Γ N M Y V) ∧
            RepresentationData (transitionValue U H e₁ e₂ A B Γ N M Y V) ∧
            (∀ w ∈ ball (0 : ℂ) 4,
              transitionValue U H e₁ e₂ A B Γ N M Y V 0 w =
                globalAttracting R (chartPoint Y (V 0 w)) -
                  globalAttracting R RealNormalizationAnchor.normalizationAnchor ∧
              globalRepelling R (chartPoint Y (V 0 w)) =
                FullCanonicalImageGate.canonicalGateInZeta N (chartCenter Y) + w) ∧
            ∃ Vroot p Rp : ℂ → ℂ,
              FourierExpansionData (fun s => lift (transitionValue U H e₁ e₂ A B Γ N M Y V s))
                (periodize (transitionCorrection U H e₁ e₂ A B Γ N M Y V)) Vroot p Rp := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, hs,
    N, M, Y, V, ht, habs, hstrip, hglobal, Vroot, p, Rp, hf⟩ :=
    ActualCanonicalFourierExpansion.exists_actual_canonical_strip_fourier_expansion
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, hs,
    N, M, Y, V, ht, habs, hstrip,
    representation_data_of_transition U H e₁ e₂ A B Γ R N M Y V hd hl ht,
    hglobal, Vroot, p, Rp, hf⟩

end Kneser.ActualStripFourierRepresentation
end
