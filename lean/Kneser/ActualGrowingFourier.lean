import Kneser.ActualGrowingPeriodicity
import Kneser.GrowingStripFourier

/-! The actual growing transition has a convergent Fourier series and
full multiplier-height exponential decay, derived from genuine bilateral
dynamics, the true holomorphic inverse, and exact Abel identities. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualGrowingFourier

open Filter Set Metric Complex Kneser.GrowingBandGeometry
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualGrowingCoordinateInverse
open Kneser.ActualGrowingTransition Kneser.ActualGrowingPeriodicity
open Kneser.GrowingStripFourier Kneser.GateFourierDerivative
open Kneser.GrowingLensSpatialHolomorphy Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

def center (θ : ℝ) : ℂ := (height θ / 2 : ℝ) * I

def centeredTransition (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ : ℂ) (V : ℂ → ℂ) (z : ℂ) : ℂ :=
  transition A B Γ s a b θ e₁ e₂ V (z+center θ)-center θ

def outerWidth (θ Y P : ℝ) : ℝ := height θ / 2 - (3 * Y + boundaryMargin P)
def decayWidth (θ Y P : ℝ) : ℝ := outerWidth θ Y P - 1

theorem centered_mem_growing_strip (θ Y P : ℝ) (z : ℂ)
    (hz : z ∈ symmetricStrip (outerWidth θ Y P)) :
    z+center θ ∈ strip θ (3 * Y + boundaryMargin P) := by
  have hh := abs_lt.mp (show |z.im| < outerWidth θ Y P from hz)
  change 3 * Y + boundaryMargin P < (z+center θ).im ∧
    (z+center θ).im < height θ - (3 * Y + boundaryMargin P)
  simp only [center,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  dsimp [outerWidth] at hh
  exact ⟨by linarith only [hh.1],by linarith only [hh.2]⟩

theorem actual_centered_fourier
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3 * Y + boundaryMargin P)))
    (hVs : ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
      V w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) = w) :
    0 < decayWidth θ Y P ∧
    (∀ n : ℤ, ‖gateFourierCoefficient n 0 (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V)‖ ≤
      2 * Real.exp (-2 * Real.pi * decayWidth θ Y P * |(n:ℝ)|)) ∧
    ∀ z : ℂ, |z.im| < decayWidth θ Y P →
      HasSum (fun n : ℤ => gateFourierCoefficient n 0
        (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V) *
          exp (Kneser.fourierFrequency n*z))
        (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V z-z) := by
  have hh : 8 * Y ≤ height θ := by
    dsimp [height]
    apply (le_div_iff₀ hc.theta_pos).mpr
    nlinarith only [hc.strong_width]
  have hB : boundaryMargin P + 2 < Y := by dsimp [boundaryMargin]; linarith only [hc.phase_margin_buffer]
  have hD : 2 < outerWidth θ Y P := by
    dsimp [outerWidth]
    linarith only [hh,hB]
  have hd : 0 < decayWidth θ Y P := by dsimp [decayWidth]; linarith only [hD]
  have hdd : decayWidth θ Y P < outerWidth θ Y P := by dsimp [decayWidth]; linarith
  have hprops := actual_transition_properties e₁ e₂ A B Γ s a b θ Y η M P hc V hV hVs
  have ha : AnalyticOnNhd ℂ (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V)
      (symmetricStrip (outerWidth θ Y P)) := by
    intro z hz
    have hg := (hprops.1 (z+center θ) (centered_mem_growing_strip θ Y P z hz)).comp
      (f := fun w => w+center θ) (analyticAt_id.add analyticAt_const)
    exact hg.sub analyticAt_const
  have hp : ∀ z ∈ symmetricStrip (outerWidth θ Y P),
      centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V (z+1) =
        centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V z+1 := by
    intro z hz
    have hh := actual_transition_translation e₁ e₂ A B Γ s a b θ Y η M P hs1 hc V hVs
      (z+center θ) (centered_mem_growing_strip θ Y P z hz)
    dsimp [centeredTransition]
    rw [show z+1+center θ=z+center θ+1 by ring,hh]
    ring
  have hb : ∀ z ∈ symmetricStrip (outerWidth θ Y P),
      ‖centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V z-z‖ ≤ 2 := by
    intro z hz
    have hh := (hprops.2.2.2 (z+center θ) (centered_mem_growing_strip θ Y P z hz)).1
    convert hh using 1
    congr 1
    dsimp [centeredTransition]
    ring
  exact ⟨hd,actual_integral_decay_and_reconstruction _ (outerWidth θ Y P) (decayWidth θ Y P) 2 hd hdd
    (by norm_num) ha hp hb⟩

/-- All analytic, dynamic, univalence, periodicity, and coefficient-decay
premises are derived for the same actual preparation and its real roots. -/
theorem exists_actual_growing_fourier_representation
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ, ∃ V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ V (strip θ (3 * Y + boundaryMargin P)) ∧
        (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
          V w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
        0<decayWidth θ Y P ∧
        (∀ n : ℤ, ‖gateFourierCoefficient n 0 (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V)‖≤
          2*Real.exp (-2*Real.pi*decayWidth θ Y P*|(n:ℝ)|)) ∧
        ∀ z : ℂ, |z.im|<decayWidth θ Y P → HasSum (fun n : ℤ =>
          gateFourierCoefficient n 0 (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V)*
            exp (Kneser.fourierFrequency n*z))
          (centeredTransition A B Γ s a b θ (e₁ s) (e₂ s) V z-z) := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  obtain ⟨_Vp,V,_hVp,hV,_hspecp,hspec⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  exact ⟨a,b,θ,V,hc,hV,hspec,actual_centered_fourier e₁ e₂ A B Γ s a b θ Y η M P
    (hss.trans_le hs₀h |>.trans (by norm_num)) hc V hV hspec⟩

end Kneser.ActualGrowingFourier
end
