import Kneser.ActualAllOrderUpperHornBaseline

/-! Integral Fourier coefficients of the same actual zero-parameter gate
are coefficients of the true canonical global upper horn. The exact
centering and attracting-anchor factors are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.ActualUpperHornCoefficientIdentification
open Set Metric Complex MeasureTheory
open Kneser.LocalPeriodicStrip Kneser.GateFourierDerivative Kneser.GateFourierHeight
open Kneser.FourierCenterShift Kneser.ActualAllOrderUpperHornBaseline
open Kneser.CanonicalUpperHornCharts Kneser.CanonicalBasinExtension
open scoped Topology Interval

theorem coefficient_sub_const_nonzero (n : ℤ) (hn : n≠0) (G : ℂ → ℂ) (a : ℂ) (Y : ℝ)
    (hc : Continuous (fun x : ℝ => G (gatePoint Y x))) :
    gateFourierCoefficient n Y (fun z => G z-a)=gateFourierCoefficient n Y G := by
  have hweight : Continuous (gateWeight n Y) := by unfold gateWeight gatePoint; fun_prop
  have hg : IntervalIntegrable (fun x : ℝ => (G (gatePoint Y x)-gatePoint Y x)*gateWeight n Y x)
      volume 0 1 := (hc.sub (by unfold gatePoint; fun_prop)).mul hweight |>.intervalIntegrable _ _
  have hw : IntervalIntegrable (fun x : ℝ => a*gateWeight n Y x) volume 0 1 :=
    (continuous_const.mul hweight).intervalIntegrable _ _
  have hi : (∫ x : ℝ in (0:ℝ)..1, gateWeight n Y x)=0 := by
    have he (x : ℝ) : gateWeight n Y x =
        exp (-Kneser.fourierFrequency n*(I*(Y:ℂ)))*exp (-Kneser.fourierFrequency n*(x:ℂ)) := by
      unfold gateWeight gatePoint
      rw [show -Kneser.fourierFrequency n*((x:ℂ)+I*(Y:ℂ))=
        -Kneser.fourierFrequency n*(I*(Y:ℂ)) + -Kneser.fourierFrequency n*(x:ℂ) by ring, exp_add]
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, integral_weight]
    simp [hn]
  unfold gateFourierCoefficient
  have he (x : ℝ) : (G (gatePoint Y x)-a-gatePoint Y x)*gateWeight n Y x=
      (G (gatePoint Y x)-gatePoint Y x)*gateWeight n Y x-a*gateWeight n Y x := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hg hw, intervalIntegral.integral_const_mul, hi]
  simp

/-- A genuine identity on the full fixed strip identifies every nonzero
mode with the actual global-horn integral at the shifted height. -/
theorem nonzero_coefficient_of_global_identity
    (n : ℤ) (hn : n≠0) (T G : ℂ → ℂ) (c a : ℂ)
    (ha : AnalyticOnNhd ℂ (lift T) strip)
    (he : ∀ w∈strip, lift T w=G (c+w)-a) :
    gateFourierCoefficient n 0 T=
      exp (Kneser.fourierFrequency n*c)*gateFourierCoefficient n c.im G := by
  have hc : Continuous (fun x : ℝ => lift T (x:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ha (x:ℂ) (by simp [strip])).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hpoint (x : ℝ) : gatePoint c.im x-c=((x-c.re:ℝ):ℂ) := by
    apply Complex.ext <;> simp [gatePoint]
  have hcG : Continuous (fun x : ℝ => G (gatePoint c.im x)) := by
    have heq : (fun x : ℝ => G (gatePoint c.im x))=
        (fun x : ℝ => lift T ((x-c.re:ℝ):ℂ)+a) := by
      funext x
      have hh := he ((x-c.re:ℝ):ℂ) (by simp [strip])
      have harg : c+((x-c.re:ℝ):ℂ)=gatePoint c.im x := by
        apply Complex.ext <;> simp [gatePoint] <;> ring
      rw [harg] at hh
      linear_combination -hh
    rw [heq]
    exact (hc.comp (continuous_id.sub continuous_const)).add continuous_const
  have hcoef : gateFourierCoefficient n c.im (centered (lift T) c)=gateFourierCoefficient n c.im G := by
    rw [←coefficient_sub_const_nonzero n hn G a c.im hcG]
    unfold gateFourierCoefficient
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [centered]
    have hh := he (gatePoint c.im x-c) (by rw [hpoint]; simp [strip])
    rw [show c+(gatePoint c.im x-c)=gatePoint c.im x by ring] at hh
    rw [hh]
  rw [coefficient_center_shift n (lift T) c (lift_translation T) hc] at hcoef
  simp only [hn, ↓reduceIte, sub_zero, gateFourier_zero_lift_eq] at hcoef
  have hx : exp (Kneser.fourierFrequency n*c)*exp (-Kneser.fourierFrequency n*c)=1 := by
    rw [←exp_add]
    simp
  calc
    gateFourierCoefficient n 0 T =
        exp (Kneser.fourierFrequency n*c)*(exp (-Kneser.fourierFrequency n*c)*gateFourierCoefficient n 0 T) := by rw [←mul_assoc,hx,one_mul]
    _ = _ := by rw [hcoef]

/-- Subtracting the actual zero mode cancels the arbitrary repelling
center exactly. Only the true attracting normalization anchor remains. -/
theorem normalized_coefficient_of_global_identity
    (n : ℤ) (hn : n≠0) (T G : ℂ → ℂ) (c a : ℂ)
    (ha : AnalyticOnNhd ℂ (lift T) strip)
    (he : ∀ w∈strip, lift T w=G (c+w)-a)
    (hm : gateFourierCoefficient 0 0 T=c-a) :
    gateFourierCoefficient n 0 T*exp (-Kneser.fourierFrequency n*gateFourierCoefficient 0 0 T)=
      gateFourierCoefficient n c.im G*exp (Kneser.fourierFrequency n*a) := by
  rw [nonzero_coefficient_of_global_identity n hn T G c a ha he,hm]
  rw [mul_comm (exp (Kneser.fourierFrequency n*c)) (gateFourierCoefficient n c.im G)]
  rw [mul_assoc,←exp_add]
  congr 2
  ring

/-- The same all-order gate coefficient, with its actual normalization,
is a coefficient of the actual canonical global upper horn. -/
theorem actual_baseline_nonzero_coefficient
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch : ℝ) (N M M₀ : ℕ) (Y : ℝ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ)
    (hb : BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Y Vold V p r G)
    (n : ℤ) (hn : n≠0) :
    gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Y V 0)*
      exp (-Kneser.fourierFrequency n*gateFourierCoefficient 0 0 (actualTransition U H A B e Γ N M Y V 0))=
    gateFourierCoefficient n (imageCenter Rₛ Y).im G*
      exp (Kneser.fourierFrequency n*globalAttracting Rₛ Kneser.RealNormalizationAnchor.normalizationAnchor) :=
  normalized_coefficient_of_global_identity n hn _ G _ _ hb.baseline_analytic hb.actual_baseline hb.baseline_mean

end Kneser.ActualUpperHornCoefficientIdentification
end
