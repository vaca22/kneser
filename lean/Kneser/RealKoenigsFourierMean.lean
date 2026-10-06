import Kneser.ActualKoenigsUpperBranch
import Kneser.GateFourierDerivative

/-! The actual Fourier mean has exact imaginary phase whenever the true
normalized Koenigs time is composed with a real interval chart. This
module proves the integral bridge; identifying the global repelling
inverse with that real chart is a separate dynamical assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.RealKoenigsFourierMean
open Set MeasureTheory Metric
open Kneser.GateFourierDerivative Kneser.ActualKoenigsUpperBranch
open Kneser.ReflectedOrbitChainCoefficient Kneser.ExponentialUnfolding
open Kneser.PositiveKoenigsOrbit
open scoped Topology Interval

theorem mean_im_of_real_phase (T : ℂ → ℂ) (h : ℝ)
    (hcontinuous : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1))
    (hphase : ∀ x : ℝ, x∈Icc 0 1 → (T (x:ℂ)).im=h) :
    (gateFourierCoefficient 0 0 T).im=h := by
  have hc : ContinuousOn (fun x : ℝ => T (x:ℂ)-(x:ℂ)) (Icc 0 1) :=
    hcontinuous.sub Complex.continuous_ofReal.continuousOn
  have hi : IntervalIntegrable (fun x : ℝ => T (x:ℂ)-(x:ℂ)) volume 0 1 :=
    (show ContinuousOn (fun x : ℝ => T (x:ℂ)-(x:ℂ)) (uIcc 0 1) from by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hc).intervalIntegrable
  have he : gateFourierCoefficient 0 0 T=∫ x : ℝ in (0:ℝ)..1, T (x:ℂ)-(x:ℂ) := by
    simp only [gateFourierCoefficient,gateWeight,Kneser.fourierFrequency,Int.cast_zero,mul_zero,
      neg_zero,zero_mul,Complex.exp_zero,mul_one,gatePoint,Complex.ofReal_zero,mul_zero,add_zero]
  rw [he]
  change Complex.imCLM (∫ x : ℝ in (0:ℝ)..1, T (x:ℂ)-(x:ℂ))=h
  rw [←Complex.imCLM.intervalIntegral_comp_comm hi]
  have ht : (∫ x : ℝ in (0:ℝ)..1, Complex.imCLM (T (x:ℂ)-(x:ℂ)))=
      ∫ x : ℝ in (0:ℝ)..1, h := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    simpa only [Complex.imCLM_apply,Complex.sub_im,Complex.ofReal_im,sub_zero] using hphase x hx'
  rw [ht]
  simp

/-- The chart premise refers to a real function with its actual range
between the genuine roots. The Koenigs phase is derived from the actual
preparation and dynamics, rather than supplied as a mean hypothesis. -/
theorem exists_actual_real_chart_koenigs_mean
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        a<0 ∧ 0<b ∧ 0<θ ∧ unfolding s a=(a:ℂ) ∧ unfolding s b=(b:ℂ) ∧
        θ=-Real.log (multiplier s a) ∧ θ*Y≤Real.pi/2 ∧
        ∀ r₀ : ℝ, r₀<a → ∀ S : ℝ → ℝ,
          ContinuousOn S (Icc 0 1) → (∀ x∈Icc (0:ℝ) 1, a<S x ∧ S x<b) →
          (gateFourierCoefficient 0 0 (fun w : ℂ => upperTime s a r₀ (S w.re:ℂ))).im=Real.pi/θ := by
  obtain ⟨Y,s₀,hY,hs₀,hs₀h,hphase⟩ := exists_actual_analytic_upper_real_phase U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,ha,hb,hθ,hfa,hfb,hθeq,hθY,hreal⟩ := hphase s hs hss
  refine ⟨a,b,θ,ha,hb,hθ,hfa,hfb,hθeq,hθY,?_⟩
  intro r₀ hr₀ S hS hRange
  apply mean_im_of_real_phase
  · intro x hx
    have hi := hRange x hx
    have hc : ContinuousAt (upperTime s a r₀) (S x:ℂ) :=
      (hreal (S x) r₀ hi.1 hi.2 hr₀).1.continuousAt
    have hSc : ContinuousWithinAt (fun t : ℝ => (S t:ℂ)) (Icc 0 1) x :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hS x hx)
    change ContinuousWithinAt (fun t : ℝ => upperTime s a r₀ (S t:ℂ)) (Icc 0 1) x
    exact hc.comp_continuousWithinAt (f := fun t : ℝ => (S t:ℂ)) hSc
  · intro x hx
    have hi := hRange x hx
    simpa only [Complex.ofReal_re] using (hreal (S x) r₀ hi.1 hi.2 hr₀).2.1

end Kneser.RealKoenigsFourierMean
end
