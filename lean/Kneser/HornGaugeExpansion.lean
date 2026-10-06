import Kneser.ActualStripFourierRepresentation
import Kneser.FourierCenterShift

/-!
The actual quantitative horn expansion is unchanged by any parameter-
dependent complex origin of the repelling coordinate. No regularity of
that origin is required: exact integral gauge invariance comes first.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.HornGaugeExpansion

open Filter Set Complex Kneser.GateFourierDerivative Kneser.FourierCenterShift
open Kneser.LocalPeriodicStrip Kneser.ActualStripTransition Kneser.ActualFourierExpansion
open scoped Topology

def gaugeCoefficient (T : ℝ → ℂ → ℂ) (c : ℝ → ℂ) (n : ℤ) (s : ℝ) : ℂ :=
  gateFourierCoefficient n (c s).im (centered (T s) (c s))

theorem gauge_horn_eq (T : ℝ → ℂ → ℂ) (c : ℝ → ℂ) (n : ℤ) (hn : n ≠ 0) (s : ℝ)
    (hp : ∀ z, T s (z + 1) = T s z + 1)
    (hc : Continuous (fun x : ℝ => T s (x : ℂ))) :
    Kneser.realHornCoefficient n (gaugeCoefficient T c n) (gaugeCoefficient T c 0) s =
      Kneser.realHornCoefficient n (fun t => gateFourierCoefficient n 0 (T t))
        (fun t => gateFourierCoefficient 0 0 (T t)) s :=
  horn_gauge_invariant n hn (T s) (c s) hp hc

theorem strip_continuous_real (T : ℂ → ℂ) (ha : AnalyticOnNhd ℂ T strip) :
    Continuous (fun x : ℝ => T (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : (x : ℂ) ∈ strip := by simp [strip]
  exact (ha _ hx).continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem normalized_gauge_eq_of_strip (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (hd : StripTransitionData T D) (c : ℝ → ℂ) (n : ℤ) (hn : n ≠ 0) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      Kneser.realNormalizedHornCoefficient n
        (gaugeCoefficient (fun t => lift (T t)) c n)
        (gaugeCoefficient (fun t => lift (T t)) c 0) s =
      Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n 0 (lift (T t)))
        (fun t => gateFourierCoefficient 0 0 (lift (T t))) s := by
  have hzero := gauge_horn_eq (fun t => lift (T t)) c n hn 0
    (lift_translation (T 0)) (strip_continuous_real _ hd.zero_analytic)
  filter_upwards [hd.positive_analytic] with s hs
  have hpos := gauge_horn_eq (fun t => lift (T t)) c n hn s
    (lift_translation (T s)) (strip_continuous_real _ hs)
  exact congrArg₂ (fun a b : ℂ => a / b) hpos hzero

theorem gauge_logarithm_of_strip (T : ℝ → ℂ → ℂ) (D Vroot p Rp : ℂ → ℂ)
    (hd : StripTransitionData T D)
    (hf : FourierExpansionData (fun s => lift (T s)) D Vroot p Rp)
    (c : ℝ → ℂ) (n : ℤ) (hn : n ≠ 0)
    (hB : gateFourierCoefficient n 0 (lift (T 0)) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖Complex.log (Kneser.realNormalizedHornCoefficient n
          (gaugeCoefficient (fun t => lift (T t)) c n)
          (gaugeCoefficient (fun t => lift (T t)) c 0) s) -
        Kneser.hornKappa n (gateFourierCoefficient n 0 (lift (T 0)))
          (gateCorrectionCoefficient n 0 D) (gateCorrectionCoefficient 0 0 D) * p (s : ℂ)‖ ≤
        C * ‖p (s : ℂ)‖ ^ (6 / 5 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := hf.logarithm n hB
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, normalized_gauge_eq_of_strip T D hd c n hn] with s hs he
  rwa [he]

end Kneser.HornGaugeExpansion
end
