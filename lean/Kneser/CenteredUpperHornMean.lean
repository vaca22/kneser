import Kneser.UpperHornVanishingModes
import Kneser.FourierCenterShift

/-! The mean of an actual centered and anchored chart is its true complex
origin minus the attracting anchor; the canonical upper horn itself has mean zero. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.CenteredUpperHornMean
open Set Metric Complex MeasureTheory
open Kneser.GateFourierDerivative Kneser.LocalPeriodicStrip
open scoped Topology Interval

theorem displacement_int_shift (H : ℂ → ℂ) (hp : ∀ z, H (z+1)=H z+1) (z : ℂ) (k : ℤ) :
    H (z+(k:ℂ))=H z+(k:ℂ) := by
  have hper : Function.Periodic (fun w : ℂ => H w-w) 1 := by
    intro w
    change H (w+1)-(w+1)=H w-w
    rw [hp w]
    ring
  have hh := hper.int_mul k z
  simp only [mul_one] at hh
  change H (z+(k:ℂ))-(z+(k:ℂ))=H z-z at hh
  linear_combination hh

theorem lift_of_centered_eq (T H : ℂ → ℂ) (c a : ℂ)
    (hp : ∀ z, H (z+1)=H z+1)
    (he : ∀ w∈ball (0:ℂ) 2, w∈strip → T w=H (c+w)-a)
    (z : ℂ) (hz : z∈strip) : LocalPeriodicStrip.lift T z=H (c+z)-a := by
  have hh := he (reduced z) (reduced_mem_ball z hz) (by simpa only [strip,Set.mem_setOf_eq,reduced_im] using hz)
  have hint := displacement_int_shift H hp (c+reduced z) (cell z)
  have harg : c+reduced z+(cell z:ℂ)=c+z := by dsimp [reduced]; ring
  rw [harg] at hint
  simp only [LocalPeriodicStrip.lift,hh]
  linear_combination -hint

theorem mean_of_centered_upper (H : ℂ → ℂ) (Ytop : ℝ) (c a : ℂ)
    (ha : AnalyticOnNhd ℂ H {z : ℂ | Ytop<z.im})
    (hp : ∀ z, H (z+1)=H z+1) (hc : Ytop<c.im)
    (hzero : gateFourierCoefficient 0 c.im H=0) :
    gateFourierCoefficient 0 0 (fun w => H (c+w)-a)=c-a := by
  let G : ℝ → ℂ := fun x => H (gatePoint c.im x)-gatePoint c.im x
  have hGc : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hha := (ha (gatePoint c.im x) (by simpa [gatePoint] using hc)).continuousAt
    exact (hha.comp (by unfold gatePoint; fun_prop : ContinuousAt (gatePoint c.im) x)).sub (by unfold gatePoint; fun_prop)
  have hper : Function.Periodic G 1 := by
    intro x
    have he : gatePoint c.im (x+1)=gatePoint c.im x+1 := by simp [gatePoint]; ring
    dsimp only [G]
    rw [he,hp]
    ring
  have hG : IntervalIntegrable G volume 0 1 := hGc.intervalIntegrable _ _
  have hGs : IntervalIntegrable (fun x : ℝ => G (x+c.re)) volume 0 1 :=
    (hGc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hi : (∫ x : ℝ in (0:ℝ)..1, G (x+c.re))=0 := by
    rw [intervalIntegral.integral_comp_add_right]
    have hh := hper.intervalIntegral_add_eq c.re 0
    simp only [zero_add,add_comm 1 c.re] at hh
    simp only [zero_add,add_comm 1 c.re]
    rw [hh]
    simpa only [gateFourierCoefficient,gateWeight,Kneser.fourierFrequency,Int.cast_zero,mul_zero,
      neg_zero,zero_mul,Complex.exp_zero,mul_one,G] using hzero
  have harg (x : ℝ) : c+(x:ℂ)=gatePoint c.im (x+c.re) := by
    apply Complex.ext <;> simp [gatePoint] <;> ring
  have he : gateFourierCoefficient 0 0 (fun w => H (c+w)-a)=
      (∫ x : ℝ in (0:ℝ)..1, G (x+c.re)+(c-a)) := by
    unfold gateFourierCoefficient gateWeight
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [Kneser.fourierFrequency,Int.cast_zero,mul_zero,neg_zero,zero_mul,Complex.exp_zero,mul_one,
      gatePoint,Complex.ofReal_zero,mul_zero,add_zero]
    rw [harg]
    dsimp [G]
    have hh := harg x
    linear_combination -hh
  rw [he,intervalIntegral.integral_add hGs (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c-a) volume 0 1),hi]
  simp

theorem mean_of_lift_eq_centered_upper (T H : ℂ → ℂ) (Ytop : ℝ) (c a : ℂ)
    (ha : AnalyticOnNhd ℂ H {z : ℂ | Ytop<z.im})
    (hp : ∀ z, H (z+1)=H z+1) (hc : Ytop<c.im)
    (hzero : gateFourierCoefficient 0 c.im H=0)
    (he : ∀ w∈strip, LocalPeriodicStrip.lift T w=H (c+w)-a) :
    gateFourierCoefficient 0 0 T=c-a := by
  rw [←gateFourier_zero_lift_eq]
  have hcoef : gateFourierCoefficient 0 0 (LocalPeriodicStrip.lift T)=
      gateFourierCoefficient 0 0 (fun w => H (c+w)-a) := by
    unfold gateFourierCoefficient
    apply intervalIntegral.integral_congr
    intro x _hx
    have hs : gatePoint 0 x∈strip := by simp [strip,gatePoint]
    dsimp only
    rw [he _ hs]
  rw [hcoef]
  exact mean_of_centered_upper H Ytop c a ha hp hc hzero

end Kneser.CenteredUpperHornMean
end
