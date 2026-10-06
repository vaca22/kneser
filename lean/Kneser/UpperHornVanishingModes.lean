import Kneser.LocalStripFourierDecay
import Kneser.ActualGlobalUpperHorn

/-! Upper-infinity normalization kills the actual constant and negative
Fourier modes on the one globally continued upper horn. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.UpperHornVanishingModes
open Filter Set Metric Complex
open Kneser.GateFourierDerivative Kneser.GateFourierHeight Kneser.LocalStripFourierDecay
open Kneser.ActualGlobalUpperHorn Kneser.CanonicalBasinExtension
open Kneser.PeriodicHornGlobal Kneser.CanonicalUpperHornCharts
open scoped Topology

theorem height_independent_upper (T : ℂ → ℂ) (Ytop Y Z : ℝ)
    (ha : AnalyticOnNhd ℂ T {z : ℂ | Ytop<z.im})
    (hp : ∀ z : ℂ, T (z+1)=T z+1) (hY : Ytop<Y) (hZ : Ytop<Z) (n : ℤ) :
    gateFourierCoefficient n Y T=gateFourierCoefficient n Z T := by
  apply gateFourier_height_independent n T Y Z hp
  intro z hz
  have hi := (Complex.mem_reProdIm.mp hz).2
  have hsub : uIcc Y Z ⊆ Ioi Ytop := ordConnected_Ioi.uIcc_subset hY hZ
  exact (ha z (hsub hi)).differentiableAt.differentiableWithinAt

theorem nonpositive_coefficient_zero (T : ℂ → ℂ) (Ytop D C : ℝ)
    (hYtop : 0≤Ytop) (hD : D<Ytop) (hC : 0≤C)
    (ha : AnalyticOnNhd ℂ T {z : ℂ | Ytop<z.im})
    (hp : ∀ z : ℂ, T (z+1)=T z+1)
    (hbound : ∀ z : ℂ, Ytop<z.im → ‖T z-z‖≤C/(z.im-D))
    (n : ℤ) (hn : n≤0) (Yref : ℝ) (hYref : Ytop<Yref) :
    gateFourierCoefficient n Yref T=0 := by
  by_contra hne
  let d : ℝ := ‖gateFourierCoefficient n Yref T‖
  have hd : 0<d := norm_pos_iff.mpr hne
  let Y : ℝ := max Ytop Yref+C/d+1
  have hY : Ytop<Y := by dsimp [Y]; have hh := div_nonneg hC hd.le; linarith [le_max_left Ytop Yref]
  have hpos : 0≤Y := (hYtop.trans hY.le)
  have hYd : 0<Y-D := by linarith
  have hb := gate_coefficient_bound n T Y (C/(Y-D)) (by
    intro x _hx
    simpa only [gatePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] using hbound (gatePoint Y x) (by
      simpa only [gatePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] using hY))
  rw [height_independent_upper T Ytop Y Yref ha hp hY hYref n] at hb
  have hnreal : (n:ℝ)≤0 := by exact_mod_cast hn
  have hexp : Real.exp (2*Real.pi*(n:ℝ)*Y)≤1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnreal) hpos
  have hb' : d≤C/(Y-D) := hb.trans (mul_le_of_le_one_right (div_nonneg hC hYd.le) hexp)
  have hc : C<d*(Y-D) := by
    have he : d*(C/d)=C := mul_div_cancel₀ C (ne_of_gt hd)
    dsimp [Y]
    nlinarith [le_max_left Ytop Yref]
  have hc' := (le_div_iff₀ hYd).mp hb'
  linarith

theorem exists_actual_upper_horn_vanishing_modes (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₁ Y₀ M C : ℝ, ∃ H : ℂ → ℂ,
      H=globalHorn (hornOnImage R Y₁) (imageCenter R) Y₀ ∧
      17≤Y₀ ∧ 0≤M ∧ 0≤C ∧
      AnalyticOnNhd ℂ H {z : ℂ | Y₀+M+2<z.im} ∧
      (∀ z : ℂ, H (z+1)=H z+1) ∧
      (∀ Y : ℝ, Y₀<Y → ∀ w∈ball (0:ℂ) 1,
        imageCenter R Y+w∈Kneser.UpperCanonicalInjectivity.repellingZeta R '' Kneser.UpperCanonicalInjectivity.region 32 Y₁ ∧
        H (imageCenter R Y+w)=hornOnImage R Y₁ (imageCenter R Y+w)) ∧
      (∀ z : ℂ, Y₀+M+18<z.im → ‖H z-z‖≤C/(z.im-M-17)) ∧
      (∀ n : ℤ, n≤0 → ∀ Y : ℝ, Y₀+M+18<Y → gateFourierCoefficient n Y H=0) := by
  obtain ⟨Y₁,Y₀,M,C,H,hdef,hY₀,hM,hC,_hi,_hpchart,ha,hp,_hpatch,hactual,hbound⟩ := exists_actual_global_upper_horn R hs
  refine ⟨Y₁,Y₀,M,C,H,hdef,hY₀,hM,hC,ha,hp,hactual,hbound,?_⟩
  intro n hn Y hY
  apply nonpositive_coefficient_zero H (Y₀+M+18) (M+17) C (by linarith) (by linarith) hC
    (ha.mono (by intro z hz; change Y₀+M+2<z.im; change Y₀+M+18<z.im at hz; linarith)) hp
  · intro z hz
    have he : z.im-(M+17)=z.im-M-17 := by ring
    rw [he]
    exact hbound z hz
  · exact hn
  · exact hY

end Kneser.UpperHornVanishingModes
end
