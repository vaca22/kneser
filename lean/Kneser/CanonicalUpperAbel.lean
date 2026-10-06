import Kneser.CanonicalUpperHornCharts

/-! Genuine Abel gluing of the common upper inverse charts. The physical
forward map is paired with the proved principal reflected inverse, and
regular finite entries supply the global Abel identities. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.CanonicalUpperAbel

open Filter Set Metric Complex Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.ParabolicCoordinateJacobian Kneser.CanonicalBasinExtension Kneser.FatouBasinExtension
open Kneser.CanonicalHighImaginaryAsymptotics Kneser.UpperCanonicalInjectivity
open Kneser.CanonicalUpperHornCharts Kneser.HolomorphicInjectiveInverse
open scoped Topology

theorem extend_abel_of_regular_pair (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (hf : AnalyticAt ℂ f z ∧ deriv f z ≠ 0)
    (hnext : f z ∈ basin f U) : extend f φ U (f z) = extend f φ U z + 1 := by
  obtain ⟨n, hn⟩ := hnext
  have ha : AnalyticAt ℂ (f^[n + 1]) z := by
    rw [Function.iterate_succ]
    exact hn.2.1.comp hf.1
  have hd := (hn.2.1.hasStrictDerivAt.hasDerivAt.comp z hf.1.hasStrictDerivAt.hasDerivAt).deriv
  have he : (f^[n + 1]) = fun w => (f^[n]) (f w) := by
    funext w
    exact Function.iterate_succ_apply f n w
  have hne : deriv (f^[n + 1]) z ≠ 0 := by
    rw [he]
    change deriv (fun w => (f^[n]) (f w)) z = deriv (f^[n]) (f z) * deriv f z at hd
    rw [hd]
    exact mul_ne_zero hn.2.2 hf.2
  have hz : Entry f U z (n + 1) := ⟨by rw [he]; exact hn.1, ha, hne⟩
  rw [extend_eq_transport f φ U hmap habel (f z) n hn,
    extend_eq_transport f φ U hmap habel z (n + 1) hz]
  dsimp only [transport]
  rw [Function.iterate_succ_apply]
  push_cast
  ring

theorem actual_upper_coordinate_abel (R : ℝ) (hs : CanonicalSeedData R) (u : ℂ)
    (hnorm : ‖u‖ ≤ 1 / 32)
    (hba : u ∈ basin parabolicMap (petal R))
    (hbr : -u ∈ basin parabolicInverse (petal R)) :
    globalAttracting R (parabolicMap u) = globalAttracting R u + 1 ∧
      upperRepelling R (parabolicMap u) = upperRepelling R u + 1 := by
  have ha := ((global_attracting_data R hs).2.2.1 u hba).2
  have hmap : ‖parabolicMap u‖ < 1 := by
    have he := Complex.norm_exp_sub_one_le (show ‖u‖ ≤ 1 by linarith)
    change ‖Complex.exp u - 1‖ < 1
    linarith
  have hv : ‖-parabolicMap u‖ < 1 := by simpa only [norm_neg] using hmap
  have hbranch : parabolicInverse (-parabolicMap u) = -u := by
    have hb := ActualGateAbel.reflectedInverse_forward 0 u (by norm_num) hnorm
    simpa only [reflectedInverse_zero, ExponentialUnfolding.unfolding_zero, parabolicMap] using hb
  have hd := RepellingExponentialOrbit.hasDerivAt_parabolicInverse (-parabolicMap u) hv
  have hslit : 1 - (-parabolicMap u) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re]
    have hh := Complex.re_le_norm (-parabolicMap u)
    simp only [Complex.neg_re] at hh
    linarith
  have hreg : AnalyticAt ℂ parabolicInverse (-parabolicMap u) ∧ deriv parabolicInverse (-parabolicMap u) ≠ 0 := by
    refine ⟨((analyticAt_const.sub analyticAt_id).clog hslit).neg, ?_⟩
    rw [hd.deriv]
    exact one_div_ne_zero (slitPlane_ne_zero hslit)
  have hb := extend_abel_of_regular_pair parabolicInverse repellingCoordinate (petal R)
    hs.repelling_map hs.repelling_abel (-parabolicMap u) hreg (by rwa [hbranch])
  rw [hbranch] at hb
  refine ⟨ha, ?_⟩
  dsimp [upperRepelling, globalRepelling, globalReflected]
  rw [hb]
  ring

def physicalStep (z : ℂ) : ℂ := inverseCoordinate (parabolicMap (inverseCoordinate z))

theorem physicalStep_source (Y₁ Yb Y : ℝ) (z : ℂ)
    (hY : max Y₁ (max Yb 128) + 64 < Y)
    (hz : z ∈ closedBall (center Y) 16) :
    z ∈ region 32 Y₁ ∧ physicalStep z ∈ region 32 Y₁ ∧
      Yb < z.im ∧ Yb < (physicalStep z).im ∧ ‖inverseCoordinate z‖ ≤ 1 / 32 := by
  have hn : ‖z - center Y‖ ≤ 16 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - center Y)).trans hn
  have him := (Complex.abs_im_le_norm (z - center Y)).trans hn
  simp only [CanonicalUpperHornCharts.center, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero] at hre
  simp only [CanonicalUpperHornCharts.center, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
    zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at him
  have hY₁ : Y₁ ≤ max Y₁ (max Yb 128) := le_max_left _ _
  have hYb : Yb ≤ max Y₁ (max Yb 128) := (le_max_left _ _).trans (le_max_right _ _)
  have h128 : (128 : ℝ) ≤ max Y₁ (max Yb 128) := (le_max_right _ _).trans (le_max_right _ _)
  have hzi : 128 < z.im := by linarith [(abs_le.mp him).1]
  have hnorm : ‖inverseCoordinate z‖ ≤ 1 / 32 := by
    rw [ParabolicExponentialOrbit.inverseCoordinate_norm]
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (show 0 < z.im by linarith) (Complex.im_le_norm z)
    apply hh.trans
    apply (div_le_iff₀ (by linarith : 0 < z.im)).mpr
    linarith
  have hune : inverseCoordinate z ≠ 0 := by
    intro he
    have hh := inverseCoordinate_involutive z
    rw [he] at hh
    simp only [inverseCoordinate, div_zero] at hh
    rw [← hh] at hzi
    norm_num at hzi
  have hstep := ParabolicExponentialOrbit.inverse_step_error_bound (inverseCoordinate z) (by linarith) hune
  rw [inverseCoordinate_involutive] at hstep
  have herr : ‖physicalStep z - z - 1‖ ≤ 1 / 4 := by
    exact hstep.trans (by nlinarith)
  have hsr := (Complex.abs_re_le_norm (physicalStep z - z - 1)).trans herr
  have hsi := (Complex.abs_im_le_norm (physicalStep z - z - 1)).trans herr
  simp only [Complex.sub_re, Complex.one_re] at hsr
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at hsi
  have hlow := (abs_le.mp hsr).1
  have hupp := (abs_le.mp hsr).2
  have hzim := (abs_le.mp him).1
  have hsim := (abs_le.mp hsi).1
  refine ⟨⟨hre.trans_lt (by norm_num : (16 : ℝ) < 32), by linarith⟩, ⟨?_, by linarith⟩, by linarith, by linarith, hnorm⟩
  apply abs_lt.mpr
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hre
  constructor <;> linarith


theorem high_chart_translation (R Y₁ Yb Y : ℝ) (hs : CanonicalSeedData R)
    (hbasin : ∀ z : ℂ, |z.re| ≤ 64 → Yb < z.im →
      inverseCoordinate z ∈ basin parabolicMap (petal R) ∧
      -inverseCoordinate z ∈ basin parabolicInverse (petal R))
    (hi : InjOn (repellingZeta R) (region 32 Y₁))
    (hY : max Y₁ (max Yb 128) + 64 < Y) (V : ℂ → ℂ)
    (hV : ∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
      imageCenter R Y + w ∈ repellingZeta R '' region 32 Y₁ ∧
      imageInverse (repellingZeta R) (region 32 Y₁) (imageCenter R Y + w) = CanonicalUpperHornCharts.center Y + V w ∧
      hornOnImage R Y₁ (imageCenter R Y + w) = attractingZeta R (CanonicalUpperHornCharts.center Y + V w))
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 2) :
    hornOnImage R Y₁ (imageCenter R Y + (w + 1)) =
      hornOnImage R Y₁ (imageCenter R Y + w) + 1 := by
  have hw4 : w ∈ ball (0 : ℂ) 4 := ball_subset_ball (by norm_num) hw
  let z : ℂ := CanonicalUpperHornCharts.center Y + V w
  obtain ⟨hvw, himage, hInv, hH⟩ := hV w hw4
  have hzc : z ∈ closedBall (CanonicalUpperHornCharts.center Y) 16 := by
    simpa only [z, mem_closedBall, dist_eq_norm, add_sub_cancel_left, dist_zero_right, sub_zero] using hvw
  obtain ⟨hz, hzp, hzYb, hzpYb, hnorm⟩ := physicalStep_source Y₁ Yb Y z hY hzc
  obtain ⟨hba, hbr⟩ := hbasin z (by have hh : |z.re| < 32 := hz.1; linarith) hzYb
  have habel := actual_upper_coordinate_abel R hs (inverseCoordinate z) hnorm hba hbr
  have hstep : inverseCoordinate (physicalStep z) = parabolicMap (inverseCoordinate z) :=
    inverseCoordinate_involutive _
  have hAa : attractingZeta R (physicalStep z) = attractingZeta R z + 1 := by
    simpa only [attractingZeta, hstep] using habel.1
  have hSr : repellingZeta R (physicalStep z) = repellingZeta R z + 1 := by
    simpa only [repellingZeta, hstep] using habel.2
  have hFz := (imageInverse_spec (repellingZeta R) (region 32 Y₁) (imageCenter R Y + w) himage).2
  rw [hInv] at hFz
  change repellingZeta R z = imageCenter R Y + w at hFz
  have hFstep : repellingZeta R (physicalStep z) = imageCenter R Y + (w + 1) := by
    rw [hSr, hFz]
    ring
  have hleft := imageInverse_left (repellingZeta R) (region 32 Y₁) hi (physicalStep z) hzp
  rw [hFstep] at hleft
  change attractingZeta R (imageInverse (repellingZeta R) (region 32 Y₁) (imageCenter R Y + (w + 1))) = _
  rw [hleft, hAa]
  rw [hH]

/-- All actual high charts have genuine translation, share one inverse and
one horn on its open image, and have a common vanishing displacement bound. -/
theorem exists_actual_high_periodic_horn_charts (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₁ Y₀ C : ℝ, 0 < Y₁ ∧ Y₁ + 32 ≤ Y₀ ∧ 0 ≤ C ∧
      IsOpen (repellingZeta R '' region 32 Y₁) ∧
      InjOn (repellingZeta R) (region 32 Y₁) ∧
      AnalyticOnNhd ℂ (hornOnImage R Y₁) (repellingZeta R '' region 32 Y₁) ∧
      ∀ Y : ℝ, Y₀ < Y → ∃ V : ℂ → ℂ,
        AnalyticOnNhd ℂ V (ball (0 : ℂ) 4) ∧
        AnalyticOnNhd ℂ (fun w => hornOnImage R Y₁ (imageCenter R Y + w)) (ball (0 : ℂ) 4) ∧
        (∀ w ∈ ball (0 : ℂ) 2, hornOnImage R Y₁ (imageCenter R Y + (w + 1)) =
          hornOnImage R Y₁ (imageCenter R Y + w) + 1) ∧
        (∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
          imageCenter R Y + w ∈ repellingZeta R '' region 32 Y₁ ∧
          imageInverse (repellingZeta R) (region 32 Y₁) (imageCenter R Y + w) = CanonicalUpperHornCharts.center Y + V w ∧
          hornOnImage R Y₁ (imageCenter R Y + w) = attractingZeta R (CanonicalUpperHornCharts.center Y + V w) ∧
          ‖hornOnImage R Y₁ (imageCenter R Y + w) - (imageCenter R Y + w)‖ ≤ C / (Y - 16)) := by
  obtain ⟨Y₁, Yc, C, hY₁, hYc, hC, hopen, hi, _hleft, hhorn, hcharts⟩ := exists_actual_high_horn_charts R hs
  obtain ⟨Yb, _hYb, hbasin⟩ := exists_high_basin R hs
  let Y₀ : ℝ := max Yc (max Y₁ (max Yb 128) + 64)
  have hY₀ : Y₁ + 32 ≤ Y₀ := hYc.trans (le_max_left _ _)
  refine ⟨Y₁, Y₀, C, hY₁, hY₀, hC, hopen, hi, hhorn, ?_⟩
  intro Y hY
  obtain ⟨V, hVa, hTa, hV⟩ := hcharts Y ((le_max_left _ _).trans_lt hY)
  refine ⟨V, hVa, hTa, ?_, hV⟩
  intro w hw
  apply high_chart_translation R Y₁ Yb Y hs hbasin hi ((le_max_right _ _).trans_lt hY) V
    (fun w hw => ?_) w hw
  obtain ⟨hv, himage, hinv, hH, _⟩ := hV w hw
  exact ⟨hv, himage, hinv, hH⟩

end Kneser.CanonicalUpperAbel
end
