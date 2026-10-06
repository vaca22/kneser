import Kneser.UpperCanonicalInjectivity

/-! Every sufficiently high upper horn chart uses one and the same actual
holomorphic inverse. The resulting transition is A composed with that
inverse, and its displacement tends uniformly to zero on each image chart. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.CanonicalUpperHornCharts

open Filter Set Metric Complex Kneser.ParabolicExponentialOrbit
open Kneser.ParabolicCoordinateJacobian Kneser.CanonicalBasinExtension
open Kneser.CanonicalHighImaginaryAsymptotics Kneser.UpperCanonicalInjectivity
open Kneser.HolomorphicInjectiveInverse
open scoped Topology

def center (Y : ℝ) : ℂ := I * (Y : ℂ)

def imageCenter (R Y : ℝ) : ℂ := repellingZeta R (center Y)

def hornOnImage (R Y₁ : ℝ) (z : ℂ) : ℂ :=
  attractingZeta R (imageInverse (repellingZeta R) (region 32 Y₁) z)

theorem analyticOnNhd_hornOnImage (R Y₁ : ℝ)
    (ha : AnalyticOnNhd ℂ (attractingZeta R) (region 32 Y₁))
    (hinv : AnalyticOnNhd ℂ (imageInverse (repellingZeta R) (region 32 Y₁))
      (repellingZeta R '' region 32 Y₁)) :
    AnalyticOnNhd ℂ (hornOnImage R Y₁) (repellingZeta R '' region 32 Y₁) := by
  intro z hz
  have hv := (imageInverse_spec (repellingZeta R) (region 32 Y₁) z hz).1
  exact (ha _ hv).comp (hinv z hz)

theorem exists_image_chart (R Y₁ Y : ℝ)
    (ha : AnalyticOnNhd ℂ (repellingZeta R) (region 32 Y₁))
    (hd : ∀ z ∈ region 32 Y₁, ‖deriv (repellingZeta R) z - 1‖ ≤ 1 / 4)
    (hi : InjOn (repellingZeta R) (region 32 Y₁))
    (hY : Y₁ + 32 ≤ Y) :
    ∃ V : ℂ → ℂ, AnalyticOnNhd ℂ V (ball (0 : ℂ) 4) ∧
      ∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
        center Y + V w ∈ region 32 Y₁ ∧
        repellingZeta R (center Y + V w) = imageCenter R Y + w ∧
        imageInverse (repellingZeta R) (region 32 Y₁) (imageCenter R Y + w) = center Y + V w := by
  let F : ℂ → ℂ := fun z => repellingZeta R (center Y + z) - imageCenter R Y
  have hsource : ∀ z ∈ ball (0 : ℂ) 32, center Y + z ∈ region 32 Y₁ := by
    intro z hz
    have hn : ‖z‖ < 32 := by simpa only [mem_ball, dist_zero_right] using hz
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    have hlo := (abs_le.mp him).1
    constructor
    · simpa only [center, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, zero_add] using hre.trans_lt hn
    · simp only [center, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
        zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      linarith
  have hFa : AnalyticOnNhd ℂ F (ball (0 : ℂ) 32) := by
    intro z hz
    exact ((ha _ (hsource z hz)).comp
      (f := fun w : ℂ => center Y + w) (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hFd : ∀ z ∈ ball (0 : ℂ) 32, ‖deriv F z - 1‖ ≤ 1 / 4 := by
    intro z hz
    have hh := ha _ (hsource z hz)
    have he := ((hh.hasStrictDerivAt.hasDerivAt.comp z ((hasDerivAt_id z).const_add (center Y))).sub_const
      (imageCenter R Y)).deriv
    change deriv F z = deriv (repellingZeta R) (center Y + z) * 1 at he
    rw [he, mul_one]
    exact hd _ (hsource z hz)
  have happ := FullCanonicalImageGate.approximation_of_deriv_bound F hFa hFd
  have happ' : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * 16)) (1 / 2) := by
    intro z hz w hw
    have he := happ z (by norm_num at hz ⊢; exact hz) w (by norm_num at hw ⊢; exact hw)
    norm_num at he ⊢
    exact he.trans (by nlinarith [norm_nonneg (z - w)])
  obtain ⟨V, hv, hva, _hvlip⟩ := StableHolomorphicInverse.exists_holomorphic_inverse_on_disc F 16
    (by norm_num) happ' (by norm_num at hFa ⊢; exact hFa) (by simp [F, imageCenter]; norm_num)
  refine ⟨V, by norm_num at hva ⊢; exact hva, ?_⟩
  intro w hw
  obtain ⟨hvw, he⟩ := hv w (by norm_num at hw ⊢; exact hw)
  have hVsmall : V w ∈ ball (0 : ℂ) 32 := by
    have hn : ‖V w‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hvw
    change dist (V w) 0 < 32
    rw [dist_zero_right]
    linarith
  have hs := hsource (V w) hVsmall
  have hEq : repellingZeta R (center Y + V w) = imageCenter R Y + w := by
    change repellingZeta R (center Y + V w) - imageCenter R Y = w at he
    calc
      _ = w + imageCenter R Y := sub_eq_iff_eq_add.mp he
      _ = imageCenter R Y + w := add_comm _ _
  have hInv := imageInverse_left (repellingZeta R) (region 32 Y₁) hi (center Y + V w) hs
  rw [hEq] at hInv
  exact ⟨hvw, hs, hEq, hInv⟩

/-- The same global transition supplies all large-height image charts.
Inverse uniqueness proves exact overlap consistency on the whole image. -/
theorem exists_actual_high_horn_charts (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₁ Y₀ C : ℝ, 0 < Y₁ ∧ Y₁ + 32 ≤ Y₀ ∧ 0 ≤ C ∧
      IsOpen (repellingZeta R '' region 32 Y₁) ∧
      InjOn (repellingZeta R) (region 32 Y₁) ∧
      (∀ z ∈ region 32 Y₁, imageInverse (repellingZeta R) (region 32 Y₁) (repellingZeta R z) = z) ∧
      AnalyticOnNhd ℂ (hornOnImage R Y₁) (repellingZeta R '' region 32 Y₁) ∧
      ∀ Y : ℝ, Y₀ < Y → ∃ V : ℂ → ℂ,
        AnalyticOnNhd ℂ V (ball (0 : ℂ) 4) ∧
        AnalyticOnNhd ℂ (fun w => hornOnImage R Y₁ (imageCenter R Y + w)) (ball (0 : ℂ) 4) ∧
        (∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
          imageCenter R Y + w ∈ repellingZeta R '' region 32 Y₁ ∧
          imageInverse (repellingZeta R) (region 32 Y₁) (imageCenter R Y + w) = center Y + V w ∧
          hornOnImage R Y₁ (imageCenter R Y + w) = attractingZeta R (center Y + V w) ∧
          ‖hornOnImage R Y₁ (imageCenter R Y + w) - (imageCenter R Y + w)‖ ≤ C / (Y - 16)) := by
  obtain ⟨Y₁, hY₁, ha, hr, hd, hi, hopen, hinv, hleft⟩ := exists_high_univalent_inverse R hs
  obtain ⟨Ye, C, hYe, hC, herr⟩ := exists_upper_normalized_difference_bound R hs
  let Y₀ : ℝ := max (Y₁ + 32) (Ye + 32)
  have hY₀ : Y₁ + 32 ≤ Y₀ := le_max_left _ _
  have hYeY₀ : Ye + 32 ≤ Y₀ := le_max_right _ _
  have hhorn := analyticOnNhd_hornOnImage R Y₁ ha hinv
  refine ⟨Y₁, Y₀, C, hY₁, hY₀, hC, hopen, hi, hleft, hhorn, ?_⟩
  intro Y hY
  obtain ⟨V, hVa, hv⟩ := exists_image_chart R Y₁ Y hr hd hi (hY₀.trans hY.le)
  have hsource : ∀ w ∈ ball (0 : ℂ) 4, imageCenter R Y + w ∈ repellingZeta R '' region 32 Y₁ := by
    intro w hw
    exact ⟨center Y + V w, (hv w hw).2.1, (hv w hw).2.2.1⟩
  have hTa : AnalyticOnNhd ℂ (fun w => hornOnImage R Y₁ (imageCenter R Y + w)) (ball (0 : ℂ) 4) := by
    intro w hw
    exact (hhorn _ (hsource w hw)).comp (analyticAt_const.add analyticAt_id)
  refine ⟨V, hVa, hTa, ?_⟩
  intro w hw
  obtain ⟨hvw, hzw, hFeq, hInv⟩ := hv w hw
  have hH : hornOnImage R Y₁ (imageCenter R Y + w) = attractingZeta R (center Y + V w) := by
    dsimp only [hornOnImage]
    rw [hInv]
  have hnorm : ‖V w‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hvw
  have hre := (Complex.abs_re_le_norm (V w)).trans hnorm
  have him := (Complex.abs_im_le_norm (V w)).trans hnorm
  have hzi : Y - 16 ≤ (center Y + V w).im := by
    simp only [center, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
      zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
    linarith [(abs_le.mp him).1]
  have hheight : Ye < (center Y + V w).im := by linarith
  have hpos : 0 < (center Y + V w).im := hYe.trans hheight
  have hbound := herr (inverseCoordinate (center Y + V w)) (by
    rw [inverseCoordinate_involutive]
    simpa only [center, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, zero_add] using hre.trans (by norm_num : (16 : ℝ) ≤ 64))
    (inverseCoordinate_upper _ hpos) (by simpa only [inverseCoordinate_involutive, abs_of_pos hpos] using hheight)
  refine ⟨hvw, hsource w hw, hInv, hH, ?_⟩
  rw [hH, ← hFeq]
  have hb : ‖attractingZeta R (center Y + V w) - repellingZeta R (center Y + V w)‖ ≤
      C / (center Y + V w).im := by
    simpa only [attractingZeta, repellingZeta, inverseCoordinate_involutive, abs_of_pos hpos] using hbound
  exact hb.trans (div_le_div_of_nonneg_left hC (by linarith) hzi)

end Kneser.CanonicalUpperHornCharts
end
