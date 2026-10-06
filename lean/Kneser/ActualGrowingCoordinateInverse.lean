import Kneser.ActualHolomorphicGrowingLens
import Kneser.HorizontalStripInverse

/-! Actual prepared growing coordinates are univalent and cover the full
multiplier-height strip up to an additive boundary margin. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualGrowingCoordinateInverse

open Filter Set Metric Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.GrowingLensCoordinateRegularity
open Kneser.ActualHolomorphicGrowingLens Kneser.HorizontalStripInverse
open Kneser.ExponentialUnfolding Kneser.ReflectedOrbitChainCoefficient
open scoped Topology NNReal

def boundaryMargin (P : ℝ) : ℝ := Real.pi + 2 * P + 1

theorem actual_coordinate_phase_bounds
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (Z : ℂ) (hZ : Z ∈ strip θ Y) :
    |(attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z - Z).im| ≤ boundaryMargin P ∧
    |(repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z - Z).im| ≤ boundaryMargin P := by
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hu : ‖bandChart a b θ Z‖ ≤ 1 := by
    have hh := ((hc.true_orbits Z hZ).2.2.2.2.1 0).2.2.1
    simp only [orbit_zero] at hh
    linarith only [hh,hc.radius_small]
  have hm := Kneser.ActualLensBounds.lensModel_phase_bound s a b θ P (e₁ s) (e₂ s)
    (bandChart a b θ Z) hc.residue_bound hP hc.first_model_bound hc.second_model_bound hu
  have ht := bandTime_bandChart a b θ Y Z (lt_trans hc.left_neg hc.right_pos)
    hc.theta_pos (by linarith [hc.height_large]) (hc.width.trans (by linarith [Real.pi_pos])) hZ
  rw [ht] at hm
  have hsum := actual_series_norm_le_one e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ
  constructor
  · have hi := (Complex.abs_im_le_norm (forwardSeries A B Γ s a b θ Z)).trans hsum.1
    have hh := abs_add_le
      (lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) - Z).im
      (forwardSeries A B Γ s a b θ Z).im
    change |((lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) +
      forwardSeries A B Γ s a b θ Z) - Z).im| ≤ boundaryMargin P
    rw [show lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) + forwardSeries A B Γ s a b θ Z - Z =
      (lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) - Z) + forwardSeries A B Γ s a b θ Z by ring]
    rw [Complex.add_im]
    simp only [Complex.sub_im] at hm hh
    dsimp [boundaryMargin]
    linarith only [hh,hm,hi]
  · have hi := (Complex.abs_im_le_norm (inverseSeries A B Γ s a b θ Z)).trans hsum.2
    have hh := abs_add_le
      (lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) - Z).im
      (-(inverseSeries A B Γ s a b θ Z).im)
    rw [abs_neg,←sub_eq_add_neg] at hh
    change |((lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) -
      inverseSeries A B Γ s a b θ Z) - Z).im| ≤ boundaryMargin P
    rw [show lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) - inverseSeries A B Γ s a b θ Z - Z =
      (lensModel s a b θ (e₁ s) (e₂ s) (bandChart a b θ Z) - Z) - inverseSeries A B Γ s a b θ Z by ring]
    rw [Complex.sub_im]
    simp only [Complex.sub_im] at hm hh
    dsimp [boundaryMargin]
    linarith only [hh,hm,hi]

theorem actual_coordinate_derivative_bounds
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (Z : ℂ) (hZ : Z ∈ strip θ (2 * Y)) :
    ‖deriv (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) Z - 1‖ < 1 / 4 ∧
    ‖deriv (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) Z - 1‖ < 1 / 4 := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hZ₀ := inner_strip_subset θ Y hY.le hZ
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hYθ : θ * Y ≤ Real.pi := hc.width.trans (by linarith [Real.pi_pos])
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hmodel := analyticOnNhd_chartModel s a b θ Y (e₁ s) (e₂ s) hab hc.theta_pos hY hYθ
  have hforward := actual_forwardSeries_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  have hinverse := actual_inverseSeries_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  have hmodelbound := norm_chartModel_deriv_sub_one_le s a b θ Y η P (e₁ s) (e₂ s) Z hab hc.theta_pos
    hY hYθ hc.radius_pos.le (by linarith [hc.radius_small]) hP hc.residue_bound hc.first_model_bound hc.second_model_bound
    (fun W hW => by simpa only [orbit_zero] using ((hc.true_orbits W hW).2.2.2.2.1 0).2.2.1) hZ
  have hfb := norm_deriv_le_on_buffered_strip (forwardSeries A B Γ s a b θ) θ Y 1 hY hforward
    (fun W hW => (actual_series_norm_le_one e₁ e₂ A B Γ s a b θ Y η M P hc W hW).1) Z hZ
  have hgb := norm_deriv_le_on_buffered_strip (inverseSeries A B Γ s a b θ) θ Y 1 hY hinverse
    (fun W hW => (actual_series_norm_le_one e₁ e₂ A B Γ s a b θ Y η M P hc W hW).2) Z hZ
  have hratio : (Real.pi + P * η + 2) / Y < 1 / 4 :=
    (div_lt_iff₀ hY).mpr (by linarith only [hc.height_margin])
  have heqF : attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) =ᶠ[𝓝 Z]
      (fun W => chartModel s a b θ (e₁ s) (e₂ s) W + forwardSeries A B Γ s a b θ W) := by
    filter_upwards [(strip_isOpen θ Y).mem_nhds hZ₀] with W hW
    rw [attractingCoordinate,chartModel_eq_lensModel s a b θ Y (e₁ s) (e₂ s) W hab hc.theta_pos hY hYθ hW]
  have heqG : repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) =ᶠ[𝓝 Z]
      (fun W => chartModel s a b θ (e₁ s) (e₂ s) W - inverseSeries A B Γ s a b θ W) := by
    filter_upwards [(strip_isOpen θ Y).mem_nhds hZ₀] with W hW
    rw [repellingCoordinate,chartModel_eq_lensModel s a b θ Y (e₁ s) (e₂ s) W hab hc.theta_pos hY hYθ hW]
  constructor
  · rw [heqF.deriv_eq]
    have hh := ((hmodel Z hZ₀).differentiableAt.hasDerivAt.add (hforward Z hZ₀).differentiableAt.hasDerivAt).deriv
    change deriv (fun W => chartModel s a b θ (e₁ s) (e₂ s) W + forwardSeries A B Γ s a b θ W) Z = _ at hh
    rw [hh]
    rw [show deriv (chartModel s a b θ (e₁ s) (e₂ s)) Z + deriv (forwardSeries A B Γ s a b θ) Z - 1 =
      (deriv (chartModel s a b θ (e₁ s) (e₂ s)) Z - 1) + deriv (forwardSeries A B Γ s a b θ) Z by ring]
    apply lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add hmodelbound hfb))
    convert hratio using 1 <;> first | rfl | ring
  · rw [heqG.deriv_eq]
    have hh := ((hmodel Z hZ₀).differentiableAt.hasDerivAt.sub (hinverse Z hZ₀).differentiableAt.hasDerivAt).deriv
    change deriv (fun W => chartModel s a b θ (e₁ s) (e₂ s) W - inverseSeries A B Γ s a b θ W) Z = _ at hh
    rw [hh]
    rw [show deriv (chartModel s a b θ (e₁ s) (e₂ s)) Z - deriv (inverseSeries A B Γ s a b θ) Z - 1 =
      (deriv (chartModel s a b θ (e₁ s) (e₂ s)) Z - 1) - deriv (inverseSeries A B Γ s a b θ) Z by ring]
    apply lt_of_le_of_lt ((norm_sub_le _ _).trans (add_le_add hmodelbound hgb))
    convert hratio using 1 <;> first | rfl | ring

theorem closedStrip_convex (a b : ℝ) : Convex ℝ (closedStrip a b) :=
  (convex_Icc a b).linear_preimage Complex.imCLM.toLinearMap

theorem lipschitz_displacement_of_derivative
    (F : ℂ → ℂ) (a b : ℝ) (ha : AnalyticOnNhd ℂ F (closedStrip a b))
    (hd : ∀ Z ∈ closedStrip a b, ‖deriv F Z - 1‖ ≤ 1 / 4) :
    LipschitzOnWith (⟨1 / 4, by norm_num⟩ : ℝ≥0) (fun Z => F Z - Z) (closedStrip a b) := by
  have hda : ∀ Z ∈ closedStrip a b, DifferentiableAt ℂ (fun W => F W - W) Z :=
    fun Z hZ => (ha Z hZ).differentiableAt.sub differentiableAt_id
  have hdb : ∀ Z ∈ closedStrip a b, ‖deriv (fun W => F W - W) Z‖ ≤ 1 / 4 := by
    intro Z hZ
    have he := ((ha Z hZ).differentiableAt.hasDerivAt.sub (hasDerivAt_id Z)).deriv
    change deriv (fun W => F W - W) Z = deriv F Z - 1 at he
    rw [he]
    exact hd Z hZ
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (F x - x) (F y - y) ≤ (1 / 4 : ℝ) * dist x y
  simpa only [dist_eq_norm] using
    (closedStrip_convex a b).norm_image_sub_le_of_norm_deriv_le hda hdb hy hx

theorem derivative_ne_zero_of_close_to_one {z : ℂ} (h : ‖z - 1‖ < 1 / 4) : z ≠ 0 := by
  intro he
  rw [he,zero_sub,norm_neg,norm_one] at h
  norm_num at h

/-- Both actual coordinates have a true single-valued holomorphic inverse
on a growing strip whose height suffers only a fixed additive loss. -/
theorem actual_bilateral_holomorphic_strip_inverses
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    ∃ Vplus Vminus : ℂ → ℂ,
      AnalyticOnNhd ℂ Vplus (strip θ (3 * Y + boundaryMargin P)) ∧
      AnalyticOnNhd ℂ Vminus (strip θ (3 * Y + boundaryMargin P)) ∧
      (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
        Vplus w ∈ strip θ (3 * Y) ∧ attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (Vplus w) = w) ∧
      (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
        Vminus w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (Vminus w) = w) := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hB : 0 ≤ boundaryMargin P := by dsimp [boundaryMargin]; positivity
  have hsub : closedStrip (3 * Y) (height θ - 3 * Y) ⊆ strip θ (2 * Y) := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have houter := hsub.trans (inner_strip_subset θ Y hY.le)
  have ha := actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  have hf : AnalyticOnNhd ℂ (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s))
      (closedStrip (3 * Y) (height θ - 3 * Y)) := ha.1.mono houter
  have hg : AnalyticOnNhd ℂ (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s))
      (closedStrip (3 * Y) (height θ - 3 * Y)) := ha.2.mono houter
  have hdF := fun Z hZ => (actual_coordinate_derivative_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z (hsub hZ)).1
  have hdG := fun Z hZ => (actual_coordinate_derivative_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z (hsub hZ)).2
  have hopsub : openStrip (3 * Y) (height θ - 3 * Y) ⊆ closedStrip (3 * Y) (height θ - 3 * Y) :=
    fun _ hZ => ⟨hZ.1.le,hZ.2.le⟩
  obtain ⟨Vplus,hVplus,hspecplus⟩ := exists_holomorphic_strip_inverse _ (3 * Y) (height θ - 3 * Y)
    (boundaryMargin P) (⟨1 / 4,by norm_num⟩ : ℝ≥0) (by change (1 / 4 : ℝ) < 1; norm_num) hB
    (lipschitz_displacement_of_derivative _ _ _ hf (fun Z hZ => (hdF Z hZ).le))
    (fun Z hZ => (actual_coordinate_phase_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z (houter hZ)).1)
    (hf.mono hopsub) (fun Z hZ => derivative_ne_zero_of_close_to_one (hdF Z (hopsub hZ)))
  obtain ⟨Vminus,hVminus,hspecminus⟩ := exists_holomorphic_strip_inverse _ (3 * Y) (height θ - 3 * Y)
    (boundaryMargin P) (⟨1 / 4,by norm_num⟩ : ℝ≥0) (by change (1 / 4 : ℝ) < 1; norm_num) hB
    (lipschitz_displacement_of_derivative _ _ _ hg (fun Z hZ => (hdG Z hZ).le))
    (fun Z hZ => (actual_coordinate_phase_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z (houter hZ)).2)
    (hg.mono hopsub) (fun Z hZ => derivative_ne_zero_of_close_to_one (hdG Z (hopsub hZ)))
  have heq : openStrip (3 * Y + boundaryMargin P) (height θ - 3 * Y - boundaryMargin P) =
      strip θ (3 * Y + boundaryMargin P) := by ext Z; simp only [openStrip,strip,sub_add_eq_sub_sub]
  have hsource : openStrip (3 * Y) (height θ - 3 * Y) = strip θ (3 * Y) := rfl
  rw [heq] at hVplus hVminus hspecplus hspecminus
  rw [hsource] at hspecplus hspecminus
  exact ⟨Vplus,Vminus,hVplus,hVminus,hspecplus,hspecminus⟩


theorem actual_coordinates_injective_buffered
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    InjOn (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ (2 * Y)) ∧
    InjOn (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ (2 * Y)) := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hconv : Convex ℝ (strip θ (2 * Y)) :=
    (convex_Ioo (2 * Y) (height θ - 2 * Y)).linear_preimage Complex.imCLM.toLinearMap
  have ha := actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  have hgeneric : ∀ F : ℂ → ℂ, AnalyticOnNhd ℂ F (strip θ Y) →
      (∀ Z ∈ strip θ (2 * Y), ‖deriv F Z - 1‖ < 1 / 4) → InjOn F (strip θ (2 * Y)) := by
    intro F hF hd x hx y hy heq
    have hda : ∀ Z ∈ strip θ (2 * Y), DifferentiableAt ℂ (fun W => F W - W) Z :=
      fun Z hZ => (hF Z (inner_strip_subset θ Y hY.le hZ)).differentiableAt.sub differentiableAt_id
    have hdb : ∀ Z ∈ strip θ (2 * Y), ‖deriv (fun W => F W - W) Z‖ ≤ 1 / 4 := by
      intro Z hZ
      have hh := ((hF Z (inner_strip_subset θ Y hY.le hZ)).differentiableAt.hasDerivAt.sub (hasDerivAt_id Z)).deriv
      change deriv (fun W => F W - W) Z = deriv F Z - 1 at hh
      rw [hh]
      exact (hd Z hZ).le
    have hh := hconv.norm_image_sub_le_of_norm_deriv_le hda hdb hy hx
    have hval : (F x - x) - (F y - y) = -(x-y) := by rw [heq]; ring
    rw [hval,norm_neg] at hh
    have hn : ‖x-y‖ = 0 := by nlinarith only [hh,norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨hgeneric _ ha.1 (fun Z hZ => (actual_coordinate_derivative_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ).1),
    hgeneric _ ha.2 (fun Z hZ => (actual_coordinate_derivative_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ).2)⟩

theorem actual_midline_in_inverse_domain
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (x : ℝ) :
    (x : ℂ) + (height θ / 2 : ℝ) * Complex.I ∈ strip θ (3 * Y + boundaryMargin P) := by
  have hh : 8 * Y ≤ height θ := by
    dsimp [height]
    apply (le_div_iff₀ hc.theta_pos).mpr
    nlinarith only [hc.strong_width]
  have hB : boundaryMargin P < Y := hc.phase_margin
  simp only [strip,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_im,Complex.ofReal_re,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
  exact ⟨by linarith only [hh,hB],by linarith only [hh,hB]⟩

/-- Same actual preparation yields both genuine growing-strip inverses
and a nonempty target containing the entire real-midline image level. -/
theorem exists_actual_bilateral_growing_inverses
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b θ : ℝ, ∃ Vplus Vminus : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ Vplus (strip θ (3 * Y + boundaryMargin P)) ∧
        AnalyticOnNhd ℂ Vminus (strip θ (3 * Y + boundaryMargin P)) ∧
        (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
          Vplus w ∈ strip θ (3 * Y) ∧ attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (Vplus w) = w) ∧
        (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
          Vminus w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (Vminus w) = w) ∧
        (∀ x : ℝ, (x : ℂ) + (height θ / 2 : ℝ) * Complex.I ∈ strip θ (3 * Y + boundaryMargin P)) := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  obtain ⟨Vplus,Vminus,hVp,hVm,hsp,hsm⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  exact ⟨a,b,θ,Vplus,Vminus,hc,hVp,hVm,hsp,hsm,actual_midline_in_inverse_domain e₁ e₂ A B Γ s a b θ Y η M P hc⟩

end Kneser.ActualGrowingCoordinateInverse
end
