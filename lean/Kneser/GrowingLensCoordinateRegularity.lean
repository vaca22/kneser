import Kneser.GrowingLensSpatialHolomorphy
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative regularity of the actual growing-strip model and orbit
corrections, with Cauchy estimates on fixed-width buffered substrips. -/

noncomputable section
set_option maxHeartbeats 600000
namespace Kneser.GrowingLensCoordinateRegularity

open Filter Set Metric Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.RealLensMidline
open scoped Topology

def chartModel (s a b θ : ℝ) (e₁ e₂ : ℂ) (Z : ℂ) : ℂ :=
  Z + residueSum s a b * Complex.log ((b : ℂ) - bandChart a b θ Z) +
    e₁ * bandChart a b θ Z + e₂ * (bandChart a b θ Z) ^ 2

theorem chartModel_eq_lensModel (s a b θ Y : ℝ) (e₁ e₂ Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) :
    chartModel s a b θ e₁ e₂ Z = lensModel s a b θ e₁ e₂ (bandChart a b θ Z) := by
  simp only [chartModel, lensModel, bandTime_bandChart a b θ Y Z hab hθ hY hYθ hZ]

theorem chart_log_mem_slit (a b θ Y : ℝ) (Z : ℂ) (hab : a < b)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y) :
    (b : ℂ) - bandChart a b θ Z ∈ Complex.slitPlane := by
  let u := bandChart a b θ Z
  have hroots := bandChart_ne_roots a b θ Y Z hab hθ hY hYθ hZ
  have ht := bandTime_bandChart a b θ Y Z hab hθ hY hYθ hZ
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi : u.im = 0
  · left
    have hu : u = (u.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hh := real_bandTime_between a b θ u.re hab hθ
      (by intro he; apply hroots.1; change u = (a : ℂ); rw [hu,he])
      (by intro he; apply hroots.2; change u = (b : ℂ); rw [hu,he])
      (by rw [← hu]; change 0 < (bandTime a b θ (bandChart a b θ Z)).im; rw [ht]; linarith [hZ.1])
    simpa only [Complex.sub_re, Complex.ofReal_re] using sub_pos.mpr hh.2
  · right
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_ne_zero] using hi

theorem analyticOnNhd_chartModel (s a b θ Y : ℝ) (e₁ e₂ : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) :
    AnalyticOnNhd ℂ (chartModel s a b θ e₁ e₂) (strip θ Y) := by
  intro Z hZ
  have hu := analyticOnNhd_bandChart a b θ Y hab hθ hY hYθ Z hZ
  have hl := (analyticAt_const.sub hu).clog (chart_log_mem_slit a b θ Y Z hab hθ hY hYθ hZ)
  exact ((analyticAt_id.add (analyticAt_const.mul hl)).add (analyticAt_const.mul hu)).add
    (analyticAt_const.mul (hu.pow 2))

theorem buffered_closedBall_subset (θ Y : ℝ) (Z : ℂ) (hY : 0 < Y)
    (hZ : Z ∈ strip θ (2 * Y)) : closedBall Z (Y / 2) ⊆ strip θ Y := by
  intro W hW
  have hd : ‖W - Z‖ ≤ Y / 2 := by simpa only [dist_eq_norm] using mem_closedBall.mp hW
  have hh := (Complex.abs_im_le_norm (W-Z)).trans hd
  rw [Complex.sub_im] at hh
  have hl := (abs_le.mp hh).1
  have hu := (abs_le.mp hh).2
  exact ⟨by linarith [hZ.1], by linarith [hZ.2]⟩

/-- Cauchy estimates for any bounded actual correction on the larger strip. -/
theorem norm_deriv_le_on_buffered_strip (T : ℂ → ℂ) (θ Y B : ℝ) (hY : 0 < Y)
    (hhol : AnalyticOnNhd ℂ T (strip θ Y)) (hbound : ∀ W ∈ strip θ Y, ‖T W‖ ≤ B)
    (Z : ℂ) (hZ : Z ∈ strip θ (2 * Y)) : ‖deriv T Z‖ ≤ 2 * B / Y := by
  have hsub := buffered_closedBall_subset θ Y Z hY hZ
  have hd : DifferentiableOn ℂ T (closedBall Z (Y / 2)) :=
    fun W hW => (hhol W (hsub hW)).differentiableAt.differentiableWithinAt
  have hb : ∀ W ∈ sphere Z (Y / 2), ‖T W‖ ≤ B := by
    intro W hW
    exact hbound W (hsub (mem_closedBall.mpr (mem_sphere.mp hW).le))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Y / 2)
    ((hd.mono closure_ball_subset_closedBall).diffContOnCl) hb
  exact hc.trans_eq (by field_simp)


theorem band_denominator_ne_zero (_a _b θ Y : ℝ) (Z : ℂ)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y) :
    1 - Complex.exp (-(θ : ℂ) * Z) ≠ 0 := by
  have hd := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  intro he
  rw [he,norm_zero] at hd
  have hp : 0 < θ * Y / Real.pi * (1 + ‖Complex.exp (-(θ : ℂ) * Z)‖) := by positivity
  linarith

theorem hasDerivAt_bandChart (a b θ Y : ℝ) (Z : ℂ)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y) :
    HasDerivAt (bandChart a b θ)
      ((θ : ℂ) * ((b : ℂ) - a) * Complex.exp (-(θ : ℂ) * Z) /
        (1 - Complex.exp (-(θ : ℂ) * Z)) ^ 2) Z := by
  have he : HasDerivAt (fun W : ℂ => Complex.exp (-(θ : ℂ) * W))
      (Complex.exp (-(θ : ℂ) * Z) * (-(θ : ℂ))) Z :=
    by simpa only [id_eq, mul_one] using ((hasDerivAt_id Z).const_mul (-(θ : ℂ))).cexp
  have hne := band_denominator_ne_zero a b θ Y Z hθ hY hYθ hZ
  have hh := ((hasDerivAt_const Z (a : ℂ)).sub (he.const_mul (b : ℂ))).div
    ((hasDerivAt_const Z (1 : ℂ)).sub he) hne
  convert hh using 1 <;> first | rfl | (dsimp [bandChart,rootChart]; ring)

theorem hasDerivAt_chartLog (a b θ Y : ℝ) (Z : ℂ) (hab : a < b)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y) :
    HasDerivAt (fun W => Complex.log ((b : ℂ) - bandChart a b θ W))
      (-(θ : ℂ) * Complex.exp (-(θ : ℂ) * Z) /
        (1 - Complex.exp (-(θ : ℂ) * Z))) Z := by
  have hu := hasDerivAt_bandChart a b θ Y Z hθ hY hYθ hZ
  have hh := ((hasDerivAt_const Z (b : ℂ)).sub hu).clog
    (chart_log_mem_slit a b θ Y Z hab hθ hY hYθ hZ)
  have hne := band_denominator_ne_zero a b θ Y Z hθ hY hYθ hZ
  have hgap : (b : ℂ) - a ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (ne_of_gt hab)
  have hbminus : (b : ℂ) - bandChart a b θ Z =
      ((b : ℂ) - a) / (1 - Complex.exp (-(θ : ℂ) * Z)) := by
    dsimp [bandChart,rootChart]
    generalize hq : Complex.exp (-(θ : ℂ) * Z) = q at hne ⊢
    field_simp [hne]
    ring
  have hder : (0 - (θ : ℂ) * ((b : ℂ) - a) * Complex.exp (-(θ : ℂ) * Z) /
        (1 - Complex.exp (-(θ : ℂ) * Z)) ^ 2) /
        ((b : ℂ) - bandChart a b θ Z) =
      -(θ : ℂ) * Complex.exp (-(θ : ℂ) * Z) / (1 - Complex.exp (-(θ : ℂ) * Z)) := by
    rw [hbminus]
    generalize hq : Complex.exp (-(θ : ℂ) * Z) = q at hne ⊢
    field_simp [hne,hgap]
    ring
  convert hh using 1 <;> first | rfl | exact hder.symm

theorem norm_chartLog_deriv_le (a b θ Y : ℝ) (Z : ℂ) (hab : a < b)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y) :
    ‖deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z‖ ≤ Real.pi / Y := by
  rw [(hasDerivAt_chartLog a b θ Y Z hab hθ hY hYθ hZ).deriv]
  simp only [norm_div,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hθ]
  have hd := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hne := band_denominator_ne_zero a b θ Y Z hθ hY hYθ hZ
  apply (div_le_div_iff₀ (norm_pos_iff.mpr hne) hY).mpr
  have hh : θ * Y * (1 + ‖Complex.exp (-(θ : ℂ) * Z)‖) ≤
      ‖1 - Complex.exp (-(θ : ℂ) * Z)‖ * Real.pi := by
    apply (div_le_iff₀ Real.pi_pos).mp
    convert hd using 1 <;> first | rfl | ring
  nlinarith only [hh, mul_pos hθ hY, norm_nonneg (Complex.exp (-(θ : ℂ) * Z))]


theorem inner_strip_subset (θ Y : ℝ) (hY : 0 ≤ Y) : strip θ (2 * Y) ⊆ strip θ Y := by
  intro Z hZ
  exact ⟨by linarith [hZ.1], by linarith [hZ.2]⟩

theorem norm_chartModel_deriv_sub_one_le
    (s a b θ Y η P : ℝ) (e₁ e₂ Z : ℂ) (hab : a < b) (hθ : 0 < θ)
    (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hR : ‖residueSum s a b‖ ≤ 1) (he₁ : ‖e₁‖ ≤ P) (he₂ : ‖e₂‖ ≤ P)
    (hu : ∀ W ∈ strip θ Y, ‖bandChart a b θ W‖ ≤ η / 4)
    (hZ : Z ∈ strip θ (2 * Y)) :
    ‖deriv (chartModel s a b θ e₁ e₂) Z - 1‖ ≤ (Real.pi + P * η) / Y := by
  have hZ₀ := inner_strip_subset θ Y hY.le hZ
  have hau := analyticOnNhd_bandChart a b θ Y hab hθ hY hYθ
  have hdU := (hau Z hZ₀).differentiableAt.hasDerivAt
  have hdL := (hasDerivAt_chartLog a b θ Y Z hab hθ hY hYθ hZ₀)
  have hh := (((hasDerivAt_id Z).add (hdL.const_mul (residueSum s a b))).add
    (hdU.const_mul e₁)).add ((hdU.pow 2).const_mul e₂)
  have hd : deriv (chartModel s a b θ e₁ e₂) Z =
      1 + residueSum s a b * deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z +
        e₁ * deriv (bandChart a b θ) Z + e₂ * (2 * bandChart a b θ Z * deriv (bandChart a b θ) Z) := by
    rw [hdL.deriv]
    convert hh.deriv using 1 <;> first | rfl | ring
  have hdUb := norm_deriv_le_on_buffered_strip (bandChart a b θ) θ Y (η / 4) hY hau hu Z hZ
  have hdLb := norm_chartLog_deriv_le a b θ Y Z hab hθ hY hYθ hZ₀
  have hUn : ‖bandChart a b θ Z‖ ≤ 1 / 2 := (hu Z hZ₀).trans (by linarith)
  rw [hd]
  rw [show (1 + residueSum s a b * deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z +
      e₁ * deriv (bandChart a b θ) Z + e₂ * (2 * bandChart a b θ Z * deriv (bandChart a b θ) Z)) - 1 =
      residueSum s a b * deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z +
      e₁ * deriv (bandChart a b θ) Z + e₂ * (2 * bandChart a b θ Z * deriv (bandChart a b θ) Z) by ring]
  calc
    _ ≤ ‖residueSum s a b * deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z‖ +
        ‖e₁ * deriv (bandChart a b θ) Z‖ + ‖e₂ * (2 * bandChart a b θ Z * deriv (bandChart a b θ) Z)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ = ‖residueSum s a b‖ * ‖deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z‖ +
        ‖e₁‖ * ‖deriv (bandChart a b θ) Z‖ + ‖e₂‖ * (2 * ‖bandChart a b θ Z‖ * ‖deriv (bandChart a b θ) Z‖) := by
      simp only [norm_mul,Complex.norm_ofNat]
    _ ≤ Real.pi / Y + P * (2 * (η / 4) / Y) + P * (1 * (2 * (η / 4) / Y)) := by
      have hu2 : 2 * ‖bandChart a b θ Z‖ ≤ 1 := by linarith
      have hRl : ‖residueSum s a b‖ * ‖deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z‖ ≤ Real.pi / Y := by
        calc
          _ ≤ 1 * ‖deriv (fun W => Complex.log ((b : ℂ) - bandChart a b θ W)) Z‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
          _ ≤ Real.pi / Y := by simpa only [one_mul] using hdLb
      gcongr
    _ = (Real.pi + P * η) / Y := by ring

end Kneser.GrowingLensCoordinateRegularity
end
