import Kneser.HolomorphicInjectiveInverse

/-! The actual normalized repelling coordinate has one injective high
vertical source strip and one holomorphic inverse on its whole open image.
Consequently inverse charts at different heights agree exactly. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.UpperCanonicalInjectivity

open Filter Set Metric Complex Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.RepellingExponentialOrbit Kneser.ParabolicCoordinateJacobian
open Kneser.CanonicalBasinExtension Kneser.FatouBasinExtension
open Kneser.CanonicalHighImaginaryAsymptotics Kneser.HighImaginaryOrbit
open Kneser.HolomorphicInjectiveInverse
open scoped Topology

def region (a Y : ℝ) : Set ℂ := {z | |z.re| < a ∧ Y < z.im}

def attractingZeta (R : ℝ) (z : ℂ) : ℂ := globalAttracting R (inverseCoordinate z)

def repellingZeta (R : ℝ) (z : ℂ) : ℂ := upperRepelling R (inverseCoordinate z)

def repellingTailZeta (R : ℝ) (z : ℂ) : ℂ := repellingZeta R z - zetaModel 1 z

theorem region_isOpen (a Y : ℝ) : IsOpen (region a Y) :=
  (isOpen_lt (Complex.continuous_re.abs) continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem region_convex (a Y : ℝ) : Convex ℝ (region a Y) := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    constructor
    · intro x y; simp
    · intro c z; simp
  have he : region a Y = {z : ℂ | -a < z.re} ∩ {z : ℂ | z.re < a} ∩ {z : ℂ | Y < z.im} := by
    ext z
    simp only [region, mem_setOf_eq, mem_inter_iff, abs_lt]
  rw [he]
  exact ((convex_halfSpace_re_gt (-a)).inter (convex_halfSpace_re_lt a)).inter (convex_halfSpace_gt hlin Y)

theorem inverseCoordinate_upper (z : ℂ) (hz : 0 < z.im) : 0 < (inverseCoordinate z).im := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hq := Complex.normSq_pos.mpr hn
  have he : (inverseCoordinate z).im = 2 * z.im / Complex.normSq z := by
    simp only [inverseCoordinate, Complex.div_im]
    norm_num
    ring
  rw [he]
  exact div_pos (mul_pos (by norm_num) hz) hq

theorem model_inverseCoordinate (z : ℂ) :
    ParabolicFatouCoordinate.model (inverseCoordinate z) = zetaModel 1 z := by
  change inverseCoordinate (inverseCoordinate z) + Complex.log (-inverseCoordinate z) / 3 = _
  rw [inverseCoordinate_involutive]
  have he : -inverseCoordinate z = 2 / z := by dsimp [inverseCoordinate]; ring
  rw [he]
  simp only [zetaModel, one_mul]

theorem exists_high_basin (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₀ : ℝ, 0 < Y₀ ∧ ∀ z : ℂ, |z.re| ≤ 64 → Y₀ < z.im →
      inverseCoordinate z ∈ basin parabolicMap (petal R) ∧
      -inverseCoordinate z ∈ basin parabolicInverse (petal R) := by
  let Y₀ : ℝ := max 32768 (1024 * (R + 1))
  have hY₀ : 0 < Y₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32768) (le_max_left _ _)
  refine ⟨Y₀, hY₀, ?_⟩
  intro z hRe hheight
  have hY : 0 < z.im := hY₀.trans hheight
  have hYbig : 32768 < z.im := (le_max_left _ _).trans_lt hheight
  have hYR : 1024 * (R + 1) < z.im := (le_max_right _ _).trans_lt hheight
  let N : ℕ := Nat.floor (z.im / 128)
  have hNu : (N : ℝ) ≤ z.im / 128 := Nat.floor_le (by positivity)
  have hNl : z.im / 128 - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hgate : 64 * ((N : ℝ) + 1) ≤ z.im := by linarith
  have hden : z.im / 1024 ≤ 3 * (N : ℝ) / 4 - 64 := by linarith
  have hdeep : R < 3 * (N : ℝ) / 4 - 64 := by linarith
  have hz : inverseCoordinate (inverseCoordinate z) = z := inverseCoordinate_involutive z
  have hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (inverseCoordinate z)).im| := by
    simpa only [hz, abs_of_pos hY] using hgate
  have hre : |(inverseCoordinate (inverseCoordinate z)).re| ≤ 64 := by simpa only [hz] using hRe
  have hpa := finite_orbit_re_lower parabolicMap inverse_step_error_bound (inverseCoordinate z) N hg hre
  have hea : Entry parabolicMap (petal R) (inverseCoordinate z) N :=
    ⟨hdeep.trans_le hpa, iterate_analytic_jacobian _ parabolicMap_analytic_jacobian _ N⟩
  have hneg : inverseCoordinate (-inverseCoordinate z) = -z := by
    calc
      _ = -inverseCoordinate (inverseCoordinate z) := by simp only [inverseCoordinate, div_neg]
      _ = -z := by rw [inverseCoordinate_involutive]
  have hgr : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-inverseCoordinate z)).im| := by
    simpa only [hneg, Complex.neg_im, abs_neg, abs_of_pos hY] using hgate
  have hrer : |(inverseCoordinate (-inverseCoordinate z)).re| ≤ 64 := by
    simpa only [hneg, Complex.neg_re, abs_neg] using hRe
  have hpr := finite_orbit_re_lower parabolicInverse RepellingExponentialOrbit.inverse_step_error_bound
    (-inverseCoordinate z) N hgr hrer
  have hp : (parabolicInverse^[N]) (-inverseCoordinate z) ∈ petal R := hdeep.trans_le hpr
  have her := CanonicalBasinExtension.inverse_gate_entry R N (inverseCoordinate z) (by
    simpa only [RepellingFatouCoordinate.inverseOrbit_zero_parameter] using hp) hgr
  exact ⟨⟨N, hea⟩, ⟨N, her⟩⟩

theorem exists_high_analytic_and_tail (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₀ C : ℝ, 0 < Y₀ ∧ 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 64 → Y₀ < z.im →
      AnalyticAt ℂ (attractingZeta R) z ∧ AnalyticAt ℂ (repellingZeta R) z ∧
      ‖repellingTailZeta R z‖ ≤ C / z.im := by
  obtain ⟨Yb, hYb, hbasin⟩ := exists_high_basin R hs
  obtain ⟨Ye, _Ca, Cr, hYe, _hCa, hCr, herr⟩ := exists_global_model_bounds R hs
  refine ⟨max Yb Ye, Cr, hYb.trans_le (le_max_left _ _), hCr, ?_⟩
  intro z hre hy
  have hzy : 0 < z.im := (hYb.trans_le (le_max_left _ _)).trans hy
  have hn : z ≠ 0 := by intro he; simp [he] at hzy
  have hi : AnalyticAt ℂ inverseCoordinate z := analyticAt_const.div analyticAt_id hn
  obtain ⟨hba, hbr⟩ := hbasin z hre ((le_max_left _ _).trans_lt hy)
  have haa := ((global_attracting_data R hs).2.1 _ hba).1
  have har := ((global_reflected_data R hs).2 _ hbr).1
  have hza : AnalyticAt ℂ (attractingZeta R) z := haa.comp hi
  have hzr : AnalyticAt ℂ (repellingZeta R) z := ((har.comp (f := fun w : ℂ => -inverseCoordinate w) hi.neg).neg).sub analyticAt_const
  have he := (herr (inverseCoordinate z) (by simpa only [inverseCoordinate_involutive] using hre)
    (by simpa only [inverseCoordinate_involutive, abs_of_pos hzy] using (le_max_right _ _).trans_lt hy)).2
  have hp := physical_model_eq_upper (inverseCoordinate z) (inverseCoordinate_upper z hzy)
  have hEq : repellingTailZeta R z =
      globalRepelling R (inverseCoordinate z) - (-RepellingFatouCoordinate.model (-inverseCoordinate z)) := by
    rw [hp, model_inverseCoordinate]
    dsimp [repellingTailZeta, repellingZeta, upperRepelling]
    ring
  refine ⟨hza, hzr, ?_⟩
  rw [hEq]
  simpa only [inverseCoordinate_involutive, abs_of_pos hzy] using he

theorem hasDerivAt_zetaModel_upper (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (zetaModel 1) (1 - 1 / (3 * z)) z := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hslit : (2 : ℂ) / z ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    have he : ((2 : ℂ) / z).im = -(2 * z.im) / Complex.normSq z := by
      simp only [Complex.div_im]
      norm_num
      ring
    rw [he]
    exact ne_of_lt (div_neg_of_neg_of_pos (by linarith) (Complex.normSq_pos.mpr hn))
  have hd := (hasDerivAt_id z).add
    (((((hasDerivAt_const z (2 : ℂ)).div (hasDerivAt_id z) hn).clog hslit).const_mul (1 : ℂ)).div_const 3)
  change HasDerivAt (zetaModel 1) (1 + 1 * ((0 * z - 2 * 1) / z ^ 2 / (2 / z)) / 3) z at hd
  convert hd using 1
  field_simp
  ring

theorem analyticAt_zetaModel_upper (z : ℂ) (hz : 0 < z.im) :
    AnalyticAt ℂ (zetaModel 1) z := by
  have hd : DifferentiableOn ℂ (zetaModel 1) {w : ℂ | 0 < w.im} :=
    fun w hw => (hasDerivAt_zetaModel_upper w hw).differentiableAt.differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)

theorem norm_zetaModel_deriv_sub_one (z : ℂ) (hz : 0 < z.im) :
    ‖deriv (zetaModel 1) z - 1‖ ≤ 1 / (3 * z.im) := by
  rw [(hasDerivAt_zetaModel_upper z hz).deriv]
  have he : (1 : ℂ) - 1 / (3 * z) - 1 = -(1 / (3 * z)) := by ring
  rw [he, norm_neg, norm_div, norm_one, norm_mul]
  have hthree : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [hthree]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (Complex.im_le_norm z) (by norm_num)

theorem shifted_disc_geometry (Y : ℝ) (z w : ℂ)
    (hz : |z.re| < 32 ∧ Y + 16 < z.im) (hw : w ∈ closedBall z 16) :
    |w.re| < 64 ∧ Y < w.im ∧ z.im - 16 ≤ w.im := by
  have hn : ‖w - z‖ ≤ 16 := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w - z)).trans hn
  have him := (Complex.abs_im_le_norm (w - z)).trans hn
  simp only [Complex.sub_re] at hre
  simp only [Complex.sub_im] at him
  have hb := abs_add_le (w.re - z.re) z.re
  rw [sub_add_cancel] at hb
  have hh := (abs_le.mp him).1
  constructor
  · linarith [hz.1]
  · constructor <;> linarith [hz.2]

theorem norm_deriv_tail (R Y C : ℝ) (hY : 0 < Y) (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, |z.re| ≤ 64 → Y < z.im → AnalyticAt ℂ (repellingZeta R) z ∧
      ‖repellingTailZeta R z‖ ≤ C / z.im)
    (z : ℂ) (hz : z ∈ region 32 (Y + 16)) :
    ‖deriv (repellingTailZeta R) z‖ ≤ (C / (z.im - 16)) / 16 := by
  have hgeom := fun w hw => shifted_disc_geometry Y z w
    (show |z.re| < 32 ∧ Y + 16 < z.im from hz) hw
  have ha : ∀ w ∈ closedBall z 16, AnalyticAt ℂ (repellingTailZeta R) w := by
    intro w hw
    have hh := hgeom w hw
    have hr := (hb w hh.1.le hh.2.1).1
    have hm : AnalyticAt ℂ (zetaModel 1) w :=
      analyticAt_zetaModel_upper w (hY.trans hh.2.1)
    exact hr.sub hm
  have hd : DifferentiableOn ℂ (repellingTailZeta R) (closedBall z 16) :=
    fun w hw => (ha w hw).differentiableAt.differentiableWithinAt
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 16)
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  intro w hw
  have hh := hgeom w (sphere_subset_closedBall hw)
  exact ((hb w hh.1.le hh.2.1).2).trans
    (div_le_div_of_nonneg_left hC (by have hh : Y + 16 < z.im := hz.2; linarith) hh.2.2)


theorem exists_high_univalent_inverse (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₁ : ℝ, 0 < Y₁ ∧
      AnalyticOnNhd ℂ (attractingZeta R) (region 32 Y₁) ∧
      AnalyticOnNhd ℂ (repellingZeta R) (region 32 Y₁) ∧
      (∀ z ∈ region 32 Y₁, ‖deriv (repellingZeta R) z - 1‖ ≤ 1 / 4) ∧
      InjOn (repellingZeta R) (region 32 Y₁) ∧
      IsOpen (repellingZeta R '' region 32 Y₁) ∧
      AnalyticOnNhd ℂ (imageInverse (repellingZeta R) (region 32 Y₁))
        (repellingZeta R '' region 32 Y₁) ∧
      (∀ z ∈ region 32 Y₁, imageInverse (repellingZeta R) (region 32 Y₁) (repellingZeta R z) = z) := by
  obtain ⟨Y, C, hY, hC, hb⟩ := exists_high_analytic_and_tail R hs
  let Y₁ : ℝ := max (Y + 32) (16 * C + 64)
  have hY₁ : 0 < Y₁ := lt_of_lt_of_le (by linarith : 0 < Y + 32) (le_max_left _ _)
  have hyY : Y + 32 ≤ Y₁ := le_max_left _ _
  have hyC : 16 * C + 64 ≤ Y₁ := le_max_right _ _
  have ha : AnalyticOnNhd ℂ (attractingZeta R) (region 32 Y₁) := by
    intro z hz
    exact (hb z (by have hh : |z.re| < 32 := hz.1; linarith)
      (by have hh : Y₁ < z.im := hz.2; linarith)).1
  have hr : AnalyticOnNhd ℂ (repellingZeta R) (region 32 Y₁) := by
    intro z hz
    exact (hb z (by have hh : |z.re| < 32 := hz.1; linarith)
      (by have hh : Y₁ < z.im := hz.2; linarith)).2.1
  have hder : ∀ z ∈ region 32 Y₁, ‖deriv (repellingZeta R) z - 1‖ ≤ 1 / 4 := by
    intro z hz
    have hzi : 0 < z.im := hY₁.trans hz.2
    have htm : AnalyticAt ℂ (zetaModel 1) z := analyticAt_zetaModel_upper z hzi
    have ht : AnalyticAt ℂ (repellingTailZeta R) z := (hr z hz).sub htm
    have hdt := norm_deriv_tail R Y C hY hC (fun z hzr hzy => ⟨(hb z hzr hzy).2.1, (hb z hzr hzy).2.2⟩)
      z (show z ∈ region 32 (Y + 16) from ⟨hz.1, by linarith [hz.2]⟩)
    have hzs : 64 < z.im := by linarith [hz.2]
    have hct : C < z.im - 16 := by linarith [hz.2]
    have htailSmall : ‖deriv (repellingTailZeta R) z‖ ≤ 1 / 16 := by
      apply hdt.trans
      have hd : 0 < z.im - 16 := by linarith
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
      norm_num
      exact (div_le_one hd).mpr hct.le
    have hmodelSmall : ‖deriv (zetaModel 1) z - 1‖ ≤ 1 / 16 := by
      apply (norm_zetaModel_deriv_sub_one z hzi).trans
      apply (div_le_iff₀ (by positivity : 0 < 3 * z.im)).mpr
      linarith
    have hEq : repellingZeta R = fun w => repellingTailZeta R w + zetaModel 1 w := by
      funext w
      dsimp [repellingTailZeta]
      ring
    have hd : deriv (repellingZeta R) z = deriv (repellingTailZeta R) z + deriv (zetaModel 1) z := by
      rw [hEq]
      exact deriv_add ht.differentiableAt htm.differentiableAt
    rw [hd, add_sub_assoc]
    exact (norm_add_le _ _).trans ((add_le_add htailSmall hmodelSmall).trans (by norm_num))
  have hi : InjOn (repellingZeta R) (region 32 Y₁) := by
    intro z hz w hw heq
    have hd : ∀ x ∈ region 32 Y₁, DifferentiableAt ℂ (fun t => repellingZeta R t - t) x :=
      fun x hx => (hr x hx).differentiableAt.sub differentiableAt_id
    have hbd : ∀ x ∈ region 32 Y₁, ‖deriv (fun t => repellingZeta R t - t) x‖ ≤ 1 / 4 := by
      intro x hx
      have he := ((hr x hx).hasStrictDerivAt.hasDerivAt.sub (hasDerivAt_id x)).deriv
      change deriv (fun t => repellingZeta R t - t) x = deriv (repellingZeta R) x - 1 at he
      rw [he]
      exact hder x hx
    have he := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd (region_convex 32 Y₁) hw hz
    have he' : (repellingZeta R z - z) - (repellingZeta R w - w) = -(z - w) := by rw [heq]; ring
    rw [he', norm_neg] at he
    have hn : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hne : ∀ z ∈ region 32 Y₁, deriv (repellingZeta R) z ≠ 0 := by
    intro z hz he
    have hh := hder z hz
    rw [he, zero_sub, norm_neg, norm_one] at hh
    norm_num at hh
  have hd : ∀ z ∈ region 32 Y₁, AnalyticAt ℂ (repellingZeta R) z ∧ deriv (repellingZeta R) z ≠ 0 :=
    fun z hz => ⟨hr z hz, hne z hz⟩
  exact ⟨Y₁, hY₁, ha, hr, hder, hi,
    image_isOpen _ _ (region_isOpen 32 Y₁) hd,
    analyticOnNhd_imageInverse _ _ (region_isOpen 32 Y₁) hi hd,
    fun z hz => imageInverse_left _ _ hi z hz⟩

end Kneser.UpperCanonicalInjectivity
end
