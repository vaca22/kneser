import Kneser.CanonicalUpperAbel

/-! Quantitative geometry of the genuine canonical upper image centers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualUpperHornCenters
open Filter Set Metric Complex
open Kneser.ParabolicCoordinateJacobian Kneser.CanonicalBasinExtension
open Kneser.UpperCanonicalInjectivity Kneser.CanonicalUpperHornCharts
open scoped Topology

theorem center_difference (R Yd Y Z : ℝ)
    (ha : AnalyticOnNhd ℂ (repellingZeta R) (region 32 Yd))
    (hder : ∀ z ∈ region 32 Yd, ‖deriv (repellingZeta R) z-1‖≤1/4)
    (hY : Yd<Y) (hZ : Yd<Z) :
    ‖imageCenter R Y-imageCenter R Z‖≤5/4*|Y-Z| ∧
    3/4*|Y-Z|≤|(imageCenter R Y).im-(imageCenter R Z).im| := by
  have hzY : CanonicalUpperHornCharts.center Y ∈ region 32 Yd := by
    constructor
    · simp [CanonicalUpperHornCharts.center]
    · simpa [CanonicalUpperHornCharts.center] using hY
  have hzZ : CanonicalUpperHornCharts.center Z ∈ region 32 Yd := by
    constructor
    · simp [CanonicalUpperHornCharts.center]
    · simpa [CanonicalUpperHornCharts.center] using hZ
  have hd : ∀ z∈region 32 Yd, DifferentiableAt ℂ (fun w => repellingZeta R w-w) z :=
    fun z hz => (ha z hz).differentiableAt.sub differentiableAt_id
  have hb : ∀ z∈region 32 Yd, ‖deriv (fun w => repellingZeta R w-w) z‖≤1/4 := by
    intro z hz
    have he := ((ha z hz).hasStrictDerivAt.hasDerivAt.sub (hasDerivAt_id z)).deriv
    change deriv (fun w => repellingZeta R w-w) z=deriv (repellingZeta R) z-1 at he
    rw [he]
    exact hder z hz
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (region_convex 32 Yd) hzZ hzY
  have hn : ‖CanonicalUpperHornCharts.center Y-CanonicalUpperHornCharts.center Z‖=|Y-Z| := by
    have he : CanonicalUpperHornCharts.center Y-CanonicalUpperHornCharts.center Z=I*((Y-Z:ℝ):ℂ) := by
      simp only [CanonicalUpperHornCharts.center, Complex.ofReal_sub]
      ring
    rw [he, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have he : (repellingZeta R (CanonicalUpperHornCharts.center Y)-CanonicalUpperHornCharts.center Y)-
      (repellingZeta R (CanonicalUpperHornCharts.center Z)-CanonicalUpperHornCharts.center Z)=
      (imageCenter R Y-imageCenter R Z)-(CanonicalUpperHornCharts.center Y-CanonicalUpperHornCharts.center Z) := by
    dsimp [imageCenter]
    ring
  rw [he,hn] at hh
  have hnorm := norm_add_le ((imageCenter R Y-imageCenter R Z)-(CanonicalUpperHornCharts.center Y-CanonicalUpperHornCharts.center Z))
    (CanonicalUpperHornCharts.center Y-CanonicalUpperHornCharts.center Z)
  rw [sub_add_cancel,hn] at hnorm
  have him := (Complex.abs_im_le_norm _).trans hh
  simp only [Complex.sub_im, CanonicalUpperHornCharts.center, Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at him
  have htri := abs_sub_le ((imageCenter R Y).im-(imageCenter R Z).im-(Y-Z)) ((imageCenter R Y).im-(imageCenter R Z).im) 0
  simp only [sub_zero] at htri
  have hlower : |Y-Z|≤|(imageCenter R Y).im-(imageCenter R Z).im-(Y-Z)|+|(imageCenter R Y).im-(imageCenter R Z).im| := by
    have ht := abs_sub ((imageCenter R Y).im-(imageCenter R Z).im)
      ((imageCenter R Y).im-(imageCenter R Z).im-(Y-Z))
    have he' : ((imageCenter R Y).im-(imageCenter R Z).im)-
      ((imageCenter R Y).im-(imageCenter R Z).im-(Y-Z))=Y-Z := by ring
    rw [he'] at ht
    linarith
  constructor <;> linarith

theorem center_model_im_bound (R Y Ct : ℝ) (hY : 1≤Y) (hCt : 0≤Ct)
    (ht : ‖repellingTailZeta R (CanonicalUpperHornCharts.center Y)‖≤Ct/Y) :
    |(imageCenter R Y).im-Y|≤Ct+Real.pi/3 := by
  have hb := Complex.abs_im_le_norm (repellingTailZeta R (CanonicalUpperHornCharts.center Y))
  change |(repellingZeta R (CanonicalUpperHornCharts.center Y)-zetaModel 1 (CanonicalUpperHornCharts.center Y)).im|≤_ at hb
  have hlog : |(Complex.log (2/CanonicalUpperHornCharts.center Y)).im|≤Real.pi := by
    apply abs_le.mpr
    exact ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
  have hmod : |(zetaModel 1 (CanonicalUpperHornCharts.center Y)).im-Y|≤Real.pi/3 := by
    simp only [zetaModel, one_mul, Complex.add_im, CanonicalUpperHornCharts.center, Complex.mul_im,
      Complex.I_re, Complex.ofReal_im, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add,
      Complex.div_ofNat_im, add_sub_cancel_left]
    simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<3)] using (div_le_div_of_nonneg_right (show |(Complex.log (2/(I*(Y:ℂ)))).im|≤Real.pi from hlog) (by norm_num : (0:ℝ)≤3))
  have hratio : Ct/Y≤Ct := by
    exact (div_le_iff₀ (by linarith : 0<Y)).mpr (by nlinarith)
  have htri := abs_add_le ((imageCenter R Y).im-(zetaModel 1 (CanonicalUpperHornCharts.center Y)).im)
    ((zetaModel 1 (CanonicalUpperHornCharts.center Y)).im-Y)
  rw [sub_add_sub_cancel] at htri
  have hb' : |(imageCenter R Y).im-(zetaModel 1 (CanonicalUpperHornCharts.center Y)).im|≤Ct/Y := by
    simpa only [Complex.sub_im, imageCenter] using hb.trans ht
  linarith

theorem exists_actual_centers_geometry (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Yg M : ℝ, 0≤M ∧ ContinuousOn (imageCenter R) (Ioi Yg) ∧
      (∀ Y, Yg<Y → |(imageCenter R Y).im-Y|≤M) ∧
      (∀ Y Z, Yg<Y → Yg<Z → ‖imageCenter R Y-imageCenter R Z‖≤5/4*|Y-Z|) ∧
      (∀ Y Z, Yg<Y → Yg<Z → 3/4*|Y-Z|≤|(imageCenter R Y).im-(imageCenter R Z).im|) := by
  obtain ⟨Yd,_hYd,_ha,hr,hd,_⟩ := exists_high_univalent_inverse R hs
  obtain ⟨Yt,Ct,_hYt,hCt,ht⟩ := exists_high_analytic_and_tail R hs
  let Yg : ℝ := max Yd (max Yt 1)
  refine ⟨Yg,Ct+Real.pi/3,by positivity,?_,?_,?_,?_⟩
  · intro Y hY
    have hz : CanonicalUpperHornCharts.center Y∈region 32 Yd := by
      constructor
      · simp [CanonicalUpperHornCharts.center]
      · simpa [CanonicalUpperHornCharts.center] using (le_max_left _ _).trans_lt hY
    exact ((hr _ hz).continuousAt.comp (by unfold CanonicalUpperHornCharts.center; fun_prop : ContinuousAt CanonicalUpperHornCharts.center Y)).continuousWithinAt
  · intro Y hY
    apply center_model_im_bound R Y Ct ((le_trans (le_max_right Yt 1) (le_max_right Yd (max Yt 1))).trans hY.le) hCt
    have hy : Yt<Y := (le_trans (le_max_left Yt 1) (le_max_right Yd (max Yt 1))).trans_lt hY
    simpa only [CanonicalUpperHornCharts.center, Complex.mul_im, Complex.I_re, Complex.ofReal_im, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] using (ht (CanonicalUpperHornCharts.center Y) (by simp [CanonicalUpperHornCharts.center]) (by simpa [CanonicalUpperHornCharts.center] using hy)).2.2
  · intro Y Z hY hZ
    exact (center_difference R Yd Y Z hr hd ((le_max_left _ _).trans_lt hY) ((le_max_left _ _).trans_lt hZ)).1
  · intro Y Z hY hZ
    exact (center_difference R Yd Y Z hr hd ((le_max_left _ _).trans_lt hY) ((le_max_left _ _).trans_lt hZ)).2

end Kneser.ActualUpperHornCenters
end
