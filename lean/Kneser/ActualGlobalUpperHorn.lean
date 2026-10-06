import Kneser.ActualUpperHornCenters
import Kneser.PeriodicHornGlobal

/-! The canonical actual upper horn is obtained by consistent integer
continuation of genuine common-inverse image charts, and tends to identity
uniformly at upper infinity. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualGlobalUpperHorn
open Filter Set Metric Complex
open Kneser.CanonicalBasinExtension Kneser.UpperCanonicalInjectivity
open Kneser.CanonicalUpperHornCharts Kneser.CanonicalUpperAbel
open Kneser.ActualUpperHornCenters Kneser.PeriodicChartGluing Kneser.PeriodicHornGlobal
open scoped Topology

theorem exists_actual_global_upper_horn (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₁ Y₀ M C : ℝ, ∃ H : ℂ → ℂ,
      H=globalHorn (hornOnImage R Y₁) (imageCenter R) Y₀ ∧
      17≤Y₀ ∧ 0≤M ∧ 0≤C ∧
      InjOn (repellingZeta R) (region 32 Y₁) ∧
      (∀ Y : ℝ, Y₀<Y → ∀ w∈ball (0:ℂ) 2,
        hornOnImage R Y₁ (imageCenter R Y+(w+1))=hornOnImage R Y₁ (imageCenter R Y+w)+1) ∧
      AnalyticOnNhd ℂ H {z : ℂ | Y₀+M+2<z.im} ∧
      (∀ z : ℂ, H (z+1)=H z+1) ∧
      (∀ Y : ℝ, Y₀<Y → ∀ z∈chartStrip (imageCenter R Y),
        H z=patch (hornOnImage R Y₁) (imageCenter R Y) z) ∧
      (∀ Y : ℝ, Y₀<Y → ∀ w∈ball (0:ℂ) 1,
        imageCenter R Y+w∈repellingZeta R '' region 32 Y₁ ∧
        H (imageCenter R Y+w)=hornOnImage R Y₁ (imageCenter R Y+w)) ∧
      (∀ z : ℂ, Y₀+M+18<z.im → ‖H z-z‖≤C/(z.im-M-17)) := by
  obtain ⟨Y₁,Yc,C,_hY₁,_hYc,hC,_hopen,hi,_ha,hcharts⟩ := exists_actual_high_periodic_horn_charts R hs
  obtain ⟨Yg,M,hM,hcc,hcb,hclose,hsep⟩ := exists_actual_centers_geometry R hs
  let Y₀ : ℝ := max Yc (max Yg 17)
  have hYc : Yc≤Y₀ := le_max_left _ _
  have hYg : Yg≤Y₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h17 : 17≤Y₀ := (le_max_right _ _).trans (le_max_right _ _)
  let H : ℂ → ℂ := globalHorn (hornOnImage R Y₁) (imageCenter R) Y₀
  have ha : ∀ Y, Y₀<Y → AnalyticOnNhd ℂ (fun w => hornOnImage R Y₁ (imageCenter R Y+w)) (ball (0:ℂ) 4) := by
    intro Y hY
    obtain ⟨_V,_hVa,hTa,_hp,_hV⟩ := hcharts Y (hYc.trans_lt hY)
    exact hTa
  have hp : ∀ Y, Y₀<Y → ∀ w∈ball (0:ℂ) 2,
      hornOnImage R Y₁ (imageCenter R Y+(w+1))=hornOnImage R Y₁ (imageCenter R Y+w)+1 := by
    intro Y hY
    obtain ⟨_V,_hVa,_hTa,hp,_hV⟩ := hcharts Y (hYc.trans_lt hY)
    exact hp
  have hcl : ∀ Y Z, Y₀<Y → Y₀<Z → ‖imageCenter R Y-imageCenter R Z‖≤5/4*|Y-Z| :=
    fun Y Z hY hZ => hclose Y Z (hYg.trans_lt hY) (hYg.trans_lt hZ)
  have hsp : ∀ Y Z, Y₀<Y → Y₀<Z → 3/4*|Y-Z|≤|(imageCenter R Y).im-(imageCenter R Z).im| :=
    fun Y Z hY hZ => hsep Y Z (hYg.trans_lt hY) (hYg.trans_lt hZ)
  have hbound : ∀ Y, Y₀<Y → |(imageCenter R Y).im-Y|≤M := fun Y hY => hcb Y (hYg.trans_lt hY)
  have hcoverage := domain_contains_upper (imageCenter R) Y₀ M hM (hcc.mono (Ioi_subset_Ioi hYg)) hbound
  have heq : ∀ Y, Y₀<Y → ∀ z∈chartStrip (imageCenter R Y), H z=patch (hornOnImage R Y₁) (imageCenter R Y) z :=
    globalHorn_eq_patch _ _ _ ha hp hcl hsp
  refine ⟨Y₁,Y₀,M,C,H,rfl,h17,hM,hC,hi,hp,(globalHorn_analytic _ _ _ ha hp hcl hsp).mono hcoverage,
    globalHorn_translation_all _ _ _ ha hp hcl hsp,heq,?_,?_⟩
  · intro Y hY w hw
    have hw2 : w∈ball (0:ℂ) 2 := ball_subset_ball (by norm_num) hw
    have hw4 : w∈ball (0:ℂ) 4 := ball_subset_ball (by norm_num) hw
    have hws : imageCenter R Y+w∈chartStrip (imageCenter R Y) := by
      change |((imageCenter R Y+w)-imageCenter R Y).im|<1
      rw [add_sub_cancel_left]
      exact (Complex.abs_im_le_norm w).trans_lt (by simpa only [mem_ball,dist_zero_right] using hw)
    obtain ⟨_V,_hVa,_hTa,_hp,hV⟩ := hcharts Y (hYc.trans_lt hY)
    refine ⟨(hV w hw4).2.1,?_⟩
    rw [heq Y hY _ hws]
    exact patch_eq_of_small _ _ _ (hp Y hY) (by simpa only [add_sub_cancel_left] using hw2) hws
  · intro z hz
    have hzdom : z∈domain (imageCenter R) Y₀ := hcoverage (by change Y₀+M+2<z.im; linarith)
    obtain ⟨Y,hY,hzY⟩ := hzdom
    rw [heq Y hY z hzY]
    have hb : ∀ w∈ball (0:ℂ) 2, ‖hornOnImage R Y₁ (imageCenter R Y+w)-(imageCenter R Y+w)‖≤C/(Y-16) := by
      intro w hw
      obtain ⟨_V,_hVa,_hTa,_hp,hV⟩ := hcharts Y (hYc.trans_lt hY)
      exact (hV w (ball_subset_ball (by norm_num) hw)).2.2.2.2
    have hn := patch_displacement_bound _ _ z (C/(Y-16)) hb hzY
    have hy : z.im-M-17≤Y-16 := by
      have hh := (abs_lt.mp (show |(z-imageCenter R Y).im|<1 from hzY)).2
      simp only [Complex.sub_im] at hh
      have hc := (abs_le.mp (hbound Y hY)).2
      linarith
    have hzpos : 0<z.im-M-17 := by linarith
    exact hn.trans (div_le_div_of_nonneg_left hC hzpos hy)

end Kneser.ActualGlobalUpperHorn
end
