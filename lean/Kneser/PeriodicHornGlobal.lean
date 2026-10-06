import Kneser.PeriodicChartGluing
import Mathlib.Topology.Order.IntermediateValue

/-! Consistent integer continuations of actual overlapping image charts. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.PeriodicHornGlobal
open Filter Set Metric Complex Kneser.PeriodicChartGluing
open Kneser.LocalPeriodicStrip
open scoped Topology

def domain (c : ℝ → ℂ) (Y₀ : ℝ) : Set ℂ := {z | ∃ Y : ℝ, Y₀ < Y ∧ z ∈ chartStrip (c Y)}

def chartHeight (c : ℝ → ℂ) (Y₀ : ℝ) (z : ℂ) : ℝ :=
  by
    classical
    exact if h : z ∈ domain c Y₀ then h.choose else Y₀+1

def globalHorn (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ : ℝ) (z : ℂ) : ℂ :=
  patch H (c (chartHeight c Y₀ z)) z

theorem chartHeight_spec (c : ℝ → ℂ) (Y₀ : ℝ) (z : ℂ) (hz : z ∈ domain c Y₀) :
    Y₀ < chartHeight c Y₀ z ∧ z ∈ chartStrip (c (chartHeight c Y₀ z)) := by
  simp only [chartHeight, hz, ↓reduceDIte]
  exact hz.choose_spec

theorem strips_overlap_centers (c d z : ℂ) (hc : z ∈ chartStrip c) (hd : z ∈ chartStrip d) :
    |c.im-d.im| < 2 := by
  change |(z-c).im|<1 at hc
  change |(z-d).im|<1 at hd
  have h₁ := abs_lt.mp hc
  have h₂ := abs_lt.mp hd
  simp only [Complex.sub_im] at h₁ h₂
  apply abs_lt.mpr
  constructor <;> linarith

theorem family_overlap (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ Y Z : ℝ)
    (ha : ∀ Y, Y₀ < Y → AnalyticOnNhd ℂ (fun w => H (c Y+w)) (ball (0 : ℂ) 4))
    (hp : ∀ Y, Y₀ < Y → ∀ w ∈ ball (0 : ℂ) 2, H (c Y+(w+1))=H (c Y+w)+1)
    (hclose : ∀ Y Z, Y₀ < Y → Y₀ < Z → ‖c Y-c Z‖ ≤ 5/4*|Y-Z|)
    (hsep : ∀ Y Z, Y₀ < Y → Y₀ < Z → 3/4*|Y-Z| ≤ |(c Y).im-(c Z).im|)
    (hY : Y₀ < Y) (hZ : Y₀ < Z) (z : ℂ)
    (hzY : z ∈ chartStrip (c Y)) (hzZ : z ∈ chartStrip (c Z)) :
    patch H (c Y) z=patch H (c Z) z := by
  have hi := strips_overlap_centers (c Y) (c Z) z hzY hzZ
  have hlo := hsep Y Z hY hZ
  have hnorm := hclose Y Z hY hZ
  have hd : ‖c Y-c Z‖<4 := by linarith
  exact overlap_eq H (c Y) (c Z) (ha Y hY) (ha Z hZ) (hp Y hY) (hp Z hZ) hd hi ⟨hzY,hzZ⟩

theorem globalHorn_eq_patch (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ : ℝ)
    (ha : ∀ Y, Y₀ < Y → AnalyticOnNhd ℂ (fun w => H (c Y+w)) (ball (0 : ℂ) 4))
    (hp : ∀ Y, Y₀ < Y → ∀ w ∈ ball (0 : ℂ) 2, H (c Y+(w+1))=H (c Y+w)+1)
    (hclose : ∀ Y Z, Y₀ < Y → Y₀ < Z → ‖c Y-c Z‖ ≤ 5/4*|Y-Z|)
    (hsep : ∀ Y Z, Y₀ < Y → Y₀ < Z → 3/4*|Y-Z| ≤ |(c Y).im-(c Z).im|)
    (Y : ℝ) (hY : Y₀ < Y) (z : ℂ) (hz : z ∈ chartStrip (c Y)) :
    globalHorn H c Y₀ z=patch H (c Y) z := by
  obtain ⟨hZ,hzZ⟩ := chartHeight_spec c Y₀ z ⟨Y,hY,hz⟩
  exact family_overlap H c Y₀ _ Y ha hp hclose hsep hZ hY z hzZ hz

theorem domain_isOpen (c : ℝ → ℂ) (Y₀ : ℝ) : IsOpen (domain c Y₀) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨Y,hY,hzY⟩ := hz
  exact mem_of_superset ((chartStrip_isOpen _).mem_nhds hzY) (fun w hw => ⟨Y,hY,hw⟩)

theorem globalHorn_analytic (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ : ℝ)
    (ha : ∀ Y, Y₀ < Y → AnalyticOnNhd ℂ (fun w => H (c Y+w)) (ball (0 : ℂ) 4))
    (hp : ∀ Y, Y₀ < Y → ∀ w ∈ ball (0 : ℂ) 2, H (c Y+(w+1))=H (c Y+w)+1)
    (hclose : ∀ Y Z, Y₀ < Y → Y₀ < Z → ‖c Y-c Z‖ ≤ 5/4*|Y-Z|)
    (hsep : ∀ Y Z, Y₀ < Y → Y₀ < Z → 3/4*|Y-Z| ≤ |(c Y).im-(c Z).im|) :
    AnalyticOnNhd ℂ (globalHorn H c Y₀) (domain c Y₀) := by
  intro z hz
  obtain ⟨Y,hY,hzY⟩ := hz
  have he : globalHorn H c Y₀ =ᶠ[𝓝 z] patch H (c Y) := by
    have hn : ∀ᶠ w in 𝓝 z, w∈chartStrip (c Y) := (chartStrip_isOpen _).mem_nhds hzY
    exact hn.mono (fun w hw => globalHorn_eq_patch H c Y₀ ha hp hclose hsep Y hY w hw)
  exact ((patch_analytic H (c Y) (ha Y hY) (hp Y hY)) z hzY).congr he.symm

theorem globalHorn_translation (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ : ℝ)
    (ha : ∀ Y, Y₀ < Y → AnalyticOnNhd ℂ (fun w => H (c Y+w)) (ball (0 : ℂ) 4))
    (hp : ∀ Y, Y₀ < Y → ∀ w ∈ ball (0 : ℂ) 2, H (c Y+(w+1))=H (c Y+w)+1)
    (hclose : ∀ Y Z, Y₀ < Y → Y₀ < Z → ‖c Y-c Z‖ ≤ 5/4*|Y-Z|)
    (hsep : ∀ Y Z, Y₀ < Y → Y₀ < Z → 3/4*|Y-Z| ≤ |(c Y).im-(c Z).im|)
    (z : ℂ) (hz : z ∈ domain c Y₀) :
    globalHorn H c Y₀ (z+1)=globalHorn H c Y₀ z+1 := by
  obtain ⟨Y,hY,hzY⟩ := hz
  have hzY' : z+1∈chartStrip (c Y) := by simpa only [chartStrip, Set.mem_setOf_eq, Complex.sub_im, Complex.add_im, Complex.one_im, add_zero] using hzY
  rw [globalHorn_eq_patch H c Y₀ ha hp hclose hsep Y hY _ hzY', globalHorn_eq_patch H c Y₀ ha hp hclose hsep Y hY z hzY]
  exact patch_translation H (c Y) z

theorem domain_contains_upper (c : ℝ → ℂ) (Y₀ M : ℝ) (hM : 0 ≤ M)
    (hc : ContinuousOn c (Ioi Y₀)) (hbound : ∀ Y, Y₀ < Y → |(c Y).im-Y| ≤ M) :
    {z : ℂ | Y₀+M+2 < z.im} ⊆ domain c Y₀ := by
  intro z hz
  let a : ℝ := Y₀+1
  let b : ℝ := z.im+M+1
  have ha : Y₀<a := by dsimp [a]; linarith
  have hb : Y₀<b := by dsimp [b]; change Y₀+M+2<z.im at hz; linarith
  have hab : a≤b := by dsimp [a,b]; change Y₀+M+2<z.im at hz; linarith
  have hsub : Icc a b ⊆ Ioi Y₀ := fun Y hY => ha.trans_le hY.1
  have hcont : ContinuousOn (fun Y => (c Y).im) (Icc a b) := Complex.continuous_im.comp_continuousOn (hc.mono hsub)
  have hlo : (c a).im≤z.im := by
    have hh := (abs_le.mp (hbound a ha)).2
    dsimp [a] at hh
    change Y₀+M+2<z.im at hz
    linarith
  have hhi : z.im≤(c b).im := by
    have hh := (abs_le.mp (hbound b hb)).1
    dsimp [b] at hh
    linarith
  obtain ⟨Y,hY,he⟩ := intermediate_value_Icc hab hcont ⟨hlo,hhi⟩
  refine ⟨Y,hsub hY,?_⟩
  change |(z-c Y).im|<1
  simp only [Complex.sub_im, he, sub_self, abs_zero]
  norm_num

theorem domain_add_one_iff (c : ℝ → ℂ) (Y₀ : ℝ) (z : ℂ) :
    z+1 ∈ domain c Y₀ ↔ z ∈ domain c Y₀ := by
  simp only [domain, Set.mem_setOf_eq, chartStrip, Complex.sub_im, Complex.add_im, Complex.one_im, add_zero]

theorem globalHorn_translation_all (H : ℂ → ℂ) (c : ℝ → ℂ) (Y₀ : ℝ)
    (ha : ∀ Y, Y₀ < Y → AnalyticOnNhd ℂ (fun w => H (c Y+w)) (ball (0 : ℂ) 4))
    (hp : ∀ Y, Y₀ < Y → ∀ w ∈ ball (0 : ℂ) 2, H (c Y+(w+1))=H (c Y+w)+1)
    (hclose : ∀ Y Z, Y₀ < Y → Y₀ < Z → ‖c Y-c Z‖ ≤ 5/4*|Y-Z|)
    (hsep : ∀ Y Z, Y₀ < Y → Y₀ < Z → 3/4*|Y-Z| ≤ |(c Y).im-(c Z).im|)
    (z : ℂ) : globalHorn H c Y₀ (z+1)=globalHorn H c Y₀ z+1 := by
  classical
  by_cases hz : z∈domain c Y₀
  · exact globalHorn_translation H c Y₀ ha hp hclose hsep z hz
  · have hz' : z+1∉domain c Y₀ := by simpa only [domain_add_one_iff] using hz
    simp only [globalHorn, chartHeight, hz, hz', ↓reduceDIte]
    exact patch_translation H (c (Y₀+1)) z

theorem patch_displacement_bound (H : ℂ → ℂ) (c z : ℂ) (B : ℝ)
    (hb : ∀ w∈ball (0:ℂ) 2, ‖H (c+w)-(c+w)‖≤B) (hz : z∈chartStrip c) :
    ‖patch H c z-z‖≤B := by
  have hr := reduced_mem_ball (z-c) hz
  have hh := hb (reduced (z-c)) hr
  have he : patch H c z-z=H (c+reduced (z-c))-(c+reduced (z-c)) := by
    dsimp [patch, LocalPeriodicStrip.lift, reduced]
    ring
  rw [he]
  exact hh

end Kneser.PeriodicHornGlobal
end
