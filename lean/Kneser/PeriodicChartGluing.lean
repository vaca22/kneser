import Kneser.LocalPeriodicStrip
import Mathlib.Analysis.Analytic.Uniqueness

/-! Integer continuation of genuine overlapping horn charts. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.PeriodicChartGluing
open Filter Set Metric Complex Kneser.LocalPeriodicStrip
open scoped Topology

def chartStrip (c : ℂ) : Set ℂ := {z | |(z-c).im| < 1}
def patch (H : ℂ → ℂ) (c z : ℂ) : ℂ := LocalPeriodicStrip.lift (fun w => H (c+w)) (z-c)

theorem chartStrip_isOpen (c : ℂ) : IsOpen (chartStrip c) :=
  isOpen_lt ((Complex.continuous_im.comp (continuous_id.sub continuous_const)).abs) continuous_const

theorem chartStrip_convex (c : ℂ) : Convex ℝ (chartStrip c) := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    constructor
    · intro x y; simp
    · intro a z; simp
  have he : chartStrip c = {z : ℂ | c.im-1 < z.im} ∩ {z : ℂ | z.im < c.im+1} := by
    ext z
    simp only [chartStrip, mem_setOf_eq, mem_inter_iff, Complex.sub_im, abs_lt]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he]
  exact (convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)

theorem norm_shift_one_le (w : ℂ) (hw : w.re ≤ -1) : ‖w+1‖ ≤ ‖w‖ := by
  have hsq : ‖w+1‖^2 ≤ ‖w‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
    nlinarith
  nlinarith [norm_nonneg w, norm_nonneg (w+1)]

theorem lift_eq_of_small (T : ℂ → ℂ)
    (hp : ∀ w ∈ ball (0 : ℂ) 2, T (w+1)=T w+1)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 2) (hstrip : w ∈ strip) : LocalPeriodicStrip.lift T w = T w := by
  have hn : ‖w‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hw
  have hre := (Complex.abs_re_le_norm w).trans_lt hn
  have hklo : -2 ≤ cell w := Int.le_floor.mpr (by norm_num; linarith [(abs_lt.mp hre).1])
  have hkhi : cell w < 2 := Int.floor_lt.mpr (by norm_num; exact (abs_lt.mp hre).2)
  have hk : cell w = -2 ∨ cell w = -1 ∨ cell w = 0 ∨ cell w = 1 := by omega
  rcases hk with hk | hk | hk | hk
  · have hr : w.re ≤ -1 := by
      have hh := Int.lt_floor_add_one w.re
      change w.re < (cell w : ℝ) + 1 at hh
      rw [hk] at hh
      norm_num at hh
      linarith
    have hplus : w+1 ∈ ball (0 : ℂ) 2 := by
      simpa only [mem_ball, dist_zero_right] using (norm_shift_one_le w hr).trans_lt hn
    have he : reduced w = (w+1)+1 := by simp only [reduced, hk]; norm_num <;> ring
    simp only [LocalPeriodicStrip.lift, he, hk]
    rw [hp _ hplus, hp w hw]
    norm_num
    ring
  · have he : reduced w = w+1 := by simp only [reduced, hk]; norm_num <;> ring
    simp only [LocalPeriodicStrip.lift, he, hk]
    rw [hp w hw]
    norm_num
  · simp only [LocalPeriodicStrip.lift, reduced, hk, Int.cast_zero, sub_zero, add_zero]
  · have he : reduced w+1 = w := by simp only [reduced, hk]; norm_num <;> ring
    have hh := hp (reduced w) (reduced_mem_ball w hstrip)
    rw [he] at hh
    simp only [LocalPeriodicStrip.lift, hk, Int.cast_one]
    exact hh.symm

theorem patch_analytic (H : ℂ → ℂ) (c : ℂ)
    (ha : AnalyticOnNhd ℂ (fun w => H (c+w)) (ball (0 : ℂ) 4))
    (hp : ∀ w ∈ ball (0 : ℂ) 2, H (c+(w+1))=H (c+w)+1) :
    AnalyticOnNhd ℂ (patch H c) (chartStrip c) := by
  intro z hz
  exact ((lift_analytic _ ha hp) (z-c) hz).comp (f := fun w : ℂ => w-c) (analyticAt_id.sub analyticAt_const)

theorem patch_translation (H : ℂ → ℂ) (c z : ℂ) : patch H c (z+1) = patch H c z+1 := by
  have he : z+1-c = (z-c)+1 := by ring
  simp only [patch, he, lift_translation]

theorem patch_eq_of_small (H : ℂ → ℂ) (c z : ℂ)
    (hp : ∀ w ∈ ball (0 : ℂ) 2, H (c+(w+1))=H (c+w)+1)
    (hz : z-c ∈ ball (0 : ℂ) 2) (hs : z ∈ chartStrip c) : patch H c z = H z := by
  unfold patch
  rw [lift_eq_of_small _ hp _ hz hs]
  congr 1
  ring

theorem overlap_eq (H : ℂ → ℂ) (c d : ℂ)
    (hac : AnalyticOnNhd ℂ (fun w => H (c+w)) (ball (0 : ℂ) 4))
    (had : AnalyticOnNhd ℂ (fun w => H (d+w)) (ball (0 : ℂ) 4))
    (hpc : ∀ w ∈ ball (0 : ℂ) 2, H (c+(w+1))=H (c+w)+1)
    (hpd : ∀ w ∈ ball (0 : ℂ) 2, H (d+(w+1))=H (d+w)+1)
    (hdist : ‖c-d‖ < 4) (him : |c.im-d.im| < 2) :
    EqOn (patch H c) (patch H d) (chartStrip c ∩ chartStrip d) := by
  let z₀ : ℂ := (c+d)/2
  have hec : z₀-c = -(c-d)/2 := by dsimp [z₀]; ring
  have hed : z₀-d = (c-d)/2 := by dsimp [z₀]; ring
  have hbc : z₀-c ∈ ball (0 : ℂ) 2 := by
    simp only [mem_ball, dist_zero_right, hec, norm_div, norm_neg]
    norm_num
    linarith
  have hbd : z₀-d ∈ ball (0 : ℂ) 2 := by
    simp only [mem_ball, dist_zero_right, hed, norm_div]
    norm_num
    linarith
  have hsc : z₀ ∈ chartStrip c := by
    change |(z₀-c).im| < 1
    rw [hec]
    simp only [Complex.div_ofNat_im, Complex.neg_im, abs_div, abs_neg]
    norm_num
    change |c.im-d.im|/2<1
    linarith
  have hsd : z₀ ∈ chartStrip d := by
    change |(z₀-d).im| < 1
    rw [hed]
    simp only [Complex.div_ofNat_im, abs_div]
    norm_num
    change |c.im-d.im|/2<1
    linarith
  have hn₁ : ∀ᶠ z in 𝓝 z₀, z-c ∈ ball (0 : ℂ) 2 :=
    (continuousAt_id.sub continuousAt_const).eventually (isOpen_ball.mem_nhds hbc)
  have hn₂ : ∀ᶠ z in 𝓝 z₀, z-d ∈ ball (0 : ℂ) 2 :=
    (continuousAt_id.sub continuousAt_const).eventually (isOpen_ball.mem_nhds hbd)
  have hn₃ : ∀ᶠ z in 𝓝 z₀, z ∈ chartStrip c := (chartStrip_isOpen c).mem_nhds hsc
  have hn₄ : ∀ᶠ z in 𝓝 z₀, z ∈ chartStrip d := (chartStrip_isOpen d).mem_nhds hsd
  have heq : patch H c =ᶠ[𝓝 z₀] patch H d := by
    filter_upwards [hn₁,hn₂,hn₃,hn₄] with z h₁ h₂ h₃ h₄
    rw [patch_eq_of_small H c z hpc h₁ h₃, patch_eq_of_small H d z hpd h₂ h₄]
  exact ((patch_analytic H c hac hpc).mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    ((patch_analytic H d had hpd).mono inter_subset_right)
    ((chartStrip_convex c).inter (chartStrip_convex d)).isPreconnected ⟨hsc,hsd⟩ heq

end Kneser.PeriodicChartGluing
end
