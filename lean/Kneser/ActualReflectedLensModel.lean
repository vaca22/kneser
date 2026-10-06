import Kneser.ActualLensModel
import Kneser.ActualLensGeometry

/-! The true principal physical inverse preserves each nonreal half-plane.
Its lens-model step and real drift are derived from the actual forward
identities at the inverse point. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualReflectedLensModel
open Filter Set Metric Complex
open Kneser.ExponentialUnfolding Kneser.RepellingExponentialOrbit
open Kneser.ActualLensModel Kneser.ActualLensGeometry
open Kneser.ReflectedOrbitChainCoefficient Kneser.EvenPreparedOrbitDiscs
open Kneser.GrowingBandGeometry Kneser.RealExponentialPetal
open scoped Topology

def inverseStep (s : ℝ) (u : ℂ) : ℂ := -reflectedInverse (s:ℂ) (-u)

theorem inverseStep_formula (s : ℝ) (u : ℂ) :
    inverseStep s u=(Complex.log (1+u)+(s:ℂ))/((1-s:ℝ):ℂ) := by
  simp only [inverseStep,reflectedInverse,sub_neg_eq_add,neg_div,neg_neg,Complex.ofReal_sub,Complex.ofReal_one]

theorem unfolding_inverseStep (s : ℝ) (u : ℂ) (hs : s<1) (hu : ‖u‖<1) :
    unfolding (s:ℂ) (inverseStep s u)=u := by
  have hsne : (s:ℂ)≠1 := by exact_mod_cast ne_of_lt hs
  simpa only [inverseStep,neg_neg] using unfolding_reflectedInverse (s:ℂ) (-u) hsne (by simpa only [norm_neg] using hu)

theorem norm_log_one_add_le (u : ℂ) (hu : ‖u‖≤1/2) : ‖Complex.log (1+u)‖≤2*‖u‖ := by
  have hr := ParabolicInitialPetal.norm_log_one_sub_remainder (z := -u) (by simpa only [norm_neg] using hu)
  simp only [sub_neg_eq_add,←sub_eq_add_neg,norm_neg] at hr
  have ht := norm_add_le (Complex.log (1+u)-u) u
  rw [sub_add_cancel] at ht
  nlinarith [norm_nonneg u]

theorem inverseStep_small (η s : ℝ) (u : ℂ) (hη : 0<η) (hη1 : η≤1)
    (hs : 0≤s) (hss : s≤η/8) (hu : ‖u‖≤η/4) :
    ‖inverseStep s u‖≤3*η/4 := by
  have hs1 : s<1 := by linarith
  have hden : 0<1-s := by linarith
  have hlog := norm_log_one_add_le u (by linarith)
  rw [inverseStep_formula,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hden]
  have hb := norm_add_le (Complex.log (1+u)) (s:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs] at hb
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem inverseStep_im (s : ℝ) (u : ℂ) :
    (inverseStep s u).im=Complex.arg (1+u)/(1-s) := by
  rw [inverseStep_formula,Complex.div_ofReal_im]
  simp only [Complex.add_im,Complex.ofReal_im,add_zero,Complex.log_im]

theorem inverseStep_im_pos (s : ℝ) (u : ℂ) (hs : s<1) (hu : 0<u.im) :
    0<(inverseStep s u).im := by
  have harg : 0<Complex.arg (1+u) := by
    have hh : 0≤Complex.arg (1+u) := Complex.arg_nonneg_iff.mpr (by simpa using hu.le)
    have hne : Complex.arg (1+u)≠0 := by
      intro he
      have hh := (Complex.arg_eq_zero_iff.mp he).2
      simp only [Complex.add_im,Complex.one_im,zero_add] at hh
      linarith
    exact lt_of_le_of_ne hh hne.symm
  rw [inverseStep_im]
  exact div_pos harg (by linarith)

theorem inverseStep_im_neg (s : ℝ) (u : ℂ) (hs : s<1) (hu : u.im<0) :
    (inverseStep s u).im<0 := by
  have harg : Complex.arg (1+u)<0 := Complex.arg_neg_iff.mpr (by simpa using hu)
  rw [inverseStep_im]
  exact div_neg_of_neg_of_pos harg (by linarith)

theorem inverseStep_im_ne_zero (s : ℝ) (u : ℂ) (hs : s<1) (hu : u.im≠0) :
    (inverseStep s u).im≠0 := by
  rcases lt_or_gt_of_ne hu with hu | hu
  · exact ne_of_lt (inverseStep_im_neg s u hs hu)
  · exact ne_of_gt (inverseStep_im_pos s u hs hu)

/-- The actual inverse lens defect is the negative true forward defect
at its inverse point. All preparation and branch inputs are constructed. -/
theorem exists_actual_inverse_lensModel_one_step (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0<η ∧ η≤1/4 ∧ 0<s₀ ∧ s₀≤η/8 ∧ s₀≤1/2 ∧
      ∀ s a b : ℝ, 0<s → s<s₀ → |a|<η → |b|<η → a<0 → 0<b →
        unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
        ∀ u : ℂ, ‖u‖≤η/4 → u.im≠0 →
          ‖inverseStep s u‖≤3*η/4 ∧ (inverseStep s u).im≠0 ∧ unfolding s (inverseStep s u)=u ∧
          lensModel s a b (-Real.log (PositiveKoenigsOrbit.multiplier s a)) (e₁ s) (e₂ s) (inverseStep s u)-
            lensModel s a b (-Real.log (PositiveKoenigsOrbit.multiplier s a)) (e₁ s) (e₂ s) u+1=
            -descendedTerm A B Γ 2 (inverseStep s u) s 0 := by
  obtain ⟨η,sf,hη,hηq,hsf,hsfq,hstep⟩ := exists_actual_lensModel_one_step U H e₁ e₂ A B K F Γ hdata
  let s₀ : ℝ := min sf (η/8)
  refine ⟨η,s₀,hη,hηq,by dsimp [s₀]; positivity,min_le_right _ _,(min_le_left _ _).trans hsfq,?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb u hu him
  have hs1 : s<1 := by have hh := hss.trans_le ((min_le_left _ _).trans hsfq); linarith
  have hsmall := inverseStep_small η s u hη (by linarith) hs.le (hss.le.trans (min_le_right _ _)) hu
  have hnorm : ‖u‖<1 := by linarith
  have hinv := unfolding_inverseStep s u hs1 hnorm
  have hsign := inverseStep_im_ne_zero s u hs1 him
  have he := hstep s a b hs (hss.trans_le (min_le_left _ _)) ha hb ha0 hb0 hfa hfb
    (inverseStep s u) (by linarith) hsign
  rw [hinv] at he
  exact ⟨hsmall,hsign,hinv,by linear_combination -he⟩

/-- The inverse step has genuine leftward logarithmic-time drift. All
quotient-disc assumptions are obtained from explicit norm estimates. -/
theorem inverse_bandTime_re_drift (Q : QuotientControl) (η s a b : ℝ) (u : ℂ)
    (hη : 0<η) (hηq : η≤1/4) (hηQ : 2*η≤Q.radius)
    (hs : 0<s) (hss : s≤η/8) (ha : |a|<η) (hb : |b|<η)
    (ha0 : a<0) (hb0 : 0<b) (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hu : ‖u‖≤η/4) (him : u.im≠0) :
    (bandTime a b (-Real.log (PositiveKoenigsOrbit.multiplier s a)) (inverseStep s u)).re+3/4≤
      (bandTime a b (-Real.log (PositiveKoenigsOrbit.multiplier s a)) u).re := by
  have hs1 : s<1/2 := by linarith
  have hab : a<b := by linarith
  have haa : -1<a := by have hh := (abs_lt.mp ha).1; linarith
  have hg := inverseStep_small η s u hη (by linarith) hs.le hss hu
  have hgi := inverseStep_im_ne_zero s u (by linarith) him
  have hinv := unfolding_inverseStep s u (by linarith) (by linarith)
  have hgn (r : ℝ) : inverseStep s u≠(r:ℂ) := by
    intro he
    apply hgi
    rw [he,Complex.ofReal_im]
  have hgap : (1-s)*(b-a)<Q.radius := by
    have hag := (abs_lt.mp ha).1
    have hbg := (abs_lt.mp hb).2
    have hm : (1-s)*(b-a)≤b-a := by nlinarith
    linarith
  have harg (r : ℝ) (hr : |r|<η) : (1-(s:ℂ))*(inverseStep s u-(r:ℂ))∈ball (0:ℂ) Q.radius := by
    have hb := norm_sub_le (inverseStep s u) (r:ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs] at hb
    have hnorm : ‖inverseStep s u-(r:ℂ)‖<Q.radius := by linarith
    have hcoeff : ‖1-(s:ℂ)‖≤1 := by
      rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<1-s)]
      linarith
    simp only [mem_ball,dist_zero_right,norm_mul]
    exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans_lt (by simpa only [one_mul] using hnorm)
  have hd := actual_bandTime_re_drift Q s a b (inverseStep s u) hs hs1 haa hab hb0 hfa hfb
    (hgn a) (hgn b) hgap (harg a ha) (harg b hb)
  have hθ := timeScale_eq_neg_log_multiplier Q s a b (by linarith) haa hab hfa hfb
  change timeScale Q ((1-s)*(b-a)) = -Real.log (PositiveKoenigsOrbit.multiplier s a) at hθ
  rw [hθ,hinv] at hd
  exact hd.2.2

end Kneser.ActualReflectedLensModel
end
