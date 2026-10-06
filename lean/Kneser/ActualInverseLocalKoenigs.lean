import Kneser.QuadraticLocalKoenigs
import Kneser.ActualReflectedLensModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! A normalized actual Koenigs germ for the principal inverse at the
true repelling fixed point. Its local inverse is a genuine Poincare seed
for the entire exponential unfolding. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.ActualInverseLocalKoenigs
open Set Metric Filter Complex
open Kneser.ExponentialUnfolding Kneser.ActualReflectedLensModel
open Kneser.PositiveKoenigsOrbit Kneser.QuadraticLocalKoenigs
open scoped Topology

def inverseMultiplier (s b : ℝ) : ℝ := (multiplier s b)⁻¹

def inverseKoenigs (s b : ℝ) : ℂ → ℂ := value (inverseStep s) (b:ℂ) (inverseMultiplier s b)

theorem actual_root_log (s b : ℝ) (hroot : unfolding s b=(b:ℂ)) :
    Real.log (1+b)= -s+(1-s)*b := by
  have he : Real.exp (-s+(1-s)*b)=1+b := by
    have hh := congrArg Complex.re hroot
    have hc : -(s:ℂ)+(1-(s:ℂ))*(b:ℂ)=((-s+(1-s)*b:ℝ):ℂ) := by push_cast; ring
    simp only [unfolding,hc,Complex.sub_re,Complex.one_re,Complex.exp_ofReal_re,Complex.ofReal_re] at hh
    linarith
  rw [←he,Real.log_exp]

theorem actual_right_multiplier (s b : ℝ) (hb : 0<b) (hroot : unfolding s b=(b:ℂ)) :
    1<multiplier s b := by
  have hlog := Real.log_pos (by linarith : 1<1+b)
  rw [actual_root_log s b hroot] at hlog
  unfold multiplier
  nlinarith

theorem inverseStep_at_root (s b : ℝ) (hs1 : s<1) (hb : 0<b) (hroot : unfolding s b=(b:ℂ)) :
    inverseStep s b=(b:ℂ) := by
  rw [inverseStep_formula,←Complex.ofReal_one,←Complex.ofReal_add,←Complex.ofReal_log (by linarith : (0:ℝ)≤1+b)]
  have hh := actual_root_log s b hroot
  rw [hh]
  push_cast
  have hsne : (1-(s:ℂ))≠0 := by exact_mod_cast (by linarith : 1-s≠0)
  field_simp
  push_cast
  ring

theorem unfolding_inverseStep_of_ne (s : ℝ) (u : ℂ) (hs1 : s<1) (hu : 1+u≠0) :
    unfolding s (inverseStep s u)=u := by
  have hd : (1-(s:ℂ))≠0 := by exact_mod_cast (by linarith : 1-s≠0)
  rw [inverseStep_formula]
  unfold unfolding
  have he : -(s:ℂ)+(1-(s:ℂ))*((Complex.log (1+u)+(s:ℂ))/((1-s:ℝ):ℂ))=Complex.log (1+u) := by
    push_cast
    field_simp
    ring
  rw [he,Complex.exp_log hu]
  ring

theorem inverseStep_analytic_ball (s b : ℝ) (hb : 0<b) :
    AnalyticOnNhd ℂ (inverseStep s) (ball (b:ℂ) (1/2)) := by
  intro u hu
  have hn : ‖u-(b:ℂ)‖<1/2 := by simpa only [mem_ball,dist_eq_norm] using hu
  have hlo := (abs_le.mp (Complex.abs_re_le_norm (u-(b:ℂ)))).1
  have hp : 0<(1+u).re := by simp only [Complex.sub_re,Complex.ofReal_re,Complex.add_re,Complex.one_re] at hlo ⊢; linarith
  have harg : AnalyticAt ℂ (fun z : ℂ => 1+z) u := analyticAt_const.add analyticAt_id
  have hh : AnalyticAt ℂ (fun z : ℂ => (Complex.log (1+z)+(s:ℂ))/((1-s:ℝ):ℂ)) u :=
    ((harg.clog (mem_slitPlane_iff.mpr (Or.inl hp))).add analyticAt_const).div_const
  convert hh using 1
  funext z
  exact inverseStep_formula s z

theorem inverseStep_quadratic_remainder (s b : ℝ) (hs : 0≤s) (hs1 : s<1/2) (hb : 0<b)
    (hroot : unfolding s b=(b:ℂ)) (u : ℂ) (hu : u∈ball (b:ℂ) (1/2)) :
    ‖inverseStep s u-(b:ℂ)-(inverseMultiplier s b:ℂ)*(u-(b:ℂ))‖≤2*‖u-(b:ℂ)‖^2 := by
  let z : ℂ := (u-(b:ℂ))/(1+(b:ℂ))
  have hn : ‖u-(b:ℂ)‖<1/2 := by simpa only [mem_ball,dist_eq_norm] using hu
  have hden : 0<1+b := by linarith
  have hnormz : ‖z‖=‖u-(b:ℂ)‖/(1+b) := by
    dsimp [z]
    rw [norm_div,←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_of_nonneg hden.le]
  have hnormzle : ‖z‖≤‖u-(b:ℂ)‖ := by
    rw [hnormz]
    exact div_le_self (norm_nonneg _) (by linarith)
  have hzsmall : ‖z‖≤1/2 := hnormzle.trans hn.le
  have hzneq : 1+z≠0 := by
    have hp : 0<(1+z).re := by
      have h := (abs_le.mp (Complex.abs_re_le_norm z)).1
      simp only [Complex.add_re,Complex.one_re]
      linarith
    intro he
    rw [he,Complex.zero_re] at hp
    linarith
  have harg : 1+u=((1+b:ℝ):ℂ)*(1+z) := by
    dsimp [z]
    push_cast
    have hbne : 1+(b:ℂ)≠0 := by exact_mod_cast (ne_of_gt hden)
    field_simp
    ring
  have hlog : Complex.log (1+u)=Complex.log ((1+b:ℝ):ℂ)+Complex.log (1+z) := by
    rw [harg]
    simpa only [Complex.ofReal_log hden.le] using Complex.log_ofReal_mul hden hzneq
  have hrem := Kneser.ParabolicInitialPetal.norm_log_one_sub_remainder (z:=-z) (by simpa only [norm_neg] using hzsmall)
  simp only [sub_neg_eq_add,←sub_eq_add_neg,norm_neg] at hrem
  have hgroot := inverseStep_at_root s b (by linarith) hb hroot
  have he' : inverseStep s u-inverseStep s (b:ℂ)-(inverseMultiplier s b:ℂ)*(u-(b:ℂ))=
      (Complex.log (1+z)-z)/((1-s:ℝ):ℂ) := by
    rw [inverseStep_formula,inverseStep_formula,hlog]
    dsimp [inverseMultiplier,multiplier,z]
    push_cast
    have hd : 1-(s:ℂ)≠0 := by exact_mod_cast (by linarith : 1-s≠0)
    have hbne : 1+(b:ℂ)≠0 := by exact_mod_cast (ne_of_gt hden)
    field_simp
    ring
  have he := he'
  rw [hgroot] at he
  rw [he,norm_div,Complex.norm_of_nonneg (by linarith : 0≤1-s)]
  calc
    _ ≤ ‖z‖^2/(1-s) := div_le_div_of_nonneg_right hrem (by linarith)
    _ ≤ ‖u-(b:ℂ)‖^2/(1-s) := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hnormzle 2) (by linarith)
    _ ≤ 2*‖u-(b:ℂ)‖^2 := by
      apply (div_le_iff₀ (by linarith : 0<1-s)).mpr
      nlinarith [sq_nonneg ‖u-(b:ℂ)‖]

/-- Actual inverse Koenigs data are constructed at every true repelling
root of a sufficiently small positive parameter. -/
theorem exists_actual_inverse_local_koenigs (s b : ℝ) (hs : 0<s) (hs1 : s<1/2) (hb : 0<b)
    (hroot : unfolding s b=(b:ℂ)) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/2 ∧
      AnalyticOnNhd ℂ (inverseKoenigs s b) (ball (b:ℂ) δ) ∧
      inverseKoenigs s b b=0 ∧ HasDerivAt (inverseKoenigs s b) 1 (b:ℂ) ∧
      ∀ u∈ball (b:ℂ) δ, inverseStep s u∈ball (b:ℂ) δ ∧
        inverseKoenigs s b (inverseStep s u)=(inverseMultiplier s b:ℂ)*inverseKoenigs s b u ∧
        Summable (fun n => ‖increment (inverseStep s) (b:ℂ) (inverseMultiplier s b) u n‖) ∧
        Tendsto (approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) u) atTop (𝓝 (inverseKoenigs s b u)) := by
  have hmult := actual_right_multiplier s b hb hroot
  have hμ : 0 < inverseMultiplier s b := inv_pos.mpr (by linarith)
  have hμ1 : inverseMultiplier s b < 1 := (inv_lt_one₀ (by linarith : 0 < multiplier s b)).mpr hmult
  exact exists_normalized_local_koenigs (inverseStep s) (b:ℂ) (inverseMultiplier s b) (1/2) hμ hμ1
    (by norm_num) (inverseStep_analytic_ball s b hb) (inverseStep_at_root s b (by linarith) hb hroot)
    (inverseStep_quadratic_remainder s b hs.le hs1 hb hroot)

/-- The actual local inverse germ provides the exact scaling identity
needed by the entire Poincare construction. -/
theorem exists_actual_poincare_seed (s b : ℝ) (hs : 0<s) (hs1 : s<1/2) (hb : 0<b)
    (hroot : unfolding s b=(b:ℂ)) :
    ∃ H : ℂ → ℂ, ∃ r : ℝ, 0<r ∧
      AnalyticOnNhd ℂ H (ball 0 r) ∧ H 0=(b:ℂ) ∧ HasDerivAt H 1 0 ∧
      ∀ z∈ball (0:ℂ) r, unfolding s (H ((inverseMultiplier s b:ℂ)*z))=H z := by
  obtain ⟨δ,hδ,_hδq,hκ,hκ0,hκd,hlocal⟩ := exists_actual_inverse_local_koenigs s b hs hs1 hb hroot
  have hκa := hκ (b:ℂ) (mem_ball_self hδ)
  have hκne : deriv (inverseKoenigs s b) (b:ℂ)≠0 := by rw [hκd.deriv]; exact one_ne_zero
  let H := hκa.hasStrictDerivAt.localInverse _ _ _ hκne
  have hHa : AnalyticAt ℂ H 0 := by simpa only [hκ0] using hκa.analyticAt_localInverse hκne
  have hHl : ∀ᶠ u : ℂ in 𝓝 (b:ℂ), H (inverseKoenigs s b u)=u := HasStrictDerivAt.eventually_left_inverse _ _
  have hHr : ∀ᶠ z : ℂ in 𝓝 0, inverseKoenigs s b (H z)=z := by
    simpa only [hκ0] using (HasStrictDerivAt.eventually_right_inverse hκa.hasStrictDerivAt hκne)
  have hH0 : H 0=(b:ℂ) := by
    have hh : (fun u => H (inverseKoenigs s b u))=ᶠ[𝓝 (b:ℂ)] id := hHl
    simpa only [hκ0,id_eq] using hh.eq_of_nhds
  have hHd : HasDerivAt H 1 0 := by
    have hh := (hκa.hasStrictDerivAt.to_localInverse hκne).hasDerivAt
    simpa only [hκ0,hκd.deriv,inv_one] using hh
  have hGcont := (inverseStep_analytic_ball s b hb (b:ℂ) (mem_ball_self (by norm_num))).continuousAt
  have hHcont : Tendsto H (𝓝 0) (𝓝 (b:ℂ)) := by simpa only [hH0] using hHa.continuousAt.tendsto
  have hGcontH : Tendsto (fun z => inverseStep s (H z)) (𝓝 0) (𝓝 (b:ℂ)) := by
    simpa only [Function.comp_def,inverseStep_at_root s b (by linarith) hb hroot] using hGcont.tendsto.comp hHcont
  have hnonzero : ∀ᶠ u : ℂ in 𝓝 (b:ℂ), 1+u≠0 :=
    (show ContinuousAt (fun u : ℂ => 1+u) (b:ℂ) from continuousAt_const.add continuousAt_id).eventually_ne
      (by change 1+(b:ℂ)≠0; exact_mod_cast (by linarith : (1+b:ℝ)≠0))
  have hstep : ∀ᶠ z : ℂ in 𝓝 0,
      unfolding s (H ((inverseMultiplier s b:ℂ)*z))=H z := by
    filter_upwards [hHcont.eventually (isOpen_ball.mem_nhds (mem_ball_self hδ : (b:ℂ)∈ball (b:ℂ) δ)),
      hHr,hGcontH.eventually hHl,hHcont.eventually hnonzero] with z hz hzr hzl hzn
    have hlin := (hlocal (H z) hz).2.1
    rw [hzr] at hlin
    rw [hlin] at hzl
    rw [hzl]
    exact unfolding_inverseStep_of_ne s (H z) (by linarith) hzn
  have hboth : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ H z ∧
      unfolding s (H ((inverseMultiplier s b:ℂ)*z))=H z := hHa.eventually_analyticAt.and hstep
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hboth
  exact ⟨H,r,hr,fun z hz => (hball hz).1,hH0,hHd,fun z hz => (hball hz).2⟩

end Kneser.ActualInverseLocalKoenigs
end
