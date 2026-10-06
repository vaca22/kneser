import Kneser.ActualReflectedLensMidline
import Kneser.ActualInverseLensRootLimit

/-! The actual logarithmic model extends holomorphically across the real
split interval. Its true inverse step identity extends there by
continuity from the already proved nonreal identity. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.RealLensModelStep
open Set Metric Complex Filter
open Kneser.ActualLensModel Kneser.ActualLensGeometry Kneser.GrowingBandGeometry
open Kneser.ActualReflectedLensModel Kneser.ActualReflectedLensMidline
open Kneser.ApolloniusGeometry Kneser.ExponentialUnfolding
open Kneser.PositiveKoenigsOrbit Kneser.EvenPreparedOrbitDiscs
open scoped Topology

theorem analyticAt_lensModel_real_between (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (har : a<r) (hrb : r<b) :
    AnalyticAt ℂ (lensModel s a b θ e₁ e₂) (r:ℂ) := by
  have hn : (r:ℂ)-(b:ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr (ne_of_lt hrb)
  have hq : AnalyticAt ℂ (fun u : ℂ => -crossRatio a b u) (r:ℂ) :=
    (((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hn).neg)
  have hqv : -crossRatio a b (r:ℂ)=((-(r-a)/(r-b):ℝ):ℂ) := by
    simp only [crossRatio]
    push_cast
    ring
  have hslit : -crossRatio a b (r:ℂ)∈Complex.slitPlane := by
    rw [hqv]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp only [Complex.ofReal_re]; exact div_pos_of_neg_of_neg (by linarith) (by linarith)))
  have ht : AnalyticAt ℂ (bandTime a b θ) (r:ℂ) :=
    (((hq.clog hslit).sub analyticAt_const).neg).div_const
  have hbarg : (b:ℂ)-(r:ℂ)∈Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [Complex.sub_re,Complex.ofReal_re] using sub_pos.mpr hrb
  have hl : AnalyticAt ℂ (fun u : ℂ => Complex.log ((b:ℂ)-u)) (r:ℂ) :=
    (analyticAt_const.sub analyticAt_id).clog hbarg
  have hp : AnalyticAt ℂ (fun u : ℂ => e₁*u+e₂*u^2) (r:ℂ) :=
    (analyticAt_const.mul analyticAt_id).add (analyticAt_const.mul (analyticAt_id.pow 2))
  have hsum : AnalyticAt ℂ (fun u : ℂ => bandTime a b θ u+
    residueSum s a b*Complex.log ((b:ℂ)-u)+(e₁*u+e₂*u^2)) (r:ℂ) :=
    (ht.add (analyticAt_const.mul hl)).add hp
  convert hsum using 1
  funext u
  dsimp only [lensModel]
  ring

theorem continuousAt_physical_inverse_real (s r : ℝ) (hr : -1<r) :
    ContinuousAt (inverseStep s) (r:ℂ) := by
  have hslit : 1+(r:ℂ)∈Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    linarith
  have hc : AnalyticAt ℂ (fun u : ℂ => Complex.log (1+u)+(s:ℂ)) (r:ℂ) :=
    ((analyticAt_const.add analyticAt_id).clog hslit).add analyticAt_const
  have hd : AnalyticAt ℂ (fun u : ℂ => (Complex.log (1+u)+(s:ℂ))/(1-(s:ℂ))) (r:ℂ) := hc.div_const
  convert hd.continuousAt using 1
  funext u
  rw [inverseStep_formula]
  push_cast
  rfl

theorem upper_approach (r : ℝ) :
    Tendsto (fun n : ℕ => (r:ℂ)+I*((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝 (r:ℂ)) := by
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  change Tendsto (fun n : ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝 (0:ℂ)) at hc
  simpa using (hc.const_mul I).const_add (r:ℂ)

/-- A real step follows from the genuine nonreal formula and actual local
continuity of its residual, rather than any imposed real correction. -/
theorem inverse_real_one_step_of_continuity
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r η : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (ha : -1<a) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hrη : ‖(r:ℂ)‖<η)
    (hΓ : AnalyticAt ℂ Γ (Complex.sqrt (s:ℂ),inverseStep s r))
    (hstep : ∀ u : ℂ, ‖u‖<η → u.im≠0 →
      lensModel s a b θ e₁ e₂ (inverseStep s u)-lensModel s a b θ e₁ e₂ u+1=
        -descendedTerm A B Γ 2 (inverseStep s u) s 0) :
    lensModel s a b θ e₁ e₂ (inverseStep s r)-lensModel s a b θ e₁ e₂ r+1=
      -descendedTerm A B Γ 2 (inverseStep s r) s 0 := by
  have hgr := inverseReal_between s a b r hs1 ha hfa hfb har hrb
  have he := inverseStep_ofReal s r (by linarith)
  have hcG := continuousAt_physical_inverse_real s r (by linarith)
  have hcM := (analyticAt_lensModel_real_between s a b θ r e₁ e₂ har hrb).continuousAt
  have hcMG : ContinuousAt (fun u : ℂ => lensModel s a b θ e₁ e₂ (inverseStep s u)) (r:ℂ) := by
    have hh := (analyticAt_lensModel_real_between s a b θ (inverseReal s r) e₁ e₂ hgr.1 hgr.2).continuousAt
    rw [←he] at hh
    exact hh.comp hcG
  have hcR : ContinuousAt (fun u : ℂ => descendedTerm A B Γ 2 (inverseStep s u) s 0) (r:ℂ) := by
    have hq : ContinuousAt (fun u : ℂ =>
      ((inverseStep s u)^2-A s*inverseStep s u+B s)^2) (r:ℂ) := by fun_prop
    have hgp : ContinuousAt (fun u : ℂ => (Complex.sqrt (s:ℂ),inverseStep s u)) (r:ℂ) :=
      continuousAt_const.prodMk hcG
    have hg : ContinuousAt (fun u : ℂ => Γ (Complex.sqrt (s:ℂ),inverseStep s u)) (r:ℂ) :=
      hΓ.continuousAt.comp (f := fun u : ℂ => (Complex.sqrt (s:ℂ),inverseStep s u)) hgp
    simp only [descendedTerm,splitTerm,orbit_zero,Kneser.AnalyticEvenDescent.square_sqrt,
      Kneser.ExponentialRootPolynomial.rootPolynomial]
    convert hq.mul hg using 1
    funext u
    rfl
  let G : ℂ → ℂ := fun u => lensModel s a b θ e₁ e₂ (inverseStep s u)-lensModel s a b θ e₁ e₂ u+1+
    descendedTerm A B Γ 2 (inverseStep s u) s 0
  have hc : ContinuousAt G (r:ℂ) := ((hcMG.sub hcM).add continuousAt_const).add hcR
  have hseq := upper_approach r
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖(r:ℂ)+I*((1/((n:ℝ)+1):ℝ):ℂ)‖<η :=
    (continuous_norm.continuousAt.tendsto.comp hseq).eventually (gt_mem_nhds hrη)
  have hzero : ∀ᶠ n : ℕ in atTop, G ((r:ℂ)+I*((1/((n:ℝ)+1):ℝ):ℂ))=0 := by
    filter_upwards [hsmall] with n hn
    have him : ((r:ℂ)+I*((1/((n:ℝ)+1):ℝ):ℂ)).im≠0 := by
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
        Complex.I_im,Complex.ofReal_re,mul_zero,zero_mul,mul_one,zero_add]
      positivity
    have hh := hstep _ hn him
    dsimp [G]
    linear_combination hh
  have hz : G (r:ℂ)=0 := tendsto_nhds_unique (hc.tendsto.comp hseq)
    ((tendsto_const_nhds (x:=(0:ℂ))).congr' (hzero.mono fun n hn => hn.symm))
  dsimp [G] at hz
  linear_combination hz

/-- The actual preparation supplies the residual holomorphy needed in the
continuity extension. Thus the real one-step identity has no branch,
residual-continuity or polynomial-reality premise. -/
theorem exists_actual_inverse_real_one_step
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0<η ∧ η≤1/4 ∧ 0<s₀ ∧ s₀≤η/8 ∧ s₀≤1/2 ∧
      ∀ s a b : ℝ, 0<s → s<s₀ → |a|<η → |b|<η → a<0 → 0<b →
        unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
        ∀ r : ℝ, a<r → r<b → ‖(r:ℂ)‖≤η/4 →
          lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) (inverseStep s r)-
            lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) r+1=
              -descendedTerm A B Γ 2 (inverseStep s r) s 0 := by
  obtain ⟨η₁,s₁,hη₁,hη₁q,hs₁,_hs₁η,hs₁h,hstep⟩ :=
    exists_actual_inverse_lensModel_one_step U H e₁ e₂ A B K F Γ hdata
  rcases hdata with ⟨_hU,_hU0,_hUd,_hH,_hHne,_hHlog,_hA,_hB,_hA0,_hB0,
    _he₁,_he₂,_hF,hΓ0,_htail⟩
  obtain ⟨δ,hδ,hΓball⟩ := Metric.eventually_nhds_iff.mp hΓ0.eventually_analyticAt
  let η := min (η₁/2) (δ/4)
  have hη : 0<η := by dsimp [η]; positivity
  have hη₁' : η≤η₁/2 := min_le_left _ _
  have hηδ : η≤δ/4 := min_le_right _ _
  have hηq : η≤1/4 := by linarith
  let s₀ := min s₁ (min (η/8) (η^2))
  refine ⟨η,s₀,hη,hηq,by dsimp [s₀]; positivity,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_left _ _).trans hs₁h,?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb r har hrb hrnorm
  have hss₁ : s<s₁ := hss.trans_le (min_le_left _ _)
  have hsη : s≤η/8 := hss.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsηsq : s<η^2 := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hs1 : s<1 := by linarith [hss₁.trans_le hs₁h]
  have haa : -1<a := by have hh := (abs_lt.mp ha).1; linarith
  have hgsmall := inverseStep_small η s r hη (by linarith) hs.le hsη hrnorm
  have hxsq : ‖Complex.sqrt (s:ℂ)‖^2=s := by
    rw [←norm_pow,Kneser.AnalyticEvenDescent.square_sqrt,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hs]
  have hxn : ‖Complex.sqrt (s:ℂ)‖<η := by nlinarith [norm_nonneg (Complex.sqrt (s:ℂ))]
  have hΓpoint : AnalyticAt ℂ Γ (Complex.sqrt (s:ℂ),inverseStep s r) := by
    apply hΓball
    rw [dist_zero_right,Prod.norm_def]
    exact max_lt (by linarith) (by linarith)
  apply inverse_real_one_step_of_continuity A B Γ s a b (-Real.log (multiplier s a)) r
    (η₁/4) (e₁ s) (e₂ s) hs1 haa har hrb hfa hfb (by linarith) hΓpoint
  intro u hu him
  exact (hstep s a b hs hss₁ (ha.trans_le (by linarith)) (hb.trans_le (by linarith))
    ha0 hb0 hfa hfb u hu.le him).2.2.2

end Kneser.RealLensModelStep
end
