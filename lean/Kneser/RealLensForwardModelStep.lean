import Kneser.RealLensModelStep

/-! The genuine forward model step across the actual real split interval. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.RealLensForwardModelStep
open Set Metric Complex Filter
open Kneser.ActualLensModel Kneser.GrowingBandGeometry Kneser.RealLensMidline
open Kneser.RealLensModelStep Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open scoped Topology

theorem forward_real_one_step_of_continuity
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r η : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hrη : ‖(r:ℂ)‖<η) (hΓ : AnalyticAt ℂ Γ (Complex.sqrt (s:ℂ),(r:ℂ)))
    (hstep : ∀ u : ℂ, ‖u‖<η → u.im≠0 →
      lensModel s a b θ e₁ e₂ (unfolding s u)-lensModel s a b θ e₁ e₂ u-1=
        descendedTerm A B Γ 2 u s 0) :
    lensModel s a b θ e₁ e₂ (unfolding s r)-lensModel s a b θ e₁ e₂ r-1=
      descendedTerm A B Γ 2 r s 0 := by
  have hfr := unfolding_real_between s a b r hs1 hfa hfb har hrb
  have hcF : ContinuousAt (unfolding (s:ℂ)) (r:ℂ) :=
    (hasDerivAt_unfolding_spatial s r).continuousAt
  have hcM := (analyticAt_lensModel_real_between s a b θ r e₁ e₂ har hrb).continuousAt
  have hcMF : ContinuousAt (fun u : ℂ => lensModel s a b θ e₁ e₂ (unfolding s u)) (r:ℂ) := by
    have hh := (analyticAt_lensModel_real_between s a b θ (realStep s r) e₁ e₂ hfr.1 hfr.2).continuousAt
    rw [←unfolding_ofReal] at hh
    exact hh.comp (f := unfolding (s:ℂ)) hcF
  have hcR : ContinuousAt (fun u : ℂ => descendedTerm A B Γ 2 u s 0) (r:ℂ) := by
    have hq : ContinuousAt (fun u : ℂ => (u^2-A s*u+B s)^2) (r:ℂ) := by fun_prop
    have hgp : ContinuousAt (fun u : ℂ => (Complex.sqrt (s:ℂ),u)) (r:ℂ) :=
      continuousAt_const.prodMk continuousAt_id
    have hg : ContinuousAt (fun u : ℂ => Γ (Complex.sqrt (s:ℂ),u)) (r:ℂ) :=
      hΓ.continuousAt.comp (f := fun u : ℂ => (Complex.sqrt (s:ℂ),u)) hgp
    simp only [descendedTerm,splitTerm,orbit_zero,Kneser.AnalyticEvenDescent.square_sqrt,
      Kneser.ExponentialRootPolynomial.rootPolynomial]
    convert hq.mul hg using 1
    funext u
    rfl
  let G : ℂ → ℂ := fun u => lensModel s a b θ e₁ e₂ (unfolding s u)-lensModel s a b θ e₁ e₂ u-1-
    descendedTerm A B Γ 2 u s 0
  have hc : ContinuousAt G (r:ℂ) := ((hcMF.sub hcM).sub continuousAt_const).sub hcR
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

end Kneser.RealLensForwardModelStep
end
