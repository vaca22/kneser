import Kneser.InverseKoenigsEntry
import Kneser.PoincareTimeChart

/-! The actual Poincare seed retains its genuine Koenigs inverse identities. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualInversePoincareSeed
open Set Metric Filter Complex
open Kneser.ActualInverseLocalKoenigs Kneser.InverseKoenigsEntry
open Kneser.ExponentialUnfolding Kneser.ActualReflectedLensModel
open scoped Topology

theorem exists_seed_with_inverse (s b : ℝ) (hs : 0<s) (hs1 : s<1/2) (hb : 0<b)
    (hroot : unfolding s b=(b:ℂ)) :
    ∃ H : ℂ → ℂ, ∃ r : ℝ, 0<r ∧
      AnalyticOnNhd ℂ H (ball 0 r) ∧ H 0=(b:ℂ) ∧ HasDerivAt H 1 0 ∧
      (∀ᶠ u : ℂ in 𝓝 (b:ℂ), H (inverseKoenigs s b u)=u) ∧
      (∀ᶠ z : ℂ in 𝓝 0, inverseKoenigs s b (H z)=z) ∧
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
  exact ⟨H,r,hr,fun z hz => (hball hz).1,hH0,hHd,hHl,hHr,fun z hz => (hball hz).2⟩


end Kneser.ActualInversePoincareSeed
end
