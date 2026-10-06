import Kneser.ActualAnchorKoenigsIdentification
import Kneser.ActualKoenigsUpperBranch

/-! The actual Koenigs derivative is nonzero throughout its genuine
attracting basin. In particular the actual real normalization anchor has
an analytic Koenigs time with a nonzero spatial derivative. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.ActualKoenigsJacobian
open Filter Set Metric Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.PositiveKoenigsAbel Kneser.ActualKoenigsUpperBranch
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualKoenigsRealPhase Kneser.ActualAnchorKoenigsIdentification
open scoped Topology

theorem actual_orbit_deriv_ne_zero (s : ℂ) (hs : s≠1) (u : ℂ) (N : ℕ) :
    deriv (fun v : ℂ => orbit v s N) u≠0 := by
  induction N with
  | zero => simpa only [orbit_zero,deriv_id''] using (one_ne_zero : (1:ℂ)≠0)
  | succ N ih =>
    have ho := (Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s N u).hasDerivAt
    have hd := (hasDerivAt_unfolding_spatial s (orbit u s N)).comp u ho
    have he := hd.deriv
    have hfun : (fun v : ℂ => unfolding s (orbit v s N))=(fun v : ℂ => orbit v s (N+1)) := by
      funext v
      exact (orbit_succ v s N).symm
    change deriv (fun v : ℂ => unfolding s (orbit v s N)) u = _ at he
    rw [hfun] at he
    rw [he]
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero.mpr hs.symm)) ih

/-- A true orbit limit suffices. Neither a derivative nor a neighborhood
summability estimate is assumed. -/
theorem deriv_koenigsValue_ne_zero_of_true_limit (s a : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ))) :
    deriv (koenigsValue s a) u≠0 := by
  obtain ⟨δ,hδ,hhol,_hz,hder,hlocal⟩ := exists_actual_local_koenigs s a hs hs1 ha ha0 hfa hμ hμ1
  have hKr := hhol (a:ℂ) (mem_ball_self hδ)
  have hKd : AnalyticAt ℂ (deriv (koenigsValue s a)) (a:ℂ) := by
    exact ((ContinuousLinearMap.apply ℂ ℂ (1:ℂ)).analyticAt _).comp hKr.fderiv
  have hnear : ∀ᶠ v : ℂ in 𝓝 (a:ℂ), deriv (koenigsValue s a) v≠0 :=
    hKd.continuousAt.eventually_ne (by rw [hder.deriv]; exact one_ne_zero)
  obtain ⟨N,hN,hNd⟩ := ((hlim.eventually (ball_mem_nhds (a:ℂ) hδ)).and (hlim.eventually hnear)).exists
  have ho : AnalyticAt ℂ (fun v : ℂ => orbit v s N) u :=
    (Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s N).differentiableOn.analyticAt Filter.univ_mem
  have hentry : ∀ᶠ v : ℂ in 𝓝 u, orbit v s N∈ball (a:ℂ) δ :=
    ho.continuousAt.eventually (isOpen_ball.mem_nhds hN)
  have hsums : ∀ᶠ v : ℂ in 𝓝 u, Summable (fun k => ‖increment s a v k‖) := by
    filter_upwards [hentry] with v hv
    exact summable_increment_from_entry s a v N (ne_of_gt hμ) (hlocal _ hv).1
  have he : (fun v : ℂ => koenigsValue s a (orbit v s N))=ᶠ[𝓝 u]
      (fun v : ℂ => (multiplier s a:ℂ)^N*koenigsValue s a v) := by
    filter_upwards [hsums] with v hv
    exact koenigsValue_iterate s a v (ne_of_gt hμ) hv N
  have hKu := analyticAt_koenigsValue_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim
  have hdl := (hhol _ hN).differentiableAt.hasDerivAt.comp u ho.differentiableAt.hasDerivAt
  have hdr := hKu.differentiableAt.hasDerivAt.const_mul ((multiplier s a:ℂ)^N)
  have hde := hdl.unique (hdr.congr_of_eventuallyEq he)
  intro hzero
  have hos : (s:ℂ)≠1 := by exact_mod_cast ne_of_lt hs1
  have hprod := mul_ne_zero hNd (actual_orbit_deriv_ne_zero s hos u N)
  rw [hzero,mul_zero] at hde
  exact hprod hde

theorem koenigsTime_analytic_nonzero_of_true_left_limit (s a : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ))) (hu : u.re<a) :
    AnalyticAt ℂ (koenigsTime s a) u ∧ deriv (koenigsTime s a) u≠0 := by
  have hk := analyticAt_koenigsValue_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim
  have hsums := actual_koenigs_sum_of_orbit_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim
  obtain ⟨hne,hslit⟩ := actual_koenigs_branch s a u hs hs1 ha ha0 hfa hμ hμ1 hsums hlim hu
  have hlog : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  have hd := (hk.differentiableAt.hasDerivAt.neg.clog hslit).div_const (Real.log (multiplier s a):ℂ)
  refine ⟨by exact (hk.neg.clog hslit).div_const,?_⟩
  change deriv (fun x : ℂ => Complex.log ((-koenigsValue s a) x) / (Real.log (multiplier s a):ℂ)) u≠0
  rw [hd.deriv]
  exact div_ne_zero (div_ne_zero (neg_ne_zero.mpr (deriv_koenigsValue_ne_zero_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim))
    (neg_ne_zero.mpr hne)) hlog

/-- Every real point strictly to the left of the actual attracting root,
including the paper's anchor, has a genuine analytic invertible chart. -/
theorem koenigsTime_analytic_nonzero_real_left (s a r : ℝ)
    (hs : 0<s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hr : r<a) :
    AnalyticAt ℂ (koenigsTime s a) (r:ℂ) ∧ deriv (koenigsTime s a) (r:ℂ)≠0 := by
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hs]
  have hμ1' : multiplier s a<1 := hμ1
  exact koenigsTime_analytic_nonzero_of_true_left_limit s a r hs.le hs1 ha ha0 hfa hμ hμ1'
    (real_left_orbit_limit s a r hs1 ha hfa hμ.le hμ1' hr) (by simpa using hr)

/-- The true Koenigs time, centered at a real point on the left, has an
actual analytic inverse germ and both inverse identities. -/
theorem exists_actual_anchor_inverse_germ (s a r : ℝ)
    (hs : 0<s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hr : r<a) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0=(r:ℂ) ∧
      (∀ᶠ z : ℂ in 𝓝 0, koenigsTime s a (R z)-koenigsTime s a r=z) ∧
      (∀ᶠ u : ℂ in 𝓝 (r:ℂ), R (koenigsTime s a u-koenigsTime s a r)=u) := by
  obtain ⟨hk,hd⟩ := koenigsTime_analytic_nonzero_real_left s a r hs hs1 ha ha0 hfa hr
  let A : ℂ → ℂ := fun u => koenigsTime s a u-koenigsTime s a r
  have hA : AnalyticAt ℂ A (r:ℂ) := hk.sub analyticAt_const
  have hAd : deriv A (r:ℂ)≠0 := by
    rw [show deriv A (r:ℂ)=deriv (koenigsTime s a) (r:ℂ) by exact (hk.differentiableAt.hasDerivAt.sub_const _).deriv]
    exact hd
  let R := hA.hasStrictDerivAt.localInverse _ _ _ hAd
  have hzero : A (r:ℂ)=0 := sub_self _
  have hRa : AnalyticAt ℂ R 0 := by
    simpa only [hzero] using hA.analyticAt_localInverse hAd
  have hleft : ∀ᶠ u : ℂ in 𝓝 (r:ℂ), R (A u)=u := HasStrictDerivAt.eventually_left_inverse _ _
  have hright : ∀ᶠ z : ℂ in 𝓝 0, A (R z)=z := by
    simpa only [hzero] using (HasStrictDerivAt.eventually_right_inverse hA.hasStrictDerivAt hAd)
  have hRzero : R 0=(r:ℂ) := by
    have heq : (fun u : ℂ => R (A u))=ᶠ[𝓝 (r:ℂ)] id := hleft
    simpa only [hzero,id_eq] using heq.eq_of_nhds
  exact ⟨R,hRa,hRzero,hright,hleft⟩

end Kneser.ActualKoenigsJacobian
end
