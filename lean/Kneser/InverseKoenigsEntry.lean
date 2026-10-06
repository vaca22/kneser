import Kneser.ActualInverseLocalKoenigs
import Kneser.ActualInverseLensRootLimit
import Kneser.ActualHolomorphicGrowingLens

/-! Genuine finite inverse entry propagates the normalized Koenigs orbit
sum and its holomorphy to the actual growing lens. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.InverseKoenigsEntry
open Set Metric Filter Complex
open Kneser.QuadraticLocalKoenigs Kneser.ActualInverseLocalKoenigs
open Kneser.ActualReflectedLensModel Kneser.ExponentialUnfolding
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.ActualInverseLensRootLimit Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingBandGeometry
open scoped Topology

theorem summable_backward (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ)
    (hμ : μ≠0) (hs : Summable (fun n => ‖increment f c μ (f u) n‖)) :
    Summable (fun n => ‖increment f c μ u n‖) := by
  have hn : ‖(μ:ℂ)‖≠0 := norm_ne_zero_iff.mpr (by exact_mod_cast hμ)
  have hm : Summable (fun n => ‖(μ:ℂ)‖*‖increment f c μ u (n+1)‖) := by
    simpa only [increment_forward f c μ u _ hμ,norm_mul] using hs
  exact (summable_nat_add_iff 1).mp ((summable_mul_left_iff hn).mp hm)

theorem summable_from_entry (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (N : ℕ)
    (hμ : μ≠0) (hs : Summable (fun n => ‖increment f c μ ((f^[N]) u) n‖)) :
    Summable (fun n => ‖increment f c μ u n‖) := by
  induction N with
  | zero => simpa using hs
  | succ N ih =>
    apply ih
    apply summable_backward f c μ ((f^[N]) u) hμ
    simpa only [Function.iterate_succ_apply'] using hs

theorem value_iterate (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (N : ℕ)
    (hμ : μ≠0) (hs : Summable (fun n => ‖increment f c μ u n‖)) :
    value f c μ ((f^[N]) u)=(μ:ℂ)^N*value f c μ u := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsn : Summable (fun n => ‖increment f c μ ((f^[N]) u) n‖) := by
      clear ih
      induction N with
      | zero => simpa using hs
      | succ N ih => simpa only [Function.iterate_succ_apply'] using summable_forward f c μ ((f^[N]) u) hμ ih
    rw [Function.iterate_succ_apply',functional_eq f c μ _ hμ hsn,ih,pow_succ]
    ring

theorem value_from_entry (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (N : ℕ)
    (hμ : μ≠0) (hs : Summable (fun n => ‖increment f c μ ((f^[N]) u) n‖)) :
    value f c μ u=((μ:ℂ)^N)⁻¹*value f c μ ((f^[N]) u) := by
  rw [value_iterate f c μ u N hμ (summable_from_entry f c μ u N hμ hs)]
  have hc : (μ:ℂ)≠0 := by exact_mod_cast hμ
  field_simp

theorem analyticAt_iterate (f : ℂ → ℂ) (u : ℂ) (N : ℕ)
    (hf : ∀ k : ℕ, AnalyticAt ℂ f ((f^[k]) u)) : AnalyticAt ℂ (f^[N]) u := by
  induction N with
  | zero => exact analyticAt_id
  | succ N ih => simpa only [Function.iterate_succ'] using (hf N).comp ih

theorem analyticAt_value_of_entry (f : ℂ → ℂ) (c : ℂ) (μ δ : ℝ) (u : ℂ) (N : ℕ)
    (hμ : μ≠0) (hδ : 0<δ)
    (hv : AnalyticOnNhd ℂ (value f c μ) (ball c δ))
    (hs : ∀ v∈ball c δ, Summable (fun n => ‖increment f c μ v n‖))
    (hentry : (f^[N]) u∈ball c δ)
    (hf : ∀ k : ℕ, AnalyticAt ℂ f ((f^[k]) u)) : AnalyticAt ℂ (value f c μ) u := by
  have hi := analyticAt_iterate f u N hf
  have he : ∀ᶠ v : ℂ in 𝓝 u, (f^[N]) v∈ball c δ :=
    hi.continuousAt.tendsto.eventually (isOpen_ball.mem_nhds hentry)
  have hEq : value f c μ=ᶠ[𝓝 u] (fun v => ((μ:ℂ)^N)⁻¹*value f c μ ((f^[N]) v)) := by
    filter_upwards [he] with v hvv
    exact value_from_entry f c μ v N hμ (hs _ hvv)
  exact (analyticAt_const.mul ((hv _ hentry).comp hi)).congr hEq.symm

theorem actual_inverse_sum_of_limit (s b : ℝ) (u : ℂ)
    (hs : 0<s) (hs1 : s<1/2) (hb : 0<b) (hroot : unfolding s b=(b:ℂ))
    (hlim : Tendsto (fun n => (inverseStep s)^[n] u) atTop (𝓝 (b:ℂ))) :
    Summable (fun n => ‖increment (inverseStep s) (b:ℂ) (inverseMultiplier s b) u n‖) := by
  obtain ⟨δ,hδ,_hδq,_ha,_hz,_hd,hlocal⟩ := exists_actual_inverse_local_koenigs s b hs hs1 hb hroot
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds (b:ℂ) hδ)).exists
  have hμ : inverseMultiplier s b≠0 := by
    unfold inverseMultiplier
    exact inv_ne_zero (ne_of_gt (lt_trans (by norm_num) (actual_right_multiplier s b hb hroot)))
  exact summable_from_entry _ _ _ u N hμ (hlocal _ hN).2.2.1

theorem lensControl_inverse_limit
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (Z : ℂ) (hZ : Z∈strip θ Y) :
    Tendsto (fun n => (inverseStep s)^[n] (bandChart a b θ Z)) atTop (𝓝 (b:ℂ)) := by
  have hd := (hc.true_orbits Z hZ).2.2.2.2.2
  have ht := true_inverse_orbit_tendsto_root s a b θ (bandChart a b θ Z)
    (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (fun k => ⟨(hd k).1,(hd k).2.1⟩) (fun k => (hd k).2.2.2.2)
  convert ht using 1
  funext n
  exact (inverseOrbit_eq_iterate s (bandChart a b θ Z) n).symm

theorem inverseKoenigs_analytic_lens
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (Z : ℂ) (hZ : Z∈strip θ Y) : AnalyticAt ℂ (inverseKoenigs s b) (bandChart a b θ Z) := by
  obtain ⟨δ,hδ,_hδq,ha,_hz,_hd,hlocal⟩ := exists_actual_inverse_local_koenigs s b hs hs1 hc.right_pos hc.right_fixed
  have hlim := lensControl_inverse_limit e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds (b:ℂ) hδ)).exists
  have hμ : inverseMultiplier s b≠0 := by
    unfold inverseMultiplier
    exact inv_ne_zero (ne_of_gt (lt_trans (by norm_num) (actual_right_multiplier s b hc.right_pos hc.right_fixed)))
  apply analyticAt_value_of_entry (inverseStep s) (b:ℂ) (inverseMultiplier s b) δ _ N hμ hδ ha
    (fun v hv => (hlocal v hv).2.2.1) hN
  intro k
  have hn := ((hc.true_orbits Z hZ).2.2.2.2.2 k).2.2.1
  rw [inverseOrbit_eq_iterate] at hn
  have hp : 0<(1+(inverseStep s)^[k] (bandChart a b θ Z)).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm ((inverseStep s)^[k] (bandChart a b θ Z)))).1
    simp only [Complex.add_re,Complex.one_re]
    linarith [hc.radius_small]
  have harg : AnalyticAt ℂ (fun v : ℂ => 1+v) ((inverseStep s)^[k] (bandChart a b θ Z)) := analyticAt_const.add analyticAt_id
  have hh : AnalyticAt ℂ (fun v : ℂ => (Complex.log (1+v)+(s:ℂ))/((1-s:ℝ):ℂ))
      ((inverseStep s)^[k] (bandChart a b θ Z)) :=
    ((harg.clog (mem_slitPlane_iff.mpr (Or.inl hp))).add analyticAt_const).div_const
  convert hh using 1
  funext v
  exact inverseStep_formula s v

end Kneser.InverseKoenigsEntry
end
