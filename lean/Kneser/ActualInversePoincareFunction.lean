import Kneser.ActualInversePoincareSeed

/-! The actual entire Poincare function is a genuine inverse of the
repelling Koenigs orbit sum on the growing lens. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.ActualInversePoincareFunction
open Set Metric Filter Complex
open Kneser.ActualInversePoincareSeed Kneser.ActualInverseLocalKoenigs
open Kneser.QuadraticLocalKoenigs Kneser.InverseKoenigsEntry
open Kneser.ExponentialUnfolding Kneser.ActualReflectedLensModel
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.PoincareEntireExtension
open scoped Topology

theorem iterate_inverse_cancel (f g : ℂ → ℂ) (u : ℂ)
    (heq : ∀ n : ℕ, f (g ((g^[n]) u))=(g^[n]) u) (N : ℕ) :
    (f^[N]) ((g^[N]) u)=u := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply' (f:=g),Function.iterate_succ_apply (f:=f),heq N]
    exact ih

theorem poincare_koenigs_of_true_entry (s b : ℝ) (H : ℂ → ℂ) (r : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hb : 0<b) (hroot : unfolding s b=(b:ℂ))
    (hr : 0<r) (hH : AnalyticOnNhd ℂ H (ball 0 r))
    (hleft : ∀ᶠ u : ℂ in 𝓝 (b:ℂ), H (inverseKoenigs s b u)=u)
    (heq : ∀ z∈ball (0:ℂ) r, unfolding s (H ((inverseMultiplier s b:ℂ)*z))=H z)
    (u : ℂ) (hlim : Tendsto (fun n => (inverseStep s)^[n] u) atTop (𝓝 (b:ℂ)))
    (hcancel : ∀ n, unfolding s (inverseStep s ((inverseStep s)^[n] u))=(inverseStep s)^[n] u) :
    entire (unfolding s) H (inverseMultiplier s b) r (inverseKoenigs s b u)=u := by
  have hm : 0 < inverseMultiplier s b := inv_pos.mpr (lt_trans (by norm_num) (actual_right_multiplier s b hb hroot))
  have hm1 : inverseMultiplier s b < 1 := (inv_lt_one₀ (lt_trans (by norm_num) (actual_right_multiplier s b hb hroot))).mpr (actual_right_multiplier s b hb hroot)
  have hsum := actual_inverse_sum_of_limit s b u hs hs1 hb hroot hlim
  obtain ⟨δ,hδ,_hδq,hκ,hκ0,_hd,_hlocal⟩ := exists_actual_inverse_local_koenigs s b hs hs1 hb hroot
  have hκcont := (hκ (b:ℂ) (mem_ball_self hδ)).continuousAt
  have hsmall : ∀ᶠ v : ℂ in 𝓝 (b:ℂ), inverseKoenigs s b v∈ball (0:ℂ) r := by
    apply hκcont.tendsto.eventually
    change ball (0:ℂ) r∈𝓝 (inverseKoenigs s b b)
    rw [hκ0]
    exact ball_mem_nhds (0:ℂ) hr
  obtain ⟨N,hN,hNr⟩ := (hlim.eventually (hleft.and hsmall)).exists
  have hscale := value_iterate (inverseStep s) (b:ℂ) (inverseMultiplier s b) u N (ne_of_gt hm) hsum
  change inverseKoenigs s b ((inverseStep s)^[N] u)=(inverseMultiplier s b:ℂ)^N*inverseKoenigs s b u at hscale
  rw [entire_eq_term (unfolding s) H (inverseMultiplier s b) r hm.le hm1 hr heq N _
    (by rwa [←hscale])]
  unfold term
  rw [←hscale,hN]
  exact iterate_inverse_cancel (unfolding s) (inverseStep s) u hcancel N

/-- Same actual roots and lens control construct a whole-plane Poincare
function whose inverse identity is proved on every physical lens point. -/
theorem exists_actual_poincare_function_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    ∃ F : ℂ → ℂ, (∀ z, AnalyticAt ℂ F z) ∧ F 0=(b:ℂ) ∧ HasDerivAt F 1 0 ∧
      (∀ z, F (z/(inverseMultiplier s b:ℂ))=unfolding s (F z)) ∧
      ∀Z∈strip θ Y, F (inverseKoenigs s b (bandChart a b θ Z))=bandChart a b θ Z := by
  obtain ⟨H,r,hr,hH,hH0,hHd,hleft,_hright,heq⟩ := exists_seed_with_inverse s b hs hs1 hc.right_pos hc.right_fixed
  have hm : 0 < inverseMultiplier s b := inv_pos.mpr
    (lt_trans (by norm_num) (actual_right_multiplier s b hc.right_pos hc.right_fixed))
  have hm1 : inverseMultiplier s b < 1 := (inv_lt_one₀ (by linarith [actual_right_multiplier s b hc.right_pos hc.right_fixed] : 0 < Kneser.PositiveKoenigsOrbit.multiplier s b)).mpr
    (actual_right_multiplier s b hc.right_pos hc.right_fixed)
  let F := entire (unfolding s) H (inverseMultiplier s b) r
  have hf : ∀ z : ℂ, AnalyticAt ℂ (unfolding s) z := by
    intro z
    exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cexp).sub analyticAt_const
  have hFa : ∀ z, AnalyticAt ℂ F z := entire_analytic _ _ _ _ hm.le hm1 hr hf hH heq
  have hFl : EqOn F H (ball (0:ℂ) r) := entire_eq_local _ _ _ _ hm.le hm1 hr heq
  have hF0 : F 0=(b:ℂ) := (hFl (mem_ball_self hr)).trans hH0
  have hnear : F=ᶠ[𝓝 (0:ℂ)] H := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr : (0:ℂ)∈ball (0:ℂ) r)] with z hz
    exact hFl hz
  have hFd : HasDerivAt F 1 0 := hHd.congr_of_eventuallyEq
    hnear
  refine ⟨F,hFa,hF0,hFd,entire_functional_eq _ _ _ _ hm hm1 hr heq,?_⟩
  intro Z hZ
  apply poincare_koenigs_of_true_entry s b H r hs hs1 hc.right_pos hc.right_fixed hr hH hleft heq _
    (lensControl_inverse_limit e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ)
  intro n
  apply unfolding_inverseStep_of_ne s _ (by linarith)
  have hn := ((hc.true_orbits Z hZ).2.2.2.2.2 n).2.2.1
  rw [inverseOrbit_eq_iterate] at hn
  have hp : 0<(1+(inverseStep s)^[n] (bandChart a b θ Z)).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm ((inverseStep s)^[n] (bandChart a b θ Z)))).1
    simp only [Complex.add_re,Complex.one_re]
    linarith [hc.radius_small]
  intro hz
  rw [hz,Complex.zero_re] at hp
  linarith

end Kneser.ActualInversePoincareFunction
end
