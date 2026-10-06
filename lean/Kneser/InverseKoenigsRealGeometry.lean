import Kneser.ActualInversePoincareSeed
import Kneser.ActualGrowingRealPhases

/-! Nonvanishing and real sign of the actual repelling Koenigs sum follow
from finite entry and its proved local inverse. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.InverseKoenigsRealGeometry
open Set Metric Filter Complex
open Kneser.QuadraticLocalKoenigs Kneser.ActualInverseLocalKoenigs
open Kneser.ActualInversePoincareSeed Kneser.InverseKoenigsEntry
open Kneser.ActualReflectedLensModel Kneser.ExponentialUnfolding
open Kneser.ActualReflectedLensMidline Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.GrowingBandGeometry
open scoped Topology

theorem inverseKoenigs_ne_zero_of_limit (s b : ℝ) (u : ℂ)
    (hs : 0<s) (hs1 : s<1/2) (hb : 0<b) (hroot : unfolding s b=(b:ℂ))
    (hlim : Tendsto (fun n => (inverseStep s)^[n] u) atTop (𝓝 (b:ℂ)))
    (hne : ∀ n, (inverseStep s)^[n] u≠(b:ℂ)) : inverseKoenigs s b u≠0 := by
  obtain ⟨H,r,_hr,_hH,hH0,_hHd,hleft,_hright,_hstep⟩ := exists_seed_with_inverse s b hs hs1 hb hroot
  have hsum := actual_inverse_sum_of_limit s b u hs hs1 hb hroot hlim
  have hμ : inverseMultiplier s b≠0 := by
    unfold inverseMultiplier
    exact inv_ne_zero (ne_of_gt (lt_trans (by norm_num) (actual_right_multiplier s b hb hroot)))
  obtain ⟨N,hN⟩ := (hlim.eventually hleft).exists
  have he := value_iterate (inverseStep s) (b:ℂ) (inverseMultiplier s b) u N hμ hsum
  change inverseKoenigs s b ((inverseStep s)^[N] u)=(inverseMultiplier s b:ℂ)^N*inverseKoenigs s b u at he
  intro hz
  rw [hz,mul_zero] at he
  rw [he,hH0] at hN
  exact hne N hN.symm

theorem inverseKoenigs_negative_between_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    (inverseKoenigs s b r).im=0 ∧ (inverseKoenigs s b r).re<0 := by
  obtain ⟨hZ,hchart⟩ := interval_source a b θ Y r hc.theta_pos hc.width har hrb
  have hlim := lensControl_inverse_limit e₁ e₂ A B Γ s a b θ Y η M P hc (bandTime a b θ r) hZ
  rw [hchart] at hlim
  have haa := real_root_gt_neg_one s a hc.left_fixed
  have hreal := real_between_inverse_orbit s a b r (by linarith) haa hc.left_fixed hc.right_fixed har hrb
  have hsum := actual_inverse_sum_of_limit s b r hs hs1 hc.right_pos hc.right_fixed hlim
  have hμ : 0 < inverseMultiplier s b := inv_pos.mpr
    (lt_trans (by norm_num) (actual_right_multiplier s b hc.right_pos hc.right_fixed))
  have happroxim := tendsto_approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) (r:ℂ) hsum
  have hapreal : ∀ n : ℕ, (approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) (r:ℂ) n).im=0 ∧
      (approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) (r:ℂ) n).re<0 := by
    intro n
    have he : (inverseStep s)^[n] (r:ℂ)=(((inverseStep s)^[n] (r:ℂ)).re:ℂ) := by
      apply Complex.ext <;> simp [(hreal n).1]
    rw [approximation,he]
    simp only [←Complex.ofReal_pow,←Complex.ofReal_inv,←Complex.ofReal_sub,←Complex.ofReal_mul,Complex.ofReal_im,Complex.ofReal_re]
    exact ⟨trivial,mul_neg_of_pos_of_neg (inv_pos.mpr (pow_pos hμ n)) (by linarith [(hreal n).2.2])⟩
  have him : (inverseKoenigs s b r).im=0 := by
    have ht := Complex.continuous_im.continuousAt.tendsto.comp happroxim
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hapreal n).1.symm))
  have hre : (inverseKoenigs s b r).re≤0 :=
    le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp happroxim) (Eventually.of_forall fun n => (hapreal n).2.le)
  have hne := inverseKoenigs_ne_zero_of_limit s b r hs hs1 hc.right_pos hc.right_fixed hlim
    (fun n => by intro he; have hh := (hreal n).2.2; rw [he,Complex.ofReal_re] at hh; exact lt_irrefl _ hh)
  refine ⟨him,lt_of_le_of_ne hre ?_⟩
  intro he
  apply hne
  apply Complex.ext <;> simp [he,him]

end Kneser.InverseKoenigsRealGeometry
end
