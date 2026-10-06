import Kneser.RealOrderedRootUniqueness
import Kneser.ActualLambdaFlatness
import Kneser.FourierSewingLambdaComparison
import Kneser.ActualHolomorphicGrowingLens

/-! Flatness of the genuine sewing scale holds for every actual ordered
root pair and every actual lens control. The root smallness hypothesis in
the quantitative exponential estimate is discharged by global uniqueness. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualOrderedLambdaFlatness

open Filter Set Kneser.ExponentialUnfolding Kneser.RealOrderedRootUniqueness
open Kneser.ActualLambdaFlatness Kneser.GrowingBandGeometry Kneser.FourierSewing
open Kneser.ActualHolomorphicGrowingLens
open scoped Topology

theorem actual_ordered_lambda_flat (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      0 < lambdaFactor s a ∧ lambdaFactor s a ≤ s ^ m := by
  have hsmall := eventually_all_ordered_roots_small (1 / 2) (by norm_num)
  filter_upwards [actual_lambda_flat m, hsmall] with s hflat hs a b ha hb hfa hfb
  have haabs := (hs a b ha hb hfa hfb).1
  have halow : -1 / 2 ≤ a := by rw [abs_of_neg ha] at haabs; linarith
  exact ⟨Real.exp_pos _, hflat a halow ha hfa⟩

theorem actual_negative_lambda_flat (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a : ℝ, a < 0 →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) →
      0 < lambdaFactor s a ∧ lambdaFactor s a ≤ s ^ m := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [actual_ordered_lambda_flat m, hpos, hlt] with s hs hsp hs1 a ha hfa
  obtain ⟨_a', b, _ha', hb, _hfa', hfb⟩ := exists_ordered_actual_roots s hsp hs1
  exact hs a b ha hb hfa hfb

theorem lambda_height_eq_actual_factor (s a : ℝ) :
    lambda (height (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a))) = lambdaFactor s a := by
  unfold lambda height lambdaFactor attractingMultiplier Kneser.PositiveKoenigsOrbit.multiplier
  congr 1
  ring

theorem actual_ordered_height_lambda_flat (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      0 < lambda (height (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a))) ∧
      lambda (height (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a))) ≤ s ^ m := by
  filter_upwards [actual_ordered_lambda_flat m] with s hs a b ha hb hfa hfb
  rw [lambda_height_eq_actual_factor]
  exact hs a b ha hb hfa hfb

theorem actual_control_lambda_flat (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b θ Y η M P : ℝ,
      LensControl e₁ e₂ A B Γ s a b θ Y η M P →
        0 < lambda (height θ) ∧ lambda (height θ) ≤ s ^ m := by
  filter_upwards [actual_ordered_lambda_flat m] with s hs a b θ Y η M P hc
  rw [hc.theta_actual, lambda_height_eq_actual_factor]
  exact hs a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed

end Kneser.ActualOrderedLambdaFlatness

end
