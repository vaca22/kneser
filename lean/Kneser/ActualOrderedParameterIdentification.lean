import Kneser.ActualAllOrderUpperHornBaseline
import Kneser.RealOrderedRootUniqueness
import Kneser.ActualBandTimeConfluence

/-! The analytic parameter used by the common all-order coefficients is
the product of logarithms of the SAME true ordered multipliers. This
holds uniformly over every actual root pair, without selecting a branch. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualOrderedParameterIdentification

open Filter Set Kneser.CommonQuadraticBaseline Kneser.ReflectedOrbitChainCoefficient
open Kneser.RealOrderedRootUniqueness Kneser.ActualCommonMultiplierParameter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualAllOrderUpperHornBaseline
open scoped Topology

theorem actual_parameter_eq_ordered_multipliers
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) (p : ℂ → ℂ)
    (hp : ∀ x : ℂ, p (x^2) = -Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U x) *
      Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U (-x))) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a<0 → 0<b →
      unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
      p s = (-Real.log (multiplier s a) * Real.log (multiplier s b) : ℝ) := by
  obtain ⟨s₀,hs₀,hmatch⟩ := exists_uniform_actual_root_matching U H e₁ e₂ A B K F Γ hdata
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s<min s₀ 1 :=
    (eventually_lt_nhds (lt_min hs₀ (by norm_num))).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  filter_upwards [hsmall,hpos] with s hs hsp a b ha hb hfa hfb
  have hx : (Real.sqrt s : ℂ)^2=(s:ℂ) := by rw [←Complex.ofReal_pow,Real.sq_sqrt hsp.le]
  have hm := hmatch s a b hsp (hs.trans_le (min_le_left _ _)) ha hb hfa hfb _ hx
  exact parameter_eq_real_of_matching U p hp s a b _ hx (hs.trans_le (min_le_right _ _))
    (Kneser.ActualBandTimeConfluence.actual_negative_root_gt_neg_one s a hfa) hb hm

theorem actual_baseline_parameter_eq_ordered_multipliers
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch : ℝ) (N M M₀ : ℕ) (Y : ℝ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ)
    (hb : BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Y Vold V p r G) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a<0 → 0<b →
      unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
      p s = (-Real.log (multiplier s a) * Real.log (multiplier s b) : ℝ) :=
  actual_parameter_eq_ordered_multipliers U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hb.actual p hb.actual_parameter

end Kneser.ActualOrderedParameterIdentification
end
