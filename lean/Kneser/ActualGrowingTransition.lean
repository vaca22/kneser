import Kneser.ActualGrowingCoordinateInverse

/-! The actual global growing transition is composed from the proved
inverse of the genuine repelling orbit sum. Its bounded displacement is
the sum of the two absolutely convergent true orbit corrections. -/

noncomputable section
set_option maxHeartbeats 600000
namespace Kneser.ActualGrowingTransition

open Filter Set Metric Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingCoordinateInverse Kneser.EvenPreparedOrbitDiscs
open Kneser.ActualInverseLensBootstrap Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

def transition (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ : ℂ) (V : ℂ → ℂ) (w : ℂ) : ℂ :=
  attractingCoordinate A B Γ s a b θ e₁ e₂ (V w)

def physicalInverse (a b θ : ℝ) (V : ℂ → ℂ) (w : ℂ) : ℂ := bandChart a b θ (V w)

def physicalAttractingValue (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ u : ℂ) : ℂ := lensModel s a b θ e₁ e₂ u + ∑' k, descendedTerm A B Γ 2 u s k

def physicalRepellingValue (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ u : ℂ) : ℂ := lensModel s a b θ e₁ e₂ u -
      ∑' k, descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0

theorem actual_transition_properties
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3 * Y + boundaryMargin P)))
    (hVs : ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
      V w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) = w) :
    AnalyticOnNhd ℂ (transition A B Γ s a b θ (e₁ s) (e₂ s) V) (strip θ (3 * Y + boundaryMargin P)) ∧
    AnalyticOnNhd ℂ (physicalInverse a b θ V) (strip θ (3 * Y + boundaryMargin P)) ∧
    InjOn (physicalInverse a b θ V) (strip θ (3 * Y + boundaryMargin P)) ∧
    ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
      ‖transition A B Γ s a b θ (e₁ s) (e₂ s) V w - w‖ ≤ 2 ∧
      physicalRepellingValue A B Γ s a b θ (e₁ s) (e₂ s) (physicalInverse a b θ V w) = w ∧
      physicalAttractingValue A B Γ s a b θ (e₁ s) (e₂ s) (physicalInverse a b θ V w) =
        transition A B Γ s a b θ (e₁ s) (e₂ s) V w := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hYθ : θ * Y ≤ Real.pi := hc.width.trans (by linarith [Real.pi_pos])
  have hsub : strip θ (3 * Y) ⊆ strip θ Y := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hA := (actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc).1
  have hchart := analyticOnNhd_bandChart a b θ Y hab hc.theta_pos hY hYθ
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    exact (hA (V w) (hsub (hVs w hw).1)).comp (f := V) (hV w hw)
  · intro w hw
    exact (hchart (V w) (hsub (hVs w hw).1)).comp (f := V) (hV w hw)
  · intro w hw z hz heq
    have hVz := injOn_bandChart a b θ Y hab hc.theta_pos hY hYθ
      (hsub (hVs w hw).1) (hsub (hVs z hz).1) heq
    have he := congrArg (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) hVz
    rwa [(hVs w hw).2,(hVs z hz).2] at he
  · intro w hw
    have hspec := hVs w hw
    have hb := actual_series_norm_le_one e₁ e₂ A B Γ s a b θ Y η M P hc (V w) (hsub hspec.1)
    refine ⟨?_,hspec.2,rfl⟩
    change ‖attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) - w‖ ≤ 2
    have he : attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) -
        repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) =
        forwardSeries A B Γ s a b θ (V w) + inverseSeries A B Γ s a b θ (V w) := by
      dsimp [attractingCoordinate,repellingCoordinate]
      ring
    have he' : attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) - w =
        forwardSeries A B Γ s a b θ (V w) + inverseSeries A B Γ s a b θ (V w) := by
      calc
        _ = attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) - repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) := congrArg (fun q => attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) - q) hspec.2.symm
        _ = _ := he
    rw [he']
    exact (norm_add_le _ _).trans (by linarith only [hb.1,hb.2])

/-- Changing actual normalization constants affects only a fixed additive
constant in the bounded transition displacement. -/
theorem normalized_transition_displacement
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ : ℂ)
    (V : ℂ → ℂ) (Cplus Cminus w : ℂ)
    (hb : ‖transition A B Γ s a b θ e₁ e₂ V (w+Cminus) - (w+Cminus)‖ ≤ 2) :
    ‖(transition A B Γ s a b θ e₁ e₂ V (w+Cminus)-Cplus)-w-(Cminus-Cplus)‖ ≤ 2 := by
  convert hb using 1
  congr 1
  ring

theorem exists_actual_full_growing_transition
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b θ : ℝ, ∃ V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ V (strip θ (3 * Y + boundaryMargin P)) ∧
        (∀ w ∈ strip θ (3 * Y + boundaryMargin P),
          V w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) = w) ∧
        AnalyticOnNhd ℂ (transition A B Γ s a b θ (e₁ s) (e₂ s) V) (strip θ (3 * Y + boundaryMargin P)) ∧
        AnalyticOnNhd ℂ (physicalInverse a b θ V) (strip θ (3 * Y + boundaryMargin P)) ∧
        InjOn (physicalInverse a b θ V) (strip θ (3 * Y + boundaryMargin P)) ∧
        ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
          ‖transition A B Γ s a b θ (e₁ s) (e₂ s) V w - w‖ ≤ 2 ∧
          physicalRepellingValue A B Γ s a b θ (e₁ s) (e₂ s) (physicalInverse a b θ V w) = w ∧
          physicalAttractingValue A B Γ s a b θ (e₁ s) (e₂ s) (physicalInverse a b θ V w) =
            transition A B Γ s a b θ (e₁ s) (e₂ s) V w := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  obtain ⟨_Vplus,V,hVp,hV,_hsp,hspec⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  exact ⟨a,b,θ,V,hc,hV,hspec,actual_transition_properties e₁ e₂ A B Γ s a b θ Y η M P hc V hV hspec⟩

end Kneser.ActualGrowingTransition
end
