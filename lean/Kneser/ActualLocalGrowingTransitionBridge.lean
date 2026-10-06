import Kneser.ActualLensPreparedCoordinateBridge
import Kneser.ActualRealNormalizedTransition
import Kneser.ActualGrowingTransition
import Kneser.ActualNormalizedGrowingTransition

/-! Exact identification of the common local all-order transition with
the true global growing transition. The model branch constants cancel
between the actual repelling value and its actual spatial anchor. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualLocalGrowingTransitionBridge

open Set Metric Filter Complex
open Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualLensPreparedCoordinateBridge
open Kneser.ActualBilateralGate Kneser.ActualQuantitativeGateTransition
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse
open Kneser.ActualNormalizationAnchorExpansion Kneser.CommonQuadraticBaseline

def gateConstant (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Yg : ℝ) (e₁ e₂ : ℂ) : ℂ :=
  Kneser.ActualGrowingTransition.physicalRepellingValue A B Γ s a b θ e₁ e₂ (chartPoint Yg 0)

theorem centeredRepelling_eq_actual_difference
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y Yg : ℝ) (N : ℕ)
    (hb : ∀ Z : ℂ, Z ∈ strip θ Y → 0 < (bandChart a b θ Z).im →
      forwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
        attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z ∧
      backwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
        repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z +
          residueSum s a b * (Real.pi : ℂ) * I)
    (Z Z₀ z : ℂ) (hZ : Z ∈ strip θ Y) (hZ₀ : Z₀ ∈ strip θ Y)
    (hu : 0 < (bandChart a b θ Z).im) (hu₀ : 0 < (bandChart a b θ Z₀).im)
    (he : bandChart a b θ Z = chartPoint Yg z)
    (he₀ : bandChart a b θ Z₀ = chartPoint Yg 0) :
    centeredRepelling U H e₁ e₂ A B Γ N Yg s z =
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z -
        gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s) := by
  have hz := (hb Z hZ hu).2
  have hzero := (hb Z₀ hZ₀ hu₀).2
  rw [he] at hz
  rw [he₀] at hzero
  unfold centeredRepelling repellingChart
  rw [hz,hzero]
  have hg : gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s) =
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z₀ := by
    unfold gateConstant
    rw [←he₀]
    rfl
  rw [hg]
  ring

theorem real_normalized_eq_growing
    (U H A B : ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ)
    (Γ : ℕ → ℂ × ℂ → ℂ) (s a b θ Y η Mg P Yg : ℝ) (N M : ℕ)
    (hc : LensControl (first (e 1)) (second (e 1)) A B (Γ 1) s a b θ Y η Mg P)
    (hb : ∀ Z : ℂ, Z ∈ strip θ Y → 0 < (bandChart a b θ Z).im →
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N (bandChart a b θ Z) s =
        attractingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) Z ∧
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N (bandChart a b θ Z) s =
        repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) Z +
          residueSum s a b * (Real.pi : ℂ) * I)
    (hpoints : ∀ z ∈ closedBall (0 : ℂ) 12, ∃ Z : ℂ,
      Z ∈ strip θ (3 * Y + 2 * boundaryMargin P) ∧
      0 < (bandChart a b θ Z).im ∧ bandChart a b θ Z = chartPoint Yg z)
    (Vlocal : ℂ → ℂ)
    (hl : ∀ w ∈ ball (0 : ℂ) 3, Vlocal w ∈ closedBall (0 : ℂ) 12 ∧
      centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Yg s (Vlocal w) = w)
    (Vglobal : ℂ → ℂ)
    (hg : ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
      Vglobal w ∈ strip θ (3 * Y) ∧
      repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) (Vglobal w) = w)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 3) :
    w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s)
        ∈ strip θ (3 * Y + boundaryMargin P) ∧
    Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Yg
      (fun _ => Vlocal) s w =
      Kneser.ActualGrowingTransition.transition A B (Γ 1) s a b θ
        (first (e 1) s) (second (e 1) s) Vglobal
          (w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s)) -
        anchorValue U H (first (e 1)) (second (e 1)) A B (Γ 1) M s := by
  have hP : 0 ≤ P := (norm_nonneg (first (e 1) s)).trans hc.first_model_bound
  have hB : 0 ≤ boundaryMargin P := by unfold boundaryMargin; positivity
  have hY : 0 < Y := by linarith [hc.height_large]
  have hsub₁ : strip θ (3 * Y + 2 * boundaryMargin P) ⊆ strip θ Y := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hsub₂ : strip θ (3 * Y + 2 * boundaryMargin P) ⊆ strip θ (2 * Y) := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  obtain ⟨Z₀,hZ₀,hu₀,he₀⟩ := hpoints 0 (by simp)
  obtain ⟨Z,hZ,hu,he⟩ := hpoints (Vlocal w) (hl w hw).1
  have hrep := centeredRepelling_eq_actual_difference U H (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y Yg N hb Z Z₀ (Vlocal w) (hsub₁ hZ) (hsub₁ hZ₀) hu hu₀ he he₀
  rw [(hl w hw).2] at hrep
  have hval : repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) Z =
      w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s) := by
    linear_combination -hrep
  have hphase := (actual_coordinate_phase_bounds (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y η Mg P hc Z (hsub₁ hZ)).2
  have htarget : w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s)
      ∈ strip θ (3 * Y + boundaryMargin P) := by
    rw [←hval]
    have hh := abs_le.mp hphase
    simp only [Complex.sub_im] at hh
    exact ⟨by linarith [hZ.1,hh.1],by linarith [hZ.2,hh.2]⟩
  have hspec := hg _ htarget
  have hsource : Vglobal (w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s))
      ∈ strip θ (2 * Y) := ⟨by linarith [hspec.1.1],by linarith [hspec.1.2]⟩
  have hV := (actual_coordinates_injective_buffered (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y η Mg P hc).2 hsource (hsub₂ hZ) (hspec.2.trans hval.symm)
  refine ⟨htarget,?_⟩
  have hforward := (hb Z (hsub₁ hZ) hu).1
  rw [he] at hforward
  unfold Kneser.ActualRealNormalizedTransition.transition
    Kneser.ActualRealAnchorHigherGate.normalizedCoordinate Kneser.ActualGrowingTransition.transition
  rw [hV,hforward]

theorem normalized_global_shift_identity
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Yg r₀ r : ℝ) (M : ℕ) (V : ℂ → ℂ) (w : ℂ)
    (ha : anchorValue U H e₁ e₂ A B Γ M s =
      Kneser.PositiveKoenigsAbel.koenigsTime s a r₀ +
        Kneser.PositiveKoenigsAbel.modelConstant s a b (e₁ s) (e₂ s)) :
    Kneser.ActualGrowingTransition.transition A B Γ s a b θ (e₁ s) (e₂ s) V
        (w + gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s)) -
      anchorValue U H e₁ e₂ A B Γ M s =
    Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
      (w + gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s) -
        Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)) := by
  rw [ha]
  unfold Kneser.ActualGrowingTransition.transition
    Kneser.ActualNormalizedGrowingTransition.transition
    Kneser.ActualGrowingKoenigsIdentification.normalizedAttracting
  congr 2
  ring

end Kneser.ActualLocalGrowingTransitionBridge
end
