import Kneser.ActualSewingTimeAtlas
import Kneser.ActualRegularWelding

/-! The time atlas and actual regular physical welding use exactly the
fibers selected for the all-order coefficient theorem. The physical
attracting inverse is evaluated only in its true open image, and no
global inverse or classical Kneser identification is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualFiberRegularWelding

open Filter Set Metric Complex
open Kneser.ActualSewnAllOrders Kneser.ActualSewingTimeAtlas
open Kneser.ActualRegularWelding Kneser.WeightedFourier Kneser.FourierSewing
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualGrowingCoordinateInverse
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.GrowingStripFourier Kneser.GateFourierDerivative
open Kneser.ActualNormalizedSewing Kneser.CommonQuadraticBaseline
open Kneser.ActualAllOrderUpperHornBaseline Kneser.RealNormalizationAnchor
open scoped Topology

def lowerPatch (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : ℂ → ℂ :=
  lowerPhysicalPatch A B (Γ 1) s w.left w.right w.theta ((w.left+w.right)/2)
    (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1)
    (first (e 1) s) (second (e 1) s) w.inverse w.negative

def upperPatch (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : ℂ → ℂ :=
  upperPhysicalPatch A B (Γ 1) s w.left w.right w.theta Y realAnchor
    (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1)
    (first (e 1) s) (second (e 1) s)
    (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) w.positive

structure RegularFiberData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Prop where
  atlas : TimeAtlas (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) (height w.theta)
    (globalTransition A B e Γ s w) w.negative w.positive
    (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) w.shift
  lower_analytic : AnalyticOnNhd ℂ (lowerPatch A B e Γ Y P₀ s w)
    (symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1))
  upper_analytic : AnalyticOnNhd ℂ (upperPatch A B e Γ Y P₀ s w)
    (symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1))
  upper_actual_domain : ∀ z ∈ symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1),
    upperMap (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.positive
      (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) z ∈
        attractingImage A B (Γ 1) s w.left w.right w.theta Y realAnchor (first (e 1) s) (second (e 1) s)
  exact_physical_seam : EqOn (lowerPatch A B e Γ Y P₀ s w) (upperPatch A B e Γ Y P₀ s w)
    (symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1))
  actual_abel : ∀ z ∈ symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1),
    lowerPatch A B e Γ Y P₀ s w (z + 1) =
      Kneser.ExponentialUnfolding.unfolding s (lowerPatch A B e Γ Y P₀ s w z)
  actual_koenigs : ∀ z ∈ symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1),
    exp ((Real.log (Kneser.PositiveKoenigsOrbit.multiplier s w.left) : ℂ) *
      upperMap (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.positive
        (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) z) =
      Kneser.PositiveKoenigsOrbit.koenigsValue s w.left (upperPatch A B e Γ Y P₀ s w z) /
        Kneser.PositiveKoenigsOrbit.koenigsValue s w.left realAnchor

theorem regular_data_of_fiber_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber)
    (hd : FiberData A B e Γ T Y η Mg P₀ s w) (hs : 0 < s) (hs1 : s < 1)
    (hH : 3 < sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) :
    RegularFiberData A B e Γ Y P₀ s w := by
  let H := sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1
  let Tg := globalTransition A B e Γ s w
  let t₀ := gateFourierCoefficient 0 0 Tg
  have hc := hd.control
  have har : w.left < (w.left+w.right)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (w.left+w.right)/2 < w.right := by linarith [hc.left_neg,hc.right_pos]
  obtain ⟨_hopen,hR,hS,hcompat⟩ := actual_regular_inverse_charts
    (first (e 1)) (second (e 1)) A B (Γ 1) s w.left w.right w.theta Y η Mg P₀ realAnchor
    ((w.left+w.right)/2) hs1 hc har hrb w.inverse hd.inverse_analytic hd.inverse_identity
  have hmem : ∀ z ∈ symmetricStrip H,
      lowerMap H w.negative z ∈ symmetricStrip (outerWidth w.theta Y P₀) := by
    intro z hz
    exact lowerMap_mem_regular_strip (height w.theta) (boundaryLoss Y P₀) _ w.negative
      hd.negative_norm z hz rfl
  have hseam : ∀ z : ℂ, |z.im| ≤ H → Tg (lowerMap H w.negative z) = upperMap H w.positive t₀ z :=
    hd.sewing_identity
  have hupper : ∀ z ∈ symmetricStrip H,
      upperMap H w.positive t₀ z ∈
        attractingImage A B (Γ 1) s w.left w.right w.theta Y realAnchor (first (e 1) s) (second (e 1) s) := by
    intro z hz
    have hh := (hcompat _ (hmem z hz)).1
    change Tg (lowerMap H w.negative z) ∈ _ at hh
    rw [hseam z hz.le] at hh
    exact hh
  have hlow : AnalyticOnNhd ℂ (lowerPatch A B e Γ Y P₀ s w) (symmetricStrip H) := by
    intro z hz
    have hzi := abs_lt.mp (show |z.im| < H from hz)
    have ha := (differentiableOn_evaluate_negative H w.negative hd.negative_support).analyticAt
      ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzi.2)
    exact (hS _ (hmem z hz)).comp (f := lowerMap H w.negative) (analyticAt_id.add ha)
  have hupp : AnalyticOnNhd ℂ (upperPatch A B e Γ Y P₀ s w) (symmetricStrip H) := by
    intro z hz
    have hzi := abs_lt.mp (show |z.im| < H from hz)
    have ha := (differentiableOn_evaluate_positive H w.positive hd.positive_support).analyticAt
      ((isOpen_lt continuous_const (continuous_const.add Complex.continuous_im)).mem_nhds
        (by linarith : 0 < H + z.im))
    exact (hR _ (hupper z hz)).comp (f := upperMap H w.positive t₀)
      ((analyticAt_id.add analyticAt_const).add ha)
  refine ⟨time_atlas_of_fiber_data A B e Γ T Y η Mg P₀ s w hd hH,
    hlow,hupp,hupper,?_,?_,?_⟩
  · intro z hz
    have hh := (hcompat _ (hmem z hz)).2
    change regularAttractingInverse A B (Γ 1) s w.left w.right w.theta Y realAnchor
      (first (e 1) s) (second (e 1) s) (Tg (lowerMap H w.negative z)) =
      regularRepellingInverse A B (Γ 1) s w.left w.right w.theta ((w.left+w.right)/2)
        (first (e 1) s) (second (e 1) s) w.inverse (lowerMap H w.negative z) at hh
    rw [hseam z hz.le] at hh
    exact hh.symm
  · intro z hz
    unfold lowerPatch lowerPhysicalPatch
    rw [lowerMap_translation]
    exact regular_repelling_inverse_abel (first (e 1)) (second (e 1)) A B (Γ 1)
      s w.left w.right w.theta Y η Mg P₀ ((w.left+w.right)/2) hs1 hc har hrb
      w.inverse hd.inverse_identity _ (hmem z hz)
  · intro z hz
    have hanchor := actual_anchor_left_of_control (first (e 1)) (second (e 1)) A B (Γ 1)
      s w.left w.right w.theta Y η Mg P₀ hc
    exact regular_attracting_inverse_koenigs (first (e 1)) (second (e 1)) A B (Γ 1)
      s w.left w.right w.theta Y η Mg P₀ realAnchor hs hs1 hc hanchor _ (hupper z hz)

theorem all_orders_data_regular_welding
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, RegularFiberData A B e Γ Y P₀ s (W s) := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hd.actual_fibers, all_orders_data_time_atlas U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd, hpos, hlt] with s hs ha hsp hsl
  exact regular_data_of_fiber_data A B e Γ _ Y η Mg P₀ s (W s) hs hsp hsl ha.1

end Kneser.ActualFiberRegularWelding
end
