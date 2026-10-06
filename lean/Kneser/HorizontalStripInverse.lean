import Mathlib.Topology.MetricSpace.Contracting
import Kneser.HolomorphicInjectiveInverse

/-! A bounded imaginary displacement and a proved contraction yield
coverage of the full horizontal strip with only an additive boundary
margin.  No fractional loss of the strip height occurs. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.HorizontalStripInverse

open Set Metric
open scoped Topology NNReal

def closedStrip (a b : ℝ) : Set ℂ := {z | a ≤ z.im ∧ z.im ≤ b}
def openStrip (a b : ℝ) : Set ℂ := {z | a < z.im ∧ z.im < b}

theorem closedStrip_isClosed (a b : ℝ) : IsClosed (closedStrip a b) :=
  (isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)

theorem openStrip_isOpen (a b : ℝ) : IsOpen (openStrip a b) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem exists_preimage (F : ℂ → ℂ) (a b B : ℝ) (K : ℝ≥0)
    (hK : K < 1) (hB : 0 ≤ B)
    (hlip : LipschitzOnWith K (fun z => F z - z) (closedStrip a b))
    (hdisp : ∀ z ∈ closedStrip a b, |(F z - z).im| ≤ B)
    (w : ℂ) (hw : w ∈ openStrip (a + B) (b - B)) :
    ∃ z ∈ openStrip a b, F z = w := by
  let G : ℂ → ℂ := fun z => w - (F z - z)
  have hm : MapsTo G (closedStrip a b) (closedStrip a b) := by
    intro z hz
    have hh := abs_le.mp (hdisp z hz)
    change a ≤ w.im - (F z - z).im ∧ w.im - (F z - z).im ≤ b
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hc : ContractingWith K (hm.restrict G _ _) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (G x.val) (G y.val) ≤ (K : ℝ) * dist x.val y.val
    have he : G x.val - G y.val = -((F x.val - x.val) - (F y.val - y.val)) := by dsimp [G]; ring
    rw [dist_eq_norm, he, norm_neg]
    simpa only [dist_eq_norm] using hlip.dist_le_mul x.val x.property y.val y.property
  have hwc : w ∈ closedStrip a b := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨z, hz, hfixed, _hlimit, _herror⟩ := ContractingWith.exists_fixedPoint'
    (closedStrip_isClosed a b).isComplete hm hc hwc (edist_ne_top w (G w))
  have heq : F z = w := by
    change w - (F z - z) = z at hfixed
    linear_combination -hfixed
  have him : z.im = w.im - (F z - z).im := by
    rw [heq]
    simp
  have hh := abs_le.mp (hdisp z hz)
  exact ⟨z, ⟨by rw [him]; linarith [hw.1], by rw [him]; linarith [hw.2]⟩, heq⟩

theorem injective_of_lipschitz_displacement (F : ℂ → ℂ) (a b : ℝ) (K : ℝ≥0)
    (hK : K < 1) (hlip : LipschitzOnWith K (fun z => F z - z) (closedStrip a b)) :
    InjOn F (closedStrip a b) := by
  intro x hx y hy heq
  have hh := hlip.dist_le_mul x hx y hy
  have hn : ‖x - y‖ ≤ (K : ℝ) * ‖x - y‖ := by
    have he : (F x - x) - (F y - y) = -(x-y) := by rw [heq]; ring
    simpa only [dist_eq_norm, he, norm_neg] using hh
  have hk : (K : ℝ) < 1 := hK
  have he : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

theorem exists_holomorphic_strip_inverse (F : ℂ → ℂ) (a b B : ℝ) (K : ℝ≥0)
    (hK : K < 1) (hB : 0 ≤ B)
    (hlip : LipschitzOnWith K (fun z => F z - z) (closedStrip a b))
    (hdisp : ∀ z ∈ closedStrip a b, |(F z - z).im| ≤ B)
    (ha : AnalyticOnNhd ℂ F (openStrip a b))
    (hd : ∀ z ∈ openStrip a b, deriv F z ≠ 0) :
    ∃ V : ℂ → ℂ, AnalyticOnNhd ℂ V (openStrip (a + B) (b - B)) ∧
      ∀ w ∈ openStrip (a + B) (b - B), V w ∈ openStrip a b ∧ F (V w) = w := by
  have hsub : openStrip a b ⊆ closedStrip a b := fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have hi : InjOn F (openStrip a b) := (injective_of_lipschitz_displacement F a b K hK hlip).mono hsub
  have himage : openStrip (a+B) (b-B) ⊆ F '' openStrip a b := by
    intro w hw
    exact exists_preimage F a b B K hK hB hlip hdisp w hw
  let V := Kneser.HolomorphicInjectiveInverse.imageInverse F (openStrip a b)
  exact ⟨V, (Kneser.HolomorphicInjectiveInverse.analyticOnNhd_imageInverse F _
    (openStrip_isOpen a b) hi (fun z hz => ⟨ha z hz, hd z hz⟩)).mono himage,
    fun w hw => Kneser.HolomorphicInjectiveInverse.imageInverse_spec F _ w (himage hw)⟩

end Kneser.HorizontalStripInverse
