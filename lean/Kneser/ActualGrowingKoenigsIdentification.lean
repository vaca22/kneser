import Kneser.LensKoenigsIdentification
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The true forward growing coordinate is a single holomorphic logarithm
of the actual normalized Koenigs orbit sum on the whole growing strip. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualGrowingKoenigsIdentification
open Set Metric Filter Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsAbel
open Kneser.ActualLensModel Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualKoenigsRealPhase Kneser.ActualKoenigsUpperBranch
open Kneser.LensKoenigsIdentification Kneser.GrowingLensKoenigs
open Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

def normalizedAttracting (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r₀ : ℝ)
    (e₁ e₂ : ℂ) (Z : ℂ) : ℂ :=
  attractingCoordinate A B Γ s a b θ e₁ e₂ Z-
    (koenigsTime s a r₀+modelConstant s a b e₁ e₂)

theorem strip_preconnected (θ Y : ℝ) : IsPreconnected (strip θ Y) := by
  exact ((convex_Ioo Y (height θ-Y)).linear_preimage Complex.imCLM.toLinearMap).isPreconnected

theorem midline_mem_strip (θ Y x : ℝ) (hθ : 0<θ) (hwidth : θ*Y≤Real.pi/2) :
    (x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I∈strip θ Y := by
  have hl : Y<Real.pi/θ := (lt_div_iff₀ hθ).mpr (by nlinarith [Real.pi_pos])
  change Y<((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I).im ∧
    ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I).im<height θ-Y
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
  unfold height
  rw [show 2*Real.pi/θ=2*(Real.pi/θ) by ring]
  constructor <;> linarith

/-- Equality on the real midline determines two true holomorphic strip
maps. The accumulating points are explicitly constructed. -/
theorem eqOn_strip_of_midline (f g : ℂ → ℂ) (θ Y : ℝ)
    (hθ : 0<θ) (hwidth : θ*Y≤Real.pi/2)
    (hf : AnalyticOnNhd ℂ f (strip θ Y)) (hg : AnalyticOnNhd ℂ g (strip θ Y))
    (heq : ∀ x : ℝ, f ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=
      g ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)) : EqOn f g (strip θ Y) := by
  let z₀ : ℂ := ((Real.pi/θ:ℝ):ℂ)*I
  have h0 : z₀∈strip θ Y := by simpa only [Complex.ofReal_zero,zero_add] using midline_mem_strip θ Y 0 hθ hwidth
  apply hf.eqOn_of_preconnected_of_mem_closure hg (strip_preconnected θ Y) h0
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  change Tendsto (fun n : ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝 (0:ℂ)) at hc
  have hz : Tendsto (fun n : ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)+z₀) atTop (𝓝 z₀) := by simpa only [zero_add] using hc.add_const z₀
  apply mem_closure_of_tendsto hz
  apply Eventually.of_forall
  intro n
  refine ⟨heq (1/((n:ℝ)+1)),?_⟩
  change ((1/((n:ℝ)+1):ℝ):ℂ)+z₀≠z₀
  intro he
  have hh : ((1/((n:ℝ)+1):ℝ):ℂ)=0 := by
    have hh := sub_eq_zero.mpr he
    simpa only [add_sub_cancel_right] using hh
  exact (by exact_mod_cast (ne_of_gt (show 0<(1/((n:ℝ)+1):ℝ) by positivity)) : ((1/((n:ℝ)+1):ℝ):ℂ)≠0) hh

theorem normalizedAttracting_midline_eq_upperTime
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ x : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)
      ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=
      upperTime s a r₀ (bandChart a b θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)) := by
  have hb := bandChart_midline_between a b θ x (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
  let r : ℝ := (a+b*Real.exp (-θ*x))/(1+Real.exp (-θ*x))
  have he : bandChart a b θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=(r:ℂ) := bandChart_midline a b θ x hc.theta_pos
  have har : a<r := by simpa only [he,Complex.ofReal_re] using hb.1
  have hrb : r<b := by simpa only [he,Complex.ofReal_re] using hb.2
  have ha := physicalAttracting_eq_koenigs_real_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb
  unfold normalizedAttracting attractingCoordinate forwardSeries
  change physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) (bandChart a b θ _) -
    (koenigsTime s a r₀+modelConstant s a b (e₁ s) (e₂ s))= _
  rw [he,ha]
  unfold intervalKoenigsTime upperTime koenigsTime
  rw [hc.theta_actual]
  push_cast
  ring

/-- The logarithmic identification on the entire growing strip is an
actual conclusion of preparation and dynamics. -/
theorem normalizedAttracting_exponential_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) :
    AnalyticOnNhd ℂ (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) (strip θ Y) ∧
    ∀ Z∈strip θ Y,
      Complex.exp ((Real.log (multiplier s a):ℂ)*normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s) Z)=
        koenigsValue s a (bandChart a b θ Z)/koenigsValue s a r₀ := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hl₀ := real_left_orbit_limit s a r₀ hs1 ha hc.left_fixed hμ.le hμ1 hr₀
  have hsum₀ := actual_koenigs_sum_of_orbit_limit s a r₀ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hl₀
  have hneg := koenigsValue_negative_left s a r₀ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hsum₀ hl₀ hr₀
  have hK₀ : koenigsValue s a r₀≠0 := by intro he; rw [he,Complex.zero_re] at hneg; linarith [hneg.2]
  have hA := (actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc).1
  have hN : AnalyticOnNhd ℂ (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) (strip θ Y) :=
    fun Z hZ => (hA Z hZ).sub analyticAt_const
  refine ⟨hN,?_⟩
  have hC := analyticOnNhd_bandChart a b θ Y (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (by linarith [hc.height_large]) (hc.width.trans (by linarith [Real.pi_pos]))
  have hK := (koenigs_geometry_of_lensControl e₁ e₂ A B Γ s a b θ Y η M P hs hs1 hc).1
  have hf : AnalyticOnNhd ℂ (fun Z => Complex.exp ((Real.log (multiplier s a):ℂ)*
      normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s) Z)) (strip θ Y) :=
    fun Z hZ => (analyticAt_const.mul (hN Z hZ)).cexp
  have hg : AnalyticOnNhd ℂ (fun Z => koenigsValue s a (bandChart a b θ Z)/koenigsValue s a r₀) (strip θ Y) :=
    fun Z hZ => ((hK _ ⟨Z,hZ,rfl⟩).comp (hC Z hZ)).div_const
  apply eqOn_strip_of_midline _ _ θ Y hc.theta_pos hc.width hf hg
  intro x
  rw [normalizedAttracting_midline_eq_upperTime e₁ e₂ A B Γ s a b θ Y η M P r₀ x hs hs1 hc]
  apply upperTime_exponential s a r₀ _ hμ hμ1 _ hK₀
  exact (koenigs_geometry_of_lensControl e₁ e₂ A B Γ s a b θ Y η M P hs hs1 hc).2.2 _
    ⟨_,midline_mem_strip θ Y x hc.theta_pos hc.width,rfl⟩ |>.1

end Kneser.ActualGrowingKoenigsIdentification
end
