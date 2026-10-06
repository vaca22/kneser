import Kneser.GrowingLensKoenigs
import Kneser.RealLensForwardModelStep
import Kneser.RealRepellingCoordinatePhase

/-! Both genuine growing-lens orbit coordinates have derived real
normalizations. No polynomial reality or real-series premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualGrowingRealPhases
open Set Metric Complex Filter
open Kneser.ExponentialUnfolding Kneser.ActualLensModel Kneser.ActualLensGeometry
open Kneser.GrowingBandGeometry Kneser.GrowingLensEntry Kneser.RealLensMidline
open Kneser.ActualReflectedLensMidline Kneser.ActualReflectedLensModel
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensRootLimit
open Kneser.EvenPreparedOrbitDiscs Kneser.RealLensModelStep Kneser.RealLensForwardModelStep
open Kneser.RealRepellingCoordinatePhase Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingLensKoenigs Kneser.ReflectedOrbitChainCoefficient
open scoped Topology BigOperators

def physicalAttracting (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ u : ℂ) : ℂ :=
  lensModel s a b θ e₁ e₂ u+∑' k, descendedTerm A B Γ 2 u s k

theorem forward_residual_im_telescope
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ,
      lensModel s a b θ e₁ e₂ (orbit u s (k+1))-lensModel s a b θ e₁ e₂ (orbit u s k)-1=
        descendedTerm A B Γ 2 u s k) :
    ∀ N : ℕ, (∑ k∈Finset.range N, (descendedTerm A B Γ 2 u s k).im)=
      (lensModel s a b θ e₁ e₂ (orbit u s N)).im-(lensModel s a b θ e₁ e₂ u).im := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    have hh := congrArg Complex.im (hstep N)
    simp only [Complex.sub_im,Complex.one_im,sub_zero] at hh
    linarith

theorem real_forward_model_im_limit (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hlim : Tendsto (orbit (r:ℂ) s) atTop (𝓝 (a:ℂ))) :
    Tendsto (fun k => (lensModel s a b θ e₁ e₂ (orbit r s k)).im)
      atTop (𝓝 (Real.pi/θ+polynomialImag e₁ e₂ a)) := by
  have hreal := real_between_orbit s a b r hs1 hfa hfb har hrb
  have hp : Continuous (polynomialImag e₁ e₂) := by unfold polynomialImag; fun_prop
  have hrLim : Tendsto (fun k => (orbit (r:ℂ) s k).re) atTop (𝓝 a) := by
    have hc := Complex.continuous_re.continuousAt.tendsto.comp hlim
    change Tendsto (fun k => (orbit (r:ℂ) s k).re) atTop (𝓝 a) at hc
    exact hc
  have ht := (hp.continuousAt.tendsto.comp hrLim).const_add (Real.pi/θ)
  apply ht.congr'
  apply Eventually.of_forall
  intro k
  dsimp only [Function.comp_def]
  have he : orbit (r:ℂ) s k=((orbit (r:ℂ) s k).re:ℂ) := by apply Complex.ext <;> simp [(hreal k).1]
  rw [he]
  exact (lensModel_im_real_between s a b θ _ e₁ e₂ (hreal k).2.1 (hreal k).2.2).symm

theorem physicalAttracting_im_real
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hlim : Tendsto (orbit (r:ℂ) s) atTop (𝓝 (a:ℂ)))
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 r s k‖))
    (hstep : ∀ k : ℕ,
      lensModel s a b θ e₁ e₂ (orbit r s (k+1))-lensModel s a b θ e₁ e₂ (orbit r s k)-1=
        descendedTerm A B Γ 2 r s k) :
    (physicalAttracting A B Γ s a b θ e₁ e₂ r).im=Real.pi/θ+polynomialImag e₁ e₂ a := by
  have ht := (Complex.hasSum_im hsum.of_norm.hasSum).tendsto_sum_nat
  have hp := (tendsto_const_nhds (x:=(lensModel s a b θ e₁ e₂ r).im)).add ht
  have he := forward_residual_im_telescope A B Γ s a b θ e₁ e₂ r hstep
  have hl : Tendsto (fun k => (lensModel s a b θ e₁ e₂ (orbit r s k)).im)
      atTop (𝓝 (physicalAttracting A B Γ s a b θ e₁ e₂ r).im) := by
    apply hp.congr'
    apply Eventually.of_forall
    intro k
    simp only [physicalAttracting,Complex.add_im] at *
    linarith [he k]
  exact tendsto_nhds_unique hl (real_forward_model_im_limit s a b θ r e₁ e₂ hs1 har hrb hfa hfb hlim)

theorem interval_source (a b θ Y r : ℝ) (hθ : 0<θ) (hθY : θ*Y≤Real.pi/2)
    (har : a<r) (hrb : r<b) :
    bandTime a b θ r∈strip θ Y ∧ bandChart a b θ (bandTime a b θ r)=(r:ℂ) := by
  have hl : Y<Real.pi/θ := (lt_div_iff₀ hθ).mpr (by nlinarith [Real.pi_pos])
  have him := bandTime_real_between a b θ r har hrb
  refine ⟨?_,bandChart_bandTime a b θ r (by linarith) (ne_of_gt hθ)
    (by exact_mod_cast ne_of_gt har) (by exact_mod_cast ne_of_lt hrb)⟩
  change Y<(bandTime a b θ r).im ∧ (bandTime a b θ r).im<height θ-Y
  rw [him]
  unfold height
  have hp : 2*Real.pi/θ=2*(Real.pi/θ) := by ring
  rw [hp]
  constructor <;> linarith

theorem norm_real_between_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (har : a<r) (hrb : r<b) :
    ‖(r:ℂ)‖<η/4 := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  have ha := (abs_le.mp hc.left_small).1
  have hb := (abs_le.mp hc.right_small).2
  exact abs_lt.mpr ⟨by linarith [hc.radius_pos],by linarith [hc.radius_pos]⟩

/-- The true model identity now holds on the real interval as well as
off the real line. Every continuity input is supplied by actual control. -/
theorem lensControl_real_steps
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    lensModel s a b θ (e₁ s) (e₂ s) (unfolding s r)-lensModel s a b θ (e₁ s) (e₂ s) r-1=
      descendedTerm A B Γ 2 r s 0 ∧
    lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s r)-lensModel s a b θ (e₁ s) (e₂ s) r+1=
      -descendedTerm A B Γ 2 (inverseStep s r) s 0 := by
  have hn := norm_real_between_control e₁ e₂ A B Γ s a b θ Y η M P r hc har hrb
  have haa := Kneser.ActualKoenigsGlobalRealPhase.real_root_gt_neg_one s a hc.left_fixed
  have hgin := inverseReal_between s a b r hs1 haa hc.left_fixed hc.right_fixed har hrb
  have he := inverseStep_ofReal s r (by linarith)
  have hgn : ‖inverseStep s r‖≤η/4 := by
    rw [he]
    exact (norm_real_between_control e₁ e₂ A B Γ s a b θ Y η M P _ hc hgin.1 hgin.2).le
  refine ⟨forward_real_one_step_of_continuity A B Γ s a b θ r η (e₁ s) (e₂ s)
    hs1 har hrb hc.left_fixed hc.right_fixed (by linarith [hc.radius_pos])
      (hc.analytic_residual r hn.le) hc.forward_nonreal_step,
    inverse_real_one_step_of_continuity A B Γ s a b θ r (η/4) (e₁ s) (e₂ s)
      hs1 haa har hrb hc.left_fixed hc.right_fixed hn
        (hc.analytic_residual _ hgn) (fun v hv hi => hc.inverse_nonreal_step v hv.le hi)⟩

theorem actual_real_phases_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    (physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) r).im=Real.pi/θ+polynomialImag (e₁ s) (e₂ s) a ∧
    (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r).im=Real.pi/θ+polynomialImag (e₁ s) (e₂ s) b := by
  obtain ⟨hZ,hchart⟩ := interval_source a b θ Y r hc.theta_pos hc.width har hrb
  have hd := hc.true_orbits (bandTime a b θ r) hZ
  rw [hchart] at hd
  have hF := hd.2.2.2.2.1
  have hG := hd.2.2.2.2.2
  have hLF := true_forward_orbit_tendsto_root r s a b θ (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (fun k => ⟨(hF k).1,(hF k).2.1⟩) (fun k => (hF k).2.2.2.2)
  have hLG := true_inverse_orbit_tendsto_root s a b θ r (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (fun k => ⟨(hG k).1,(hG k).2.1⟩) (fun k => (hG k).2.2.2.2)
  have haa := Kneser.ActualKoenigsGlobalRealPhase.real_root_gt_neg_one s a hc.left_fixed
  have hRF := real_between_orbit s a b r hs1 hc.left_fixed hc.right_fixed har hrb
  have hRG : ∀ k, (inverseOrbit s r k).im=0 ∧ a<(inverseOrbit s r k).re ∧ (inverseOrbit s r k).re<b := by
    intro k
    simpa only [Kneser.ActualInverseLensDynamics.inverseOrbit_eq_iterate] using
      real_between_inverse_orbit s a b r hs1 haa hc.left_fixed hc.right_fixed har hrb k
  have hstepF : ∀ k, lensModel s a b θ (e₁ s) (e₂ s) (orbit r s (k+1))-
      lensModel s a b θ (e₁ s) (e₂ s) (orbit r s k)-1=descendedTerm A B Γ 2 r s k := by
    intro k
    have he : orbit r s k=((orbit r s k).re:ℂ) := by apply Complex.ext <;> simp [(hRF k).1]
    have hh := (lensControl_real_steps e₁ e₂ A B Γ s a b θ Y η M P _ hs1 hc (hRF k).2.1 (hRF k).2.2).1
    rw [←he] at hh
    simpa only [orbit_succ,Kneser.ActualLensDynamics.descendedTerm_at_orbit] using hh
  have hstepG : ∀ k, lensModel s a b θ (e₁ s) (e₂ s) (inverseOrbit s r (k+1))-
      lensModel s a b θ (e₁ s) (e₂ s) (inverseOrbit s r k)+1=
      -descendedTerm A B Γ 2 (inverseOrbit s r (k+1)) s 0 := by
    intro k
    have he : inverseOrbit s r k=((inverseOrbit s r k).re:ℂ) := by apply Complex.ext <;> simp [(hRG k).1]
    have hh := (lensControl_real_steps e₁ e₂ A B Γ s a b θ Y η M P _ hs1 hc (hRG k).2.1 (hRG k).2.2).2
    rw [←he] at hh
    simpa only [inverseOrbit_succ] using hh
  exact ⟨physicalAttracting_im_real A B Γ s a b θ r (e₁ s) (e₂ s) hs1 har hrb hc.left_fixed hc.right_fixed hLF hd.1 hstepF,
    physicalRepelling_im_real A B Γ s a b θ r (e₁ s) (e₂ s) hs1 haa har hrb hc.left_fixed hc.right_fixed hLG hd.2.1 hstepG⟩

/-- Actual preparation constructs both true real phases on the whole split
interval, with no dynamical estimate or real-series input. -/
theorem exists_actual_growing_real_phases
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        ∀ r : ℝ, a<r → r<b →
          (physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) r).im=Real.pi/θ+polynomialImag (e₁ s) (e₂ s) a ∧
          (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r).im=Real.pi/θ+polynomialImag (e₁ s) (e₂ s) b := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  exact ⟨a,b,θ,hc,fun r har hrb => actual_real_phases_of_control e₁ e₂ A B Γ s a b θ Y η M P r
    (by linarith [hss.trans_le hs₀h]) hc har hrb⟩

end Kneser.ActualGrowingRealPhases
end
