import Kneser.ActualFiberRegularWelding
import Kneser.ActualRegularKoenigsInverse

/-! The actual Koenigs inverse composes with the same Fourier sewing
time selected for the all-order theorem. Its physical domain is an
explicit open pullback of the genuine Koenigs image domain; no extension
across a cut or entire physical Kneser function is asserted. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualFiberKoenigsUniformization

open Filter Set Metric Complex
open Kneser.ActualSewnAllOrders Kneser.ActualFiberRegularWelding
open Kneser.ActualSewingTimeAtlas Kneser.ActualRegularKoenigsInverse
open Kneser.FourierSewing Kneser.WeightedFourier
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualRegularWelding
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.GrowingBandGeometry Kneser.GrowingStripFourier
open Kneser.GateFourierDerivative Kneser.RealNormalizationAnchor
open Kneser.PositiveKoenigsOrbit Kneser.ActualKoenigsJacobian
open Kneser.GrowingLensSpatialHolomorphy Kneser.CommonQuadraticBaseline
open Kneser.ExponentialUnfolding Kneser.HolomorphicInjectiveInverse
open Kneser.ActualKoenigsGlobalRealPhase Kneser.ActualKoenigsEntryRealPhase
open Kneser.PositiveLocalKoenigs
open scoped Topology

def centerPoint (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (s : ℝ) (w : Fiber) : ℂ :=
  normalizingCentre (height w.theta) (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) + w.shift

def timeSource (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Set ℂ :=
  {z | centerPoint A B e Γ s w + z ∈ upperSource (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1)}

def physicalDomain (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Set ℂ :=
  timeSource A B e Γ Y P₀ s w ∩
    actualSewnCoordinate A B e Γ Y P₀ s w ⁻¹' regularTimeDomain s w.left realAnchor

def physicalFunction (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (z : ℂ) : ℂ :=
  regularSuperfunction s w.left realAnchor (actualSewnCoordinate A B e Γ Y P₀ s w z)

theorem sewn_time_eq_upper (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (z : ℂ) :
    actualSewnCoordinate A B e Γ Y P₀ s w z =
      upperMap (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.positive
        (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w))
        (centerPoint A B e Γ s w + z) - (height w.theta : ℂ) * I := rfl

theorem time_source_isOpen (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : IsOpen (timeSource A B e Γ Y P₀ s w) :=
  (upperSource_isOpen _).preimage (continuous_const.add continuous_id)

theorem real_anchor_koenigs_ne_zero
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    koenigsValue s a realAnchor ≠ 0 := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hr := actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P hc
  have hanchor : -1<realAnchor := by unfold realAnchor; linarith [Real.exp_pos (-1)]
  have hb := real_left_mem_unit_basin s a realAnchor hs1 ha hc.left_fixed hμ hμ1 hr
    (by linarith [hc.left_neg])
  have hi := (koenigs_unit_basin_data s a hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1).1
  intro he
  have hh := hi hb (unit_basin_root s a hc.left_fixed)
    (by simpa only [koenigsValue_at_root s a hc.left_fixed] using he)
  have hrr : realAnchor=a := by exact_mod_cast hh
  linarith

structure PhysicalFiberData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Prop where
  regular : RegularFiberData A B e Γ Y P₀ s w
  time_analytic : AnalyticOnNhd ℂ (actualSewnCoordinate A B e Γ Y P₀ s w) (timeSource A B e Γ Y P₀ s w)
  time_injective : InjOn (actualSewnCoordinate A B e Γ Y P₀ s w) (timeSource A B e Γ Y P₀ s w)
  domain_open : IsOpen (physicalDomain A B e Γ Y P₀ s w)
  zero_mem : (0:ℂ) ∈ physicalDomain A B e Γ Y P₀ s w
  analytic : AnalyticOnNhd ℂ (physicalFunction A B e Γ Y P₀ s w) (physicalDomain A B e Γ Y P₀ s w)
  normalized : physicalFunction A B e Γ Y P₀ s w 0 = (realAnchor:ℂ)
  time_identity : ∀ z ∈ physicalDomain A B e Γ Y P₀ s w,
    koenigsValue s w.left (physicalFunction A B e Γ Y P₀ s w z) =
      koenigsValue s w.left realAnchor * exp ((Real.log (multiplier s w.left):ℂ) *
        actualSewnCoordinate A B e Γ Y P₀ s w z)
  abel : ∀ z ∈ physicalDomain A B e Γ Y P₀ s w,
    z+1 ∈ physicalDomain A B e Γ Y P₀ s w ∧
      physicalFunction A B e Γ Y P₀ s w (z+1)=unfolding s (physicalFunction A B e Γ Y P₀ s w z)
  seam_domain : ∀ z ∈ symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1-1),
    z-centerPoint A B e Γ s w ∈ physicalDomain A B e Γ Y P₀ s w
  seam : ∀ z ∈ symmetricStrip (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1-1),
    physicalFunction A B e Γ Y P₀ s w (z-centerPoint A B e Γ s w)=lowerPatch A B e Γ Y P₀ s w z
  logarithmic_time_germ : ∀ᶠ z : ℂ in 𝓝 0, z ∈ physicalDomain A B e Γ Y P₀ s w ∧
    log (koenigsValue s w.left (physicalFunction A B e Γ Y P₀ s w z) /
      koenigsValue s w.left realAnchor) / (Real.log (multiplier s w.left):ℂ) =
        actualSewnCoordinate A B e Γ Y P₀ s w z

theorem physical_data_of_fiber_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber)
    (hd : FiberData A B e Γ T Y η Mg P₀ s w) (hs : 0<s) (hs1 : s<1)
    (hH : 3<sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) :
    PhysicalFiberData A B e Γ Y P₀ s w := by
  let C := actualSewnCoordinate A B e Γ Y P₀ s w
  let z₀ := centerPoint A B e Γ s w
  let H := sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1
  let t₀ := gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)
  have hc := hd.control
  have hr := actual_anchor_left_of_control (first (e 1)) (second (e 1)) A B (Γ 1) s
    w.left w.right w.theta Y η Mg P₀ hc
  have hanchor : -1<realAnchor := by unfold realAnchor; linarith [Real.exp_pos (-1)]
  have hdist : w.left-realAnchor<1 := by linarith [hc.left_neg]
  have ha := real_root_gt_neg_one s w.left hc.left_fixed
  have hμ : 0<multiplier s w.left := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s w.left<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hR := regular_domain_holomorphic s w.left realAnchor hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1
  have hreg := regular_data_of_fiber_data A B e Γ T Y η Mg P₀ s w hd hs hs1 hH
  have htime : AnalyticOnNhd ℂ C (timeSource A B e Γ Y P₀ s w) := by
    intro z hz
    exact ((hreg.atlas.upper_analytic _ hz).comp (f:=fun z : ℂ => z₀+z)
      (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hinj : InjOn C (timeSource A B e Γ Y P₀ s w) := by
    intro z hz v hv he
    have hh : upperMap H w.positive t₀ (z₀+z)=upperMap H w.positive t₀ (z₀+v) := by
      exact sub_left_inj.mp he
    exact add_left_cancel (hreg.atlas.upper_injective hz hv hh)
  have hopen : IsOpen (physicalDomain A B e Γ Y P₀ s w) := by
    exact htime.continuousOn.isOpen_inter_preimage (time_source_isOpen A B e Γ Y P₀ s w) hR.1
  have hphase : t₀.im=height w.theta/2 :=
    actual_transition_fourier_mean_phase (first (e 1)) (second (e 1)) A B (Γ 1) s
      w.left w.right w.theta Y η Mg P₀ realAnchor ((w.left+w.right)/2) hs hs1 hc hr
      (by linarith [hc.left_neg,hc.right_pos]) (by linarith [hc.left_neg,hc.right_pos])
      w.inverse hd.inverse_analytic hd.inverse_identity
  have hz₀ : z₀∈upperSource H := by
    have hci := centre_im (height w.theta) t₀ hphase
    have hshift := (Complex.abs_im_le_norm w.shift).trans hd.shift_small
    have hh : 0<height w.theta := by unfold height; exact div_pos (by positivity) hc.theta_pos
    change 1-H<(normalizingCentre (height w.theta) t₀+w.shift).im
    simp only [add_im,hci]
    linarith [(abs_le.mp hshift).1]
  have hzero : C 0=0 := hd.normalized
  have hanc := actual_anchor_domain_and_value (first (e 1)) (second (e 1)) A B (Γ 1)
    s w.left w.right w.theta Y η Mg P₀ hs hs1 hc
  have hzdom : (0:ℂ)∈physicalDomain A B e Γ Y P₀ s w := by
    refine ⟨?_,?_⟩
    · change z₀+0∈upperSource H
      simpa only [add_zero] using hz₀
    · change C 0∈regularTimeDomain s w.left realAnchor
      rw [hzero]
      exact hanc.1
  have hident : ∀z∈physicalDomain A B e Γ Y P₀ s w,
      koenigsValue s w.left (physicalFunction A B e Γ Y P₀ s w z)=
        koenigsValue s w.left realAnchor*exp ((Real.log (multiplier s w.left):ℂ)*C z) := by
    intro z hz
    exact (hR.2.2 _ hz.2).2
  have hseam : ∀z∈symmetricStrip H,
      C (z-z₀)∈regularTimeDomain s w.left realAnchor ∧
      physicalFunction A B e Γ Y P₀ s w (z-z₀)=lowerPatch A B e Γ Y P₀ s w z := by
    intro z hz
    have hm := lowerMap_mem_regular_strip (height w.theta) (boundaryLoss Y P₀) _ w.negative
      hd.negative_norm z hz rfl
    have he := actual_regular_transition_global (first (e 1)) (second (e 1)) A B (Γ 1)
      s w.left w.right w.theta Y η Mg P₀ realAnchor ((w.left+w.right)/2) hs hs1 hc hr hdist
      (by linarith [hc.left_neg,hc.right_pos]) (by linarith [hc.left_neg,hc.right_pos])
      w.inverse hd.inverse_analytic hd.inverse_identity _ hm
    have hh := hd.sewing_identity z hz.le
    change globalTransition A B e Γ s w (lowerMap H w.negative z)=upperMap H w.positive t₀ z at hh
    have he₂ := he.2.1
    have he₄ := he.2.2.2
    change globalTransition A B e Γ s w (lowerMap H w.negative z)-(height w.theta:ℂ)*I∈
      regularTimeDomain s w.left realAnchor at he₂
    change regularSuperfunction s w.left realAnchor
      (globalTransition A B e Γ s w (lowerMap H w.negative z)-(height w.theta:ℂ)*I)=
        lowerPatch A B e Γ Y P₀ s w z at he₄
    rw [hh] at he₂ he₄
    have ht : C (z-z₀)=upperMap H w.positive t₀ z-(height w.theta:ℂ)*I := by
      dsimp only [C]
      rw [sewn_time_eq_upper]
      change upperMap H w.positive t₀ (z₀+(z-z₀))-(height w.theta:ℂ)*I = _
      congr 2
      ring
    change C (z-z₀)∈regularTimeDomain s w.left realAnchor ∧
      regularSuperfunction s w.left realAnchor (C (z-z₀))=lowerPatch A B e Γ Y P₀ s w z
    rw [ht]
    exact ⟨he₂,he₄⟩
  refine ⟨hreg,htime,hinj,hopen,hzdom,?_,?_,hident,?_,?_,?_,?_⟩
  · intro z hz
    exact (hR.2.1 _ hz.2).comp (htime z hz.1)
  · change regularSuperfunction s w.left realAnchor (C 0)=(realAnchor:ℂ)
    rw [hzero]
    exact hanc.2.1
  · intro z hz
    have hh := regular_superfunction_abel s w.left realAnchor hs.le hs1 ha hc.left_neg.le
      hc.left_fixed hμ hμ1 (C z) hz.2
    have htrans : C (z+1)=C z+1 := sewnCoordinate_translation _ _ _ _ _ z
    refine ⟨⟨?_,?_⟩,?_⟩
    · change z₀+(z+1)∈upperSource H
      have hzz : z₀+z∈upperSource H := hz.1
      simpa only [upperSource,mem_ofPred_eq,add_im,one_im,add_zero] using hzz
    · change C (z+1)∈regularTimeDomain s w.left realAnchor
      rw [htrans]
      exact hh.1
    · change regularSuperfunction s w.left realAnchor (C (z+1))=unfolding s _
      rw [htrans]
      exact hh.2
  · intro z hz
    change |z.im|<H-1 at hz
    have hzH : z∈symmetricStrip H := by change |z.im|<H; linarith
    refine ⟨?_,(hseam z hzH).1⟩
    change z₀+(z-z₀)∈upperSource H
    rw [show z₀+(z-z₀)=z by ring]
    have hzlo := (abs_lt.mp (show |z.im|<H-1 from hz)).1
    change 1-H<z.im
    linarith
  · intro z hz
    exact (hseam z (by change |z.im|<H; change |z.im|<H-1 at hz; linarith)).2
  · have hKa := real_anchor_koenigs_ne_zero (first (e 1)) (second (e 1)) A B (Γ 1)
      s w.left w.right w.theta Y η Mg P₀ hs hs1 hc
    have hlog : (Real.log (multiplier s w.left):ℂ)≠0 := by
      exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
    have hCcont := (htime 0 hzdom.1).continuousAt
    have him : ContinuousAt (fun z => ((Real.log (multiplier s w.left):ℂ)*C z).im) 0 :=
      Complex.continuous_im.continuousAt.comp (continuousAt_const.mul hCcont)
    have he0 : ((Real.log (multiplier s w.left):ℂ)*C 0).im=0 := by rw [hzero,mul_zero]; rfl
    have hb : ∀ᶠz : ℂ in 𝓝 0,
        -Real.pi<((Real.log (multiplier s w.left):ℂ)*C z).im ∧
          ((Real.log (multiplier s w.left):ℂ)*C z).im<Real.pi :=
      him.eventually (isOpen_Ioo.mem_nhds (by
        change -Real.pi<((Real.log (multiplier s w.left):ℂ)*C 0).im ∧
          ((Real.log (multiplier s w.left):ℂ)*C 0).im<Real.pi
        rw [he0]
        exact ⟨by linarith [Real.pi_pos],Real.pi_pos⟩))
    filter_upwards [hopen.mem_nhds hzdom,hb] with z hz hbz
    refine ⟨hz,?_⟩
    rw [hident z hz]
    rw [mul_div_cancel_left₀ _ hKa,Complex.log_exp hbz.1 hbz.2.le]
    exact mul_div_cancel_left₀ _ hlog

theorem all_orders_data_physical_uniformization
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W) :
    ∀ᶠs : ℝ in 𝓝[>] 0, PhysicalFiberData A B e Γ Y P₀ s (W s) := by
  have hpos : ∀ᶠs : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hlt : ∀ᶠs : ℝ in 𝓝[>] 0, s<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hd.actual_fibers,all_orders_data_time_atlas U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd,hpos,hlt] with s hs ha hsp hsl
  exact physical_data_of_fiber_data A B e Γ _ Y η Mg P₀ s (W s) hs hsp hsl ha.1

end Kneser.ActualFiberKoenigsUniformization
end
