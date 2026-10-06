import Kneser.NormalizedGrowingFourier
import Kneser.ActualSewingScale
import Kneser.FourierSewingQuantitative
import Kneser.FourierSewingIntegralCoefficient

/-! The quantitative Fourier sewing construction is instantiated with the
true normalized growing transition. Numerical smallness is derived from
large genuine multiplier height; no sewing solution or coefficient
comparison is supplied as an assumption. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Kneser.ActualNormalizedSewing

open Filter Set Metric Complex
open Kneser.GrowingBandGeometry Kneser.GrowingStripFourier
open Kneser.NormalizedGrowingFourier Kneser.ActualNormalizedGrowingTransition
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualGrowingCoordinateInverse
open Kneser.GrowingLensSpatialHolomorphy Kneser.GateFourierDerivative
open Kneser.ReflectedOrbitChainCoefficient Kneser.FourierSewing
open Kneser.WeightedFourier Kneser.ActualLambdaFlatness
open scoped Topology

theorem fixed_sewing_gap_small :
    2*4*Real.exp (-2*Real.pi*64)/(1-Real.exp (-2*Real.pi*64))≤(1:ℝ) ∧
    4*Real.pi*4*Real.exp (-2*Real.pi*64)/(1-Real.exp (-2*Real.pi*64))^2≤(1/2:ℝ) := by
  let q : ℝ := Real.exp (-2*Real.pi*64)
  have hq : 0<q := Real.exp_pos _
  have he : q=1/Real.exp (128*Real.pi) := by
    dsimp [q]
    rw [show -2*Real.pi*64=-(128*Real.pi) by ring,Real.exp_neg,inv_eq_one_div]
  have hh := Real.add_one_le_exp (128*Real.pi)
  have h16 : q≤1/16 := by
    rw [he]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_three])
  have h128 : q≤1/(128*Real.pi) := by
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hden : 0<1-q := by linarith
  constructor
  · change 2*4*q/(1-q)≤1
    norm_num only [show (2:ℝ)*4=8 by norm_num]
    apply (div_le_iff₀ hden).mpr
    linarith
  · change 4*Real.pi*4*q/(1-q)^2≤1/2
    rw [show (4:ℝ)*Real.pi*4=16*Real.pi by ring]
    have hb : 128*Real.pi*q≤1 := by
      have hh := (le_div_iff₀ (by positivity : 0<128*Real.pi)).mp h128
      nlinarith only [hh]
    have hs : (1/2:ℝ)^2≤(1-q)^2 := by nlinarith
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith

theorem tendsto_lambda_height : Tendsto lambda atTop (𝓝 0) := by
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_id : Tendsto (fun h : ℝ => h) atTop atTop).const_mul_atTop
      (by positivity : 0<2*Real.pi))
  convert ht using 1
  funext h
  unfold lambda
  congr 1
  simp only [id_eq]
  ring

/-- All sewing smallness conditions hold above one fixed height. The
threshold depends only on the fixed boundary loss, not on the roots. -/
theorem exists_sewing_height_threshold (Y : ℝ) :
    ∃ H₀ : ℝ, ∀h : ℝ, H₀≤h →
      0≤sewingWidth h Y 64 1 ∧
      lambda h*gapFactor Y 64 1≤1/2 ∧
      lambda h*pointFactor Y 64 1≤1/2 ∧
      normalizationConstant Y 64 1 4*lambda h≤1 ∧
      ∀t₀ : ℂ, t₀.im=h/2 →
        normalizationLipschitzBound (sewingWidth h Y 64 1) (normalizingCentre h t₀) 1≤1/2 := by
  have hgap : Tendsto (fun h : ℝ => lambda h*gapFactor Y 64 1) atTop (𝓝 0) := by
    simpa using tendsto_lambda_height.mul_const (gapFactor Y 64 1)
  have hpoint : Tendsto (fun h : ℝ => lambda h*pointFactor Y 64 1) atTop (𝓝 0) := by
    simpa using tendsto_lambda_height.mul_const (pointFactor Y 64 1)
  have hnorm : Tendsto (fun h : ℝ => normalizationConstant Y 64 1 4*lambda h) atTop (𝓝 0) := by
    simpa using tendsto_lambda_height.const_mul (normalizationConstant Y 64 1 4)
  have hden : Tendsto (fun h : ℝ => (1-lambda h*pointFactor Y 64 1)^2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).sub hpoint).pow 2
  have hlip : Tendsto (fun h : ℝ => 4*Real.pi*(lambda h*pointFactor Y 64 1)/
      (1-lambda h*pointFactor Y 64 1)^2) atTop (𝓝 0) := by
    have hh := (hpoint.const_mul (4*Real.pi)).div hden (by norm_num : (1:ℝ)≠0)
    change Tendsto (fun h : ℝ => 4*Real.pi*(lambda h*pointFactor Y 64 1)/
      (1-lambda h*pointFactor Y 64 1)^2) atTop (𝓝 ((4*Real.pi*0)/1)) at hh
    simpa only [mul_zero,zero_div] using hh
  have he : ∀ᶠh : ℝ in atTop,
      0≤sewingWidth h Y 64 1 ∧
      lambda h*gapFactor Y 64 1≤1/2 ∧
      lambda h*pointFactor Y 64 1≤1/2 ∧
      normalizationConstant Y 64 1 4*lambda h≤1 ∧
      (4*Real.pi*(lambda h*pointFactor Y 64 1)/(1-lambda h*pointFactor Y 64 1)^2≤1/2) := by
    filter_upwards [eventually_ge_atTop (2*(Y+66)),
      hgap.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hpoint.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hnorm.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
      hlip.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with h hh hg hp hn hl
    refine ⟨?_,hg.le,hp.le,hn.le,hl.le⟩
    unfold sewingWidth bandWidth
    linarith
  obtain ⟨H₀,hall⟩ := eventually_atTop.mp he
  refine ⟨H₀,fun h hh => ?_⟩
  obtain ⟨hH,hg,hp,hn,hl⟩ := hall h hh
  refine ⟨hH,hg,hp,hn,?_⟩
  intro t₀ ht₀
  unfold normalizationLipschitzBound
  rw [point_rate_identity h Y 64 1 t₀ ht₀]
  simpa only [mul_one] using hl

/-- The actual parameter-height has exactly the actual sewing factor. -/
theorem actual_height_lambda
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    lambda (height θ)=lambdaFactor s a := by
  unfold lambda height lambdaFactor
  rw [hc.theta_actual]
  change Real.exp (-2*Real.pi*(2*Real.pi/(-Real.log ((1-s)*(1+a)))))=
    Real.exp (4*Real.pi^2/Real.log ((1-s)*(1+a)))
  congr 1
  ring


/-- A genuine sewing solution and its actual normalized Fourier integrals.
The same Q, P and normalizing translation work for every positive mode. -/
def SewingWitness (h Y : ℝ) (T : ℂ → ℂ) : Prop :=
  ∃Q P : Space, ∃ζ : ℂ,
    Q∈Negative ∧ ‖Q‖≤1 ∧
    (∀n : ℤ, n<0 → P n=0) ∧ ‖P‖≤1 ∧
    ‖ζ‖≤normalizationConstant Y 64 1 4*lambda h ∧ ‖ζ‖≤1 ∧
    (normalizingCentre h (gateFourierCoefficient 0 0 T)+ζ)+
      evaluate (sewingWidth h Y 64 1) P (normalizingCentre h (gateFourierCoefficient 0 0 T)+ζ)=
        normalizingCentre h (gateFourierCoefficient 0 0 T) ∧
    sewnCoordinate (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ 0=0 ∧
    (∀z : ℂ, |z.im|≤sewingWidth h Y 64 1 →
      T (z+evaluate (sewingWidth h Y 64 1) Q z)=
        z+gateFourierCoefficient 0 0 T+evaluate (sewingWidth h Y 64 1) P z) ∧
    (∀n : ℕ, 1≤n →
      translatedCoefficient (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ n=
        ∫x : ℝ in (0:ℝ)..1,
          sewnDisplacement (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ (x:ℂ)*
            exp (-Kneser.fourierFrequency n*(x:ℂ))) ∧
    (∀n : ℕ, 1≤n →
      ‖translatedCoefficient (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ n/(lambda h:ℂ)^n-
        gateFourierCoefficient n 0 T*hornPhase (gateFourierCoefficient 0 0 T) n‖≤
          comparisonConstant Y 64 1 4 n*lambda h)

theorem sewing_witness_of_actual_normalized_fourier
    (T : ℂ → ℂ) (h Y : ℝ)
    (hH : 0≤sewingWidth h Y 64 1) (hheight : 2≤h)
    (htphase : (gateFourierCoefficient 0 0 T).im=h/2)
    (htzero : gateFourierCoefficient 0 0 (meanRemoved T)=0)
    (htsame : ∀n : ℤ, n≠0 → gateFourierCoefficient n 0 (meanRemoved T)=gateFourierCoefficient n 0 T)
    (ht : ∀n : ℤ, ‖gateFourierCoefficient n 0 (meanRemoved T)‖≤
      4*Real.exp (-2*Real.pi*bandWidth h Y*|(n:ℝ)|))
    (hseries : ∀z : ℂ, |z.im|<bandWidth h Y → HasSum (fun n : ℤ =>
      gateFourierCoefficient n 0 (meanRemoved T)*exp (Kneser.fourierFrequency n*z))
      (T z-z-gateFourierCoefficient 0 0 T))
    (hg : lambda h*gapFactor Y 64 1≤1/2)
    (hp : lambda h*pointFactor Y 64 1≤1/2)
    (hn : normalizationConstant Y 64 1 4*lambda h≤1)
    (hl : normalizationLipschitzBound (sewingWidth h Y 64 1)
      (normalizingCentre h (gateFourierCoefficient 0 0 T)) 1≤1/2) :
    SewingWitness h Y T := by
  let t : ℤ → ℂ := fun n => gateFourierCoefficient n 0 (meanRemoved T)
  let t₀ := gateFourierCoefficient 0 0 T
  have hdecay : ∀m : ℤ, m≠0 → ‖t m‖≤4*Real.exp (-2*Real.pi*|(m:ℝ)| *bandWidth h Y) := by
    intro m _
    convert ht m using 1
    congr 2
    ring
  obtain ⟨Q,P,ζ,hneg,hQ,hpos,hP,_hproj,_hfixed,hζ,hζ1,hroot,hseam,hcomp⟩ :=
    exists_quantitative_sewing h Y 64 1 4 (by norm_num) (by norm_num) (by norm_num) hH t₀ htphase t htzero hdecay
      fixed_sewing_gap_small.1 fixed_sewing_gap_small.2 hg hp hn hl
  refine ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,hζ1,hroot,sewnCoordinate_zero _ _ _ _ _ hroot,?_,?_,?_⟩
  · intro z hz
    let q := evaluate (sewingWidth h Y 64 1) Q z
    have hq : ‖q‖≤1 := (norm_evaluate_le _ Q z hz).trans hQ
    have him : |(z+q).im|<bandWidth h Y := by
      have he := abs_add_le z.im q.im
      rw [Complex.add_im]
      have hqi := (Complex.abs_im_le_norm q).trans hq
      unfold sewingWidth at hz
      linarith
    have hsum := (hseries (z+q) him).tsum_eq
    have hsum' : periodicFunction t (z+q)=T (z+q)-(z+q)-t₀ := hsum
    have hh := hseam z hz
    change (z+q)+t₀+periodicFunction t (z+q)=z+t₀+evaluate (sewingWidth h Y 64 1) P z at hh
    rw [hsum'] at hh
    linear_combination hh
  · intro n hn
    have hpoint : 0≤sewingWidth h Y 64 1+(normalizingCentre h t₀+ζ).im := by
      have hc := centre_im h t₀ htphase
      have hζim := (Complex.abs_im_le_norm ζ).trans hζ1
      rw [Complex.add_im,hc]
      linarith [(abs_le.mp hζim).1]
    exact translatedCoefficient_eq_intervalIntegral _ _ _ hpos _ _ hpoint n hn
  · intro n hn
    have hh := hcomp n hn
    have hne : (n:ℤ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt (by omega : 0<n))
    simpa only [t,htsame n hne] using hh

/-- On every genuine lens control, sufficiently large actual height
constructs the normalized sewing solution and all-mode Lambda comparison. -/
theorem actual_normalized_sewing_of_height
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w)
    (hH : 0≤sewingWidth (height θ) (boundaryLoss Y P) 64 1)
    (hg : lambda (height θ)*gapFactor (boundaryLoss Y P) 64 1≤1/2)
    (hp : lambda (height θ)*pointFactor (boundaryLoss Y P) 64 1≤1/2)
    (hn : normalizationConstant (boundaryLoss Y P) 64 1 4*lambda (height θ)≤1)
    (hl : ∀t₀ : ℂ, t₀.im=height θ/2 →
      normalizationLipschitzBound (sewingWidth (height θ) (boundaryLoss Y P) 64 1)
        (normalizingCentre (height θ) t₀) 1≤1/2) :
    SewingWitness (height θ) (boundaryLoss Y P)
      (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V) := by
  obtain ⟨_hd,hphase,_hreal,hzero,hsame,_hbound,hdecay,hseries⟩ :=
    actual_normalized_fourier e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hV hVs
  have hheight : 2≤height θ := by
    have hh : 16*Y≤height θ := by
      unfold height
      apply (le_div_iff₀ hc.theta_pos).mpr
      nlinarith only [hc.very_strong_width]
    linarith only [hh,hc.height_large]
  exact sewing_witness_of_actual_normalized_fourier _ (height θ) (boundaryLoss Y P) hH hheight
    hphase hzero hsame hdecay hseries hg hp hn (hl _ hphase)


/-- For the same actual preparation and actual anchor, the full-width
Fourier sewing solution exists throughout a positive parameter germ.
The error factor equals the multiplier-defined Lambda exactly. -/
theorem exists_actual_normalized_sewing
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃Y η M P : ℝ, 2≤Y ∧
      ∀ᶠs : ℝ in 𝓝[>] 0, ∃a b θ : ℝ, ∃V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)) ∧
        (∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
          repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
        lambda (height θ)=lambdaFactor s a ∧
        let T := transition A B Γ s a b θ Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) (e₁ s) (e₂ s) V
        (gateFourierCoefficient 0 0 T).im=height θ/2 ∧
        SewingWitness (height θ) (boundaryLoss Y P) T := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  obtain ⟨H₀,hheight⟩ := exists_sewing_height_threshold (boundaryLoss Y P)
  have hsmall : ∀ᶠs : ℝ in 𝓝[>] 0,
      s<s₀ ∧ s<Real.exp (-2*Real.pi*H₀) :=
    ((eventually_lt_nhds hs₀).and (eventually_lt_nhds (Real.exp_pos _))).filter_mono nhdsWithin_le_nhds
  refine ⟨Y,η,M,P,hY,?_⟩
  filter_upwards [hsmall,actual_lambda_flat 1,self_mem_nhdsWithin] with s hss hflat hs
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss.1
  have ha : -1/2≤a := by
    have hh := (abs_le.mp hc.left_small).1
    linarith only [hh,hc.radius_small]
  have hscale := actual_height_lambda e₁ e₂ A B Γ s a b θ Y η M P hc
  have hΛ : lambda (height θ)≤s := by
    rw [hscale]
    simpa only [pow_one] using hflat a ha hc.left_neg hc.left_fixed
  have hH₀ : H₀≤height θ := by
    have he : Real.exp (-2*Real.pi*height θ)<Real.exp (-2*Real.pi*H₀) := hΛ.trans_lt hss.2
    have hi := Real.exp_lt_exp.mp he
    nlinarith only [hi,Real.pi_pos]
  obtain ⟨hH,hg,hp,hn,hl⟩ := hheight (height θ) hH₀
  obtain ⟨_Vp,V,_hVp,hV,_hspecp,hspec⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  have hs1 : s<1 := by linarith [hss.1.trans_le hs₀h]
  have har : a<(a+b)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (a+b)/2<b := by linarith [hc.left_neg,hc.right_pos]
  have hr₀ := actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P hc
  refine ⟨a,b,θ,V,hc,hV,hspec,hscale,
    actual_transition_fourier_mean_phase e₁ e₂ A B Γ s a b θ Y η M P
      Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) hs hs1 hc hr₀ har hrb V hV hspec,?_⟩
  exact actual_normalized_sewing_of_height e₁ e₂ A B Γ s a b θ Y η M P
    Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) hs hs1 hc hr₀ har hrb V hV hspec hH hg hp hn hl


/-- The compared sewn coefficient is the true interval-integral Fourier
coefficient of the normalized sewn coordinate, not a surrogate sequence. -/
theorem actual_sewn_coefficient_comparison (h Y : ℝ) (T : ℂ → ℂ)
    (hw : SewingWitness h Y T) :
    ∃Q P : Space, ∃ζ : ℂ,
      Q∈Negative ∧ ‖Q‖≤1 ∧ (∀n : ℤ, n<0 → P n=0) ∧ ‖P‖≤1 ∧
      ‖ζ‖≤normalizationConstant Y 64 1 4*lambda h ∧ ‖ζ‖≤1 ∧
      sewnCoordinate (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ 0=0 ∧
      (∀z : ℂ, |z.im|≤sewingWidth h Y 64 1 →
        T (z+evaluate (sewingWidth h Y 64 1) Q z)=
          z+gateFourierCoefficient 0 0 T+evaluate (sewingWidth h Y 64 1) P z) ∧
      ∀n : ℕ, 1≤n →
        ‖gateFourierCoefficient n 0 (sewnCoordinate (sewingWidth h Y 64 1) h P
          (gateFourierCoefficient 0 0 T) ζ)/(lambda h:ℂ)^n-
          gateFourierCoefficient n 0 T*hornPhase (gateFourierCoefficient 0 0 T) n‖≤
            comparisonConstant Y 64 1 4 n*lambda h := by
  obtain ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,hζ1,_hroot,hzero,hseam,hint,hcomp⟩ := hw
  refine ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,hζ1,hzero,hseam,?_⟩
  intro n hn
  have he : translatedCoefficient (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ n=
      gateFourierCoefficient n 0 (sewnCoordinate (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ) := by
    rw [hint n hn]
    simp only [gateFourierCoefficient,gatePoint,gateWeight,Complex.ofReal_zero,mul_zero,add_zero,sewnDisplacement]
  rw [←he]
  exact hcomp n hn

/-- The genuine normalized sewing coordinate and actual horn coefficient
are compared at every positive mode with the actual multiplier-defined
Lambda. The same actual preparation, inverse, Q, P and shift are retained. -/
theorem exists_actual_integral_lambda_comparison
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃Y η M P₀ : ℝ, 2≤Y ∧
      ∀ᶠs : ℝ in 𝓝[>] 0, ∃a b θ : ℝ, ∃V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P₀ ∧
        AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P₀)) ∧
        (∀w∈strip θ (3*Y+boundaryMargin P₀), V w∈strip θ (3*Y) ∧
          repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
        let T := transition A B Γ s a b θ Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) (e₁ s) (e₂ s) V
        (gateFourierCoefficient 0 0 T).im=height θ/2 ∧
        ∃Q P : Space, ∃ζ : ℂ,
          Q∈Negative ∧ ‖Q‖≤1 ∧ (∀n : ℤ, n<0 → P n=0) ∧ ‖P‖≤1 ∧
          ‖ζ‖≤normalizationConstant (boundaryLoss Y P₀) 64 1 4*lambdaFactor s a ∧ ‖ζ‖≤1 ∧
          sewnCoordinate (sewingWidth (height θ) (boundaryLoss Y P₀) 64 1) (height θ) P
            (gateFourierCoefficient 0 0 T) ζ 0=0 ∧
          (∀z : ℂ, |z.im|≤sewingWidth (height θ) (boundaryLoss Y P₀) 64 1 →
            T (z+evaluate (sewingWidth (height θ) (boundaryLoss Y P₀) 64 1) Q z)=
              z+gateFourierCoefficient 0 0 T+evaluate (sewingWidth (height θ) (boundaryLoss Y P₀) 64 1) P z) ∧
          ∀n : ℕ, 1≤n →
            ‖gateFourierCoefficient n 0 (sewnCoordinate (sewingWidth (height θ) (boundaryLoss Y P₀) 64 1) (height θ) P
              (gateFourierCoefficient 0 0 T) ζ)/(lambdaFactor s a:ℂ)^n-
              gateFourierCoefficient n 0 T*hornPhase (gateFourierCoefficient 0 0 T) n‖≤
                comparisonConstant (boundaryLoss Y P₀) 64 1 4 n*lambdaFactor s a := by
  obtain ⟨Y,η,M,P₀,hY,hall⟩ := exists_actual_normalized_sewing U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,η,M,P₀,hY,?_⟩
  filter_upwards [hall] with s hs
  obtain ⟨a,b,θ,V,hc,hV,hVs,hscale,hphase,hw⟩ := hs
  refine ⟨a,b,θ,V,hc,hV,hVs,hphase,?_⟩
  have hh := actual_sewn_coefficient_comparison (height θ) (boundaryLoss Y P₀) _ hw
  simpa only [hscale] using hh

end Kneser.ActualNormalizedSewing
end
