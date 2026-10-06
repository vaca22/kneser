import Kneser.RealOrderedRootUniqueness
import Kneser.PreparedModelAtZero
import Kneser.ActualLensModel
import Kneser.ActualLensGeometry
import Kneser.JointAnalyticFiniteTaylor

/-! The genuine two-root band time converges to the parabolic inverse
coordinate. The numerator estimate follows from actual joint analytic
Taylor bounds, and the multiplier-log factor cancels the root velocity.
The arbitrary ordered real roots are matched to the SAME preparation. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualBandTimeConfluence

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialPreparedModel
open Kneser.ParabolicExponentialOrbit Kneser.PositiveKoenigsOrbit
open Kneser.GrowingBandGeometry Kneser.ApolloniusGeometry Kneser.RealOrderedRootUniqueness
open Kneser.JointAnalyticFiniteTaylor Kneser.FiniteExpansionHolomorphy
open scoped Topology

def logarithmicRatio (U : ℂ → ℂ) (x u : ℂ) : ℂ :=
  Complex.log ((u - U x) / (u - U (-x)))

def ratioFirstCoefficient (U : ℂ → ℂ) (u : ℂ) : ℂ := -2 * deriv U 0 / u

def preparationBandTime (U H : ℂ → ℂ) (x u : ℂ) : ℂ :=
  logarithmicRatio U x u / (x * H x)

theorem logarithmicRatio_zero (U : ℂ → ℂ) (hU0 : U 0 = 0) (u : ℂ) (hu : u ≠ 0) :
    logarithmicRatio U 0 u = 0 := by simp [logarithmicRatio, hU0, div_self hu]

theorem hasDerivAt_logarithmicRatio (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0)
    (hU0 : U 0 = 0) (u : ℂ) (hu : u ≠ 0) :
    HasDerivAt (fun x => logarithmicRatio U x u) (ratioFirstCoefficient U u) 0 := by
  have hUn : HasDerivAt (fun x : ℂ => U (-x)) (-deriv U 0) 0 := by
    have h := hU.hasStrictDerivAt.hasDerivAt.comp_of_eq (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).neg) (by simp)
    change HasDerivAt (fun x : ℂ => U (-x)) (deriv U 0 * -1) 0 at h
    simpa only [mul_neg_one] using h
  have hquot := ((hasDerivAt_const (0 : ℂ) u).sub hU.hasStrictDerivAt.hasDerivAt).div
    ((hasDerivAt_const (0 : ℂ) u).sub hUn) (by
      change u - U (-0) ≠ 0
      simpa only [hU0, neg_zero, sub_zero] using hu)
  simp only [Pi.sub_apply] at hquot
  have hlog := hquot.clog (by
    change (u - U 0) / (u - U (-0)) ∈ Complex.slitPlane
    simpa only [hU0, neg_zero, sub_zero, div_self hu] using Complex.one_mem_slitPlane)
  convert hlog using 1
  · rfl
  · dsimp only [ratioFirstCoefficient, Pi.sub_apply, Pi.div_apply]
    simp only [hU0, neg_zero, sub_zero, div_self hu, div_one, zero_sub, sub_neg_eq_add]
    field_simp
    ring

theorem analyticAt_logarithmicRatio_joint (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0)
    (hU0 : U 0 = 0) (u : ℂ) (hu : u ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => logarithmicRatio U p.1 p.2) (0, u) := by
  have hUp : AnalyticAt ℂ (fun p : ℂ × ℂ => U p.1) (0, u) :=
    hU.comp_of_eq analyticAt_fst rfl
  have hUn : AnalyticAt ℂ (fun p : ℂ × ℂ => U (-p.1)) (0, u) :=
    hU.comp_of_eq analyticAt_fst.neg (by simp)
  exact ((analyticAt_snd.sub hUp).div (analyticAt_snd.sub hUn)
    (by simpa only [Pi.sub_apply, hU0, neg_zero, sub_zero] using hu)).clog
      (by simpa only [Pi.sub_apply, Pi.div_apply, hU0, neg_zero, sub_zero, div_self hu]
        using Complex.one_mem_slitPlane)

theorem logarithmicRatio_first_taylor_coefficient (U : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (u : ℂ) (hu : u ≠ 0) :
    coefficient (fun p : ℂ × ℂ => logarithmicRatio U p.1 p.2) 1 u = ratioFirstCoefficient U u := by
  unfold coefficient Kneser.CauchyHigherTaylor.coefficient
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact (hasDerivAt_logarithmicRatio U hU hU0 u hu).deriv

theorem exists_local_numerator_remainder (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0)
    (hU0 : U 0 = 0) (u₀ : ℂ) (hu₀ : u₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖x‖ ≤ r / 2 →
      ∀ u ∈ closedBall u₀ r, u ≠ 0 →
        ‖logarithmicRatio U x u - x * ratioFirstCoefficient U u‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨r, hr, C, hC, _ha, he⟩ := exists_uniform_finite_taylor
    (fun p : ℂ × ℂ => logarithmicRatio U p.1 p.2) u₀
    (analyticAt_logarithmicRatio_joint U hU hU0 u₀ hu₀) 1
  refine ⟨r, hr, C, hC, ?_⟩
  intro x hx u hu hune
  have hpoly : complexPolynomial (coefficient (fun p : ℂ × ℂ => logarithmicRatio U p.1 p.2)) 1 x u =
      x * ratioFirstCoefficient U u := by
    simp only [complexPolynomial, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, one_mul, pow_one, coefficient_zero, logarithmicRatio_zero U hU0 u hune,
      logarithmicRatio_first_taylor_coefficient U hU hU0 u hune]
  simpa only [hpoly] using he x hx u hu

/-- Compact uniformity is derived from genuine local joint Taylor bounds;
no uniform coordinate or inverse expansion is an input. -/
theorem preparationBandTime_uniform_compact (U H : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = deriv U 0)
    (S : Set ℂ) (hS : IsCompact S) (hne : ∀ u ∈ S, u ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℂ in 𝓝 0, ∀ u ∈ S, x ≠ 0 →
      ‖preparationBandTime U H x u - inverseCoordinate u‖ < ε := by
  apply hS.eventually_forall_of_forall_eventually
  intro u₀ hu₀
  have hu0 := hne u₀ hu₀
  have hHne : H 0 ≠ 0 := by rwa [hH0]
  obtain ⟨r, hr, C, hC, hrem⟩ := exists_local_numerator_remainder U hU hU0 u₀ hu0
  let I : ℝ := ‖(H 0)⁻¹‖ + 1
  have hIpos : 0 < I := by dsimp [I]; positivity
  let g : ℂ × ℂ → ℂ := fun p => ratioFirstCoefficient U p.2 / H p.1 - inverseCoordinate p.2
  have hcH : ContinuousAt (fun p : ℂ × ℂ => H p.1) (0, u₀) :=
    hH.continuousAt.comp_of_eq (f := fun p : ℂ × ℂ => p.1) continuous_fst.continuousAt rfl
  have hcD : ContinuousAt (fun p : ℂ × ℂ => ratioFirstCoefficient U p.2) (0, u₀) :=
    continuousAt_const.div continuous_snd.continuousAt hu0
  have hcZ : ContinuousAt (fun p : ℂ × ℂ => inverseCoordinate p.2) (0, u₀) :=
    continuousAt_const.div continuous_snd.continuousAt hu0
  have hcg : ContinuousAt g (0, u₀) := (hcD.div hcH hHne).sub hcZ
  have hg0 : g (0, u₀) = 0 := by
    dsimp only [g, ratioFirstCoefficient, inverseCoordinate]
    rw [hH0]
    field_simp
    ring
  have hge : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), ‖g p‖ < ε / 2 :=
    hcg.norm.eventually (gt_mem_nhds (by simpa only [hg0, norm_zero] using half_pos hε))
  have hIe : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), ‖(H p.1)⁻¹‖ < I :=
    (hcH.inv₀ hHne).norm.eventually (gt_mem_nhds (by dsimp [I]; linarith))
  have hsmall : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), C * ‖p.1‖ * I < ε / 2 := by
    have hc : ContinuousAt (fun p : ℂ × ℂ => C * ‖p.1‖ * I) (0, u₀) := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa using half_pos hε))
  have hXe : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), ‖p.1‖ ≤ r / 2 :=
    (continuous_fst.continuousAt.norm.eventually
      (gt_mem_nhds (by simpa using half_pos hr))).mono fun _ hp => hp.le
  have hUe : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), p.2 ∈ closedBall u₀ r :=
    continuous_snd.continuousAt.eventually (closedBall_mem_nhds _ hr)
  have hUne : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually (eventually_ne_nhds hu0)
  have hHene : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, u₀), H p.1 ≠ 0 :=
    hcH.eventually (eventually_ne_nhds hHne)
  filter_upwards [hge, hIe, hsmall, hXe, hUe, hUne, hHene] with p hg hi hs hx hu hune hh hxn
  have hn : 0 < ‖p.1‖ := norm_pos_iff.mpr hxn
  have he := hrem p.1 hx p.2 hu hune
  have hd : ‖(logarithmicRatio U p.1 p.2 - p.1 * ratioFirstCoefficient U p.2) / p.1‖ ≤ C * ‖p.1‖ := by
    rw [norm_div]
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ C * ‖p.1‖ ^ 2 := he
      _ = _ := by ring
  have hid : preparationBandTime U H p.1 p.2 - inverseCoordinate p.2 =
      ((logarithmicRatio U p.1 p.2 - p.1 * ratioFirstCoefficient U p.2) / p.1) * (H p.1)⁻¹ + g p := by
    dsimp only [preparationBandTime, g]
    field_simp
    ring
  rw [hid]
  have hb : ‖((logarithmicRatio U p.1 p.2 - p.1 * ratioFirstCoefficient U p.2) / p.1) * (H p.1)⁻¹‖ ≤
      C * ‖p.1‖ * I := by
    rw [norm_mul]
    exact mul_le_mul hd hi.le (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem actual_negative_root_gt_neg_one (s a : ℝ)
    (hfa : unfolding (s : ℂ) (a : ℂ) = (a : ℂ)) : -1 < a := by
  have hz := realDefect_zero_of_actual_root s a hfa
  dsimp only [Kneser.RealExponentialRoots.realDefect] at hz
  linarith [Real.exp_pos (-s + (1 - s) * a)]

theorem bandTime_eq_preparation_upper (U H : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (s a b : ℝ) (x u : ℂ) (hs1 : s < 1) (ha : -1 < a) (hab : a < b)
    (hx : x ^ 2 = (s : ℂ)) (hUa : U x = (a : ℂ)) (hUb : U (-x) = (b : ℂ))
    (hu : 0 < u.im) :
    bandTime a b (-Real.log (multiplier s a)) u = preparationBandTime U H x u := by
  have hμ : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hl : x * H x = (Real.log (multiplier s a) : ℂ) := by
    rw [← hHlog, Kneser.ActualKoenigsIdentification.rootMultiplier_of_real_value U s a x hx hUa,
      ← Complex.ofReal_log hμ.le]
  unfold bandTime preparationBandTime logarithmicRatio
  rw [Kneser.ActualLensModel.log_neg_of_im_neg _
    (Kneser.ActualLensModel.crossRatio_im_neg a b u hab hu), hUa, hUb, hl]
  simp only [add_sub_cancel_right, Complex.ofReal_neg, neg_div_neg_eq]
  rfl

/-- The same actual preparation and arbitrary true ordered roots yield
compact uniform confluence on the physical upper half-plane. The exact
bandChart inverse identity is retained with the same roots and time. -/
theorem actual_bandTime_uniform_upper_compact (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ)
    (S : Set ℂ) (hS : IsCompact S) (hupper : ∀ u ∈ S, 0 < u.im)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      ∀ u ∈ S, ‖bandTime a b (-Real.log (multiplier s a)) u - inverseCoordinate u‖ < ε ∧
        bandChart a b (-Real.log (multiplier s a)) (bandTime a b (-Real.log (multiplier s a)) u) = u := by
  obtain ⟨s₀, hs₀, hmatch⟩ := exists_uniform_actual_root_matching U H e₁ e₂ A B K F Γ hdata
  have hU := hdata.1
  have hU0 := hdata.2.1
  have hUd := hdata.2.2.1
  have hH := hdata.2.2.2.1
  have hHlog := hdata.2.2.2.2.2.1
  have hH0 := Kneser.PreparedModelAtZero.log_factor_zero_eq_root_deriv U H hU hU0 hH hHlog
  have hne : ∀ u ∈ S, u ≠ 0 := by
    intro u hu he
    have hi := hupper u hu
    simp only [he, Complex.zero_im] at hi
    linarith
  have he := preparationBandTime_uniform_compact U H hU hU0 hUd hH hH0 S hS hne ε hε
  have hsqrt : Tendsto (fun s : ℝ => (Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have hc : ContinuousAt (fun s : ℝ => (Real.sqrt s : ℂ)) (0 : ℝ) :=
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
    simpa only [Real.sqrt_zero, Complex.ofReal_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsqrtn : Tendsto (fun s : ℝ => -(Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [neg_zero] using hsqrt.neg
  have hp : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hl : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min s₀ 1 :=
    (eventually_lt_nhds (lt_min hs₀ (by norm_num))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsqrt.eventually he, hsqrtn.eventually he, hp, hl] with s hx hn hs hss
  intro a b ha hb hfa hfb u hu
  have hs1 : s < 1 := hss.trans_le (min_le_right _ _)
  have ha1 := actual_negative_root_gt_neg_one s a hfa
  have hsx : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  have hsxn : (Real.sqrt s : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hs)
  have hma := hmatch s a b hs (hss.trans_le (min_le_left _ _)) ha hb hfa hfb _ hsx
  have hbound : ‖bandTime a b (-Real.log (multiplier s a)) u - inverseCoordinate u‖ < ε := by
    rcases hma with hm | hm
    · rw [bandTime_eq_preparation_upper U H hHlog s a b _ u hs1 ha1 (ha.trans hb) hsx hm.1 hm.2 (hupper u hu)]
      exact hx u hu hsxn
    · rw [bandTime_eq_preparation_upper U H hHlog s a b (-(Real.sqrt s : ℂ)) u hs1 ha1
        (ha.trans hb) (by simpa only [neg_sq] using hsx) hm.2 (by simpa only [neg_neg] using hm.1) (hupper u hu)]
      exact hn u hu (neg_ne_zero.mpr hsxn)
  have hμ : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by dsimp only [multiplier]; nlinarith
  have hθ : 0 < -Real.log (multiplier s a) := neg_pos.mpr (Real.log_neg hμ hμ1)
  have hno (r : ℝ) : u ≠ (r : ℂ) := by
    intro heq
    have hi := hupper u hu
    simp only [heq, Complex.ofReal_im] at hi
    linarith
  exact ⟨hbound, Kneser.ActualLensGeometry.bandChart_bandTime a b _ u
    (ne_of_lt (ha.trans hb)) (ne_of_gt hθ) (hno a) (hno b)⟩

theorem actual_attracting_theta_pos (s a : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (ha : a < 0) (hfa : unfolding (s : ℂ) (a : ℂ) = (a : ℂ)) :
    0 < -Real.log (multiplier s a) := by
  have ha1 := actual_negative_root_gt_neg_one s a hfa
  have hμ : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by dsimp only [multiplier]; nlinarith
  exact neg_pos.mpr (Real.log_neg hμ hμ1)

/-- The actual attracting logarithmic multiplier tends uniformly to zero
over every genuine ordered root pair. No analytic root branch is selected. -/
theorem actual_theta_uniform_small (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      0 < -Real.log (multiplier s a) ∧ -Real.log (multiplier s a) < ε := by
  obtain ⟨s₀, hs₀, hmatch⟩ := exists_uniform_actual_root_matching U H e₁ e₂ A B K F Γ hdata
  have hH := hdata.2.2.2.1
  have hHlog := hdata.2.2.2.2.2.1
  have hc : ContinuousAt (fun x : ℂ => x * H x) 0 := continuousAt_id.mul hH.continuousAt
  have he : ∀ᶠ x : ℂ in 𝓝 0, ‖x * H x‖ < ε :=
    hc.norm.eventually (gt_mem_nhds (by simpa only [zero_mul, norm_zero] using hε))
  have hsqrt : Tendsto (fun s : ℝ => (Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have hh : ContinuousAt (fun s : ℝ => (Real.sqrt s : ℂ)) (0 : ℝ) :=
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
    simpa only [Real.sqrt_zero, Complex.ofReal_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hsqrtn : Tendsto (fun s : ℝ => -(Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [neg_zero] using hsqrt.neg
  have hp : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hl : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min s₀ 1 :=
    (eventually_lt_nhds (lt_min hs₀ (by norm_num))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsqrt.eventually he, hsqrtn.eventually he, hp, hl] with s hx hn hs hss
  intro a b ha hb hfa hfb
  have hs1 : s < 1 := hss.trans_le (min_le_right _ _)
  have ha1 := actual_negative_root_gt_neg_one s a hfa
  have hμ : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hθ := actual_attracting_theta_pos s a hs hs1 ha hfa
  have hnorm : ‖(Real.log (multiplier s a) : ℂ)‖ = -Real.log (multiplier s a) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  have hsx : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
  have hma := hmatch s a b hs (hss.trans_le (min_le_left _ _)) ha hb hfa hfb _ hsx
  refine ⟨hθ, ?_⟩
  rcases hma with hm | hm
  · have hlog : (Real.log (multiplier s a) : ℂ) = (Real.sqrt s : ℂ) * H (Real.sqrt s) := by
      rw [Complex.ofReal_log hμ.le,
        ← Kneser.ActualKoenigsIdentification.rootMultiplier_of_real_value U s a _ hsx hm.1, hHlog]
    rwa [← hlog, hnorm] at hx
  · have hlog : (Real.log (multiplier s a) : ℂ) = -(Real.sqrt s : ℂ) * H (-(Real.sqrt s : ℂ)) := by
      rw [Complex.ofReal_log hμ.le,
        ← Kneser.ActualKoenigsIdentification.rootMultiplier_of_real_value U s a (-(Real.sqrt s : ℂ))
          (by simpa only [neg_sq] using hsx) hm.2, hHlog]
    rwa [← hlog, hnorm] at hn

end Kneser.ActualBandTimeConfluence

end
