import Kneser.ActualBandTimeConfluence

/-! Compact confluence of the same true band time on the negative real
axis. Uniform smallness of arbitrary ordered roots proves that the
entire compact set lies to the left of the actual attracting root. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualBandTimeRealConfluence

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialPreparedModel
open Kneser.ParabolicExponentialOrbit Kneser.PositiveKoenigsOrbit
open Kneser.GrowingBandGeometry Kneser.ApolloniusGeometry Kneser.RealOrderedRootUniqueness
open Kneser.ActualBandTimeConfluence
open scoped Topology

theorem log_neg_of_real_pos (q : ℝ) (hq : 0 < q) :
    Complex.log (-(q : ℂ)) = Complex.log (q : ℂ) + (Real.pi : ℂ) * Complex.I := by
  have h := Complex.log_ofReal_mul hq (by norm_num : (-1 : ℂ) ≠ 0)
  simpa only [mul_neg_one, Complex.log_neg_one, Complex.ofReal_log hq.le] using h

theorem bandTime_eq_preparation_left (U H : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (s a b r : ℝ) (x : ℂ) (hs1 : s < 1) (ha : -1 < a) (hab : a < b) (hr : r < a)
    (hx : x ^ 2 = (s : ℂ)) (hUa : U x = (a : ℂ)) (hUb : U (-x) = (b : ℂ)) :
    bandTime a b (-Real.log (multiplier s a)) (r : ℂ) = preparationBandTime U H x r := by
  have hμ : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hl : x * H x = (Real.log (multiplier s a) : ℂ) := by
    rw [← hHlog, Kneser.ActualKoenigsIdentification.rootMultiplier_of_real_value U s a x hx hUa,
      ← Complex.ofReal_log hμ.le]
  have hq : crossRatio a b (r : ℂ) = (((r - a) / (r - b) : ℝ) : ℂ) := by
    simp only [crossRatio, Complex.ofReal_div, Complex.ofReal_sub]
  have hqr : 0 < (r - a) / (r - b) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hln : Complex.log (-crossRatio a b (r : ℂ)) =
      Complex.log (crossRatio a b (r : ℂ)) + (Real.pi : ℂ) * Complex.I := by
    rw [hq]
    exact log_neg_of_real_pos _ hqr
  unfold bandTime preparationBandTime logarithmicRatio
  rw [hln, hUa, hUb, hl]
  simp only [add_sub_cancel_right, Complex.ofReal_neg, neg_div_neg_eq]
  rfl

theorem actual_bandTime_uniform_real_left_compact (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ)
    (S : Set ℝ) (hS : IsCompact S) (hleft : ∀ r ∈ S, r < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      ∀ r ∈ S, r < a ∧ ‖bandTime a b (-Real.log (multiplier s a)) (r : ℂ) - inverseCoordinate r‖ < ε ∧
        bandChart a b (-Real.log (multiplier s a)) (bandTime a b (-Real.log (multiplier s a)) r) = r := by
  by_cases hSne : S.Nonempty
  · obtain ⟨r₀, hr₀, hmax⟩ := hS.exists_isMaxOn hSne continuous_id.continuousOn
    let δ : ℝ := -r₀ / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith [hleft r₀ hr₀]
    have hroots := eventually_all_ordered_roots_small δ hδ
    obtain ⟨s₀, hs₀, hmatch⟩ := exists_uniform_actual_root_matching U H e₁ e₂ A B K F Γ hdata
    have hU := hdata.1
    have hU0 := hdata.2.1
    have hUd := hdata.2.2.1
    have hH := hdata.2.2.2.1
    have hHlog := hdata.2.2.2.2.2.1
    have hH0 := Kneser.PreparedModelAtZero.log_factor_zero_eq_root_deriv U H hU hU0 hH hHlog
    have hne : ∀ u ∈ Complex.ofReal '' S, u ≠ 0 := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := hu
      exact_mod_cast ne_of_lt (hleft r hr)
    have he := preparationBandTime_uniform_compact U H hU hU0 hUd hH hH0
      (Complex.ofReal '' S) (hS.image Complex.continuous_ofReal) hne ε hε
    have hsqrt : Tendsto (fun s : ℝ => (Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      have hc : ContinuousAt (fun s : ℝ => (Real.sqrt s : ℂ)) (0 : ℝ) :=
        (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
      simpa only [Real.sqrt_zero, Complex.ofReal_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hsqrtn : Tendsto (fun s : ℝ => -(Real.sqrt s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      simpa only [neg_zero] using hsqrt.neg
    have hp : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
    have hl : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min s₀ 1 :=
      (eventually_lt_nhds (lt_min hs₀ (by norm_num))).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsqrt.eventually he, hsqrtn.eventually he, hp, hl, hroots] with s hx hn hs hss hrts
    intro a b ha hb hfa hfb r hr
    have hs1 : s < 1 := hss.trans_le (min_le_right _ _)
    have ha1 := actual_negative_root_gt_neg_one s a hfa
    have hsx : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
    have hsxn : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hs)
    have hrad := (hrts a b ha hb hfa hfb).1
    rw [abs_of_neg ha] at hrad
    have hrmax : r ≤ r₀ := hmax hr
    have hra : r < a := by dsimp [δ] at hrad; linarith [hleft r₀ hr₀]
    have hma := hmatch s a b hs (hss.trans_le (min_le_left _ _)) ha hb hfa hfb _ hsx
    have hbound : ‖bandTime a b (-Real.log (multiplier s a)) (r : ℂ) - inverseCoordinate r‖ < ε := by
      rcases hma with hm | hm
      · rw [bandTime_eq_preparation_left U H hHlog s a b r _ hs1 ha1 (ha.trans hb) hra hsx hm.1 hm.2]
        exact hx r (mem_image_of_mem Complex.ofReal hr) hsxn
      · rw [bandTime_eq_preparation_left U H hHlog s a b r (-(Real.sqrt s : ℂ)) hs1 ha1
          (ha.trans hb) hra (by simpa only [neg_sq] using hsx) hm.2 (by simpa only [neg_neg] using hm.1)]
        exact hn r (mem_image_of_mem Complex.ofReal hr) (neg_ne_zero.mpr hsxn)
    have hθ := actual_attracting_theta_pos s a hs hs1 ha hfa
    have hnoa : (r : ℂ) ≠ (a : ℂ) := by exact_mod_cast ne_of_lt hra
    have hnob : (r : ℂ) ≠ (b : ℂ) := by exact_mod_cast ne_of_lt (hra.trans (ha.trans hb))
    exact ⟨hra, hbound, Kneser.ActualLensGeometry.bandChart_bandTime a b _ r
      (ne_of_lt (ha.trans hb)) (ne_of_gt hθ) hnoa hnob⟩
  · exact Eventually.of_forall (fun _ _ _ _ _ _ _ r hr => False.elim (hSne ⟨r, hr⟩))

end Kneser.ActualBandTimeRealConfluence

end
