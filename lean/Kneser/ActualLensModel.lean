import Kneser.GrowingBandGeometry

/-!
The branch on the two-root lens is obtained from actual logarithms and
actual roots. Principal logarithm differences are valid when a true step
preserves the upper or lower physical half-plane.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace Kneser.ActualLensModel

open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.PositiveKoenigsAbel Kneser.GrowingBandGeometry
open Kneser.ApolloniusGeometry Kneser.ExponentialRootPolynomial
open Kneser.ExponentialModelTime Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference
open Kneser.ExponentialPreparedQuadratic
open Filter Metric Kneser.ReflectedOrbitChainCoefficient Kneser.ActualKoenigsIdentification
open Kneser.ActualPreparedRootMatching Kneser.EvenPreparedOrbitDiscs
open Kneser.ParabolicExponentialOrbit
open Kneser.PreparedLocalAbel
open scoped Topology

def residueSum (s a b : ℝ) : ℂ :=
  (Real.log (multiplier s a) : ℂ)⁻¹ + (Real.log (multiplier s b) : ℂ)⁻¹

def lensModel (s a b θ : ℝ) (e₁ e₂ : ℂ) (u : ℂ) : ℂ :=
  bandTime a b θ u + residueSum s a b * Complex.log ((b : ℂ) - u) +
    e₁ * u + e₂ * u ^ 2

theorem log_div_of_arg_difference (x w : ℂ) (hx : x ≠ 0) (hw : w ≠ 0)
    (hl : -Real.pi < Complex.arg w - Complex.arg x)
    (hu : Complex.arg w - Complex.arg x ≤ Real.pi) :
    Complex.log (w / x) = Complex.log w - Complex.log x := by
  have he : Complex.exp (Complex.log w - Complex.log x) = w / x := by
    rw [Complex.exp_sub, Complex.exp_log hw, Complex.exp_log hx]
  rw [← he, Complex.log_exp]
  · simpa only [Complex.sub_im, Complex.log_im] using hl
  · simpa only [Complex.sub_im, Complex.log_im] using hu

theorem log_div_of_im_neg (x w : ℂ) (hx : x.im < 0) (hw : w.im < 0) :
    Complex.log (w / x) = Complex.log w - Complex.log x := by
  have hxn : x ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hx; linarith
  have hwn : w ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hw; linarith
  apply log_div_of_arg_difference x w hxn hwn
  · linarith [Complex.neg_pi_lt_arg w, Complex.arg_neg_iff.mpr hx]
  · linarith [Complex.neg_pi_lt_arg x, Complex.arg_neg_iff.mpr hw]

theorem log_div_of_im_pos (x w : ℂ) (hx : 0 < x.im) (hw : 0 < w.im) :
    Complex.log (w / x) = Complex.log w - Complex.log x := by
  have hxn : x ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hx; linarith
  have hwn : w ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hw; linarith
  have hxp : Complex.arg x < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hx))
  have hwp : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hw))
  apply log_div_of_arg_difference x w hxn hwn
  · linarith [Complex.arg_nonneg_iff.mpr hw.le]
  · linarith [Complex.arg_nonneg_iff.mpr hx.le]

theorem crossRatio_im (a b : ℝ) (u : ℂ) :
    (crossRatio a b u).im = (a - b) * u.im / Complex.normSq (u - (b : ℂ)) := by
  unfold crossRatio
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

theorem crossRatio_im_neg (a b : ℝ) (u : ℂ) (hab : a < b) (hu : 0 < u.im) :
    (crossRatio a b u).im < 0 := by
  rw [crossRatio_im]
  have hne : u - (b : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    linarith
  have hn : 0 < Complex.normSq (u - (b : ℂ)) := by rw [Complex.normSq_eq_norm_sq]; positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hab) hu) hn

theorem crossRatio_im_pos (a b : ℝ) (u : ℂ) (hab : a < b) (hu : u.im < 0) :
    0 < (crossRatio a b u).im := by
  rw [crossRatio_im]
  have hne : u - (b : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    linarith
  have hn : 0 < Complex.normSq (u - (b : ℂ)) := by rw [Complex.normSq_eq_norm_sq]; positivity
  exact div_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hab) hu) hn

theorem log_neg_of_im_neg (q : ℂ) (hq : q.im < 0) :
    Complex.log (-q) = Complex.log q + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [Complex.log_re, norm_neg, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
  · simpa only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero]
      using Complex.arg_neg_eq_arg_add_pi_of_im_neg hq

theorem log_neg_of_im_pos (q : ℂ) (hq : 0 < q.im) :
    Complex.log (-q) = Complex.log q - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [Complex.log_re, norm_neg, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
      sub_zero]
  · simpa only [Complex.log_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero]
      using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hq

theorem lensModel_eq_paired_upper (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hθeq : θ = -Real.log (multiplier s a)) (hu : 0 < u.im) :
    lensModel s a b θ e₁ e₂ u = pairedModel s a b e₁ e₂ u := by
  have hqa := crossRatio_im_neg a b u hab hu
  have hqeq : crossRatio a b u = ((a : ℂ) - u) / ((b : ℂ) - u) := by
    unfold crossRatio
    rw [show u - (a : ℂ) = -((a : ℂ) - u) by ring,
      show u - (b : ℂ) = -((b : ℂ) - u) by ring]
    rw [neg_div_neg_eq]
  have hl := log_div_of_im_neg ((b : ℂ) - u) ((a : ℂ) - u)
    (by simp only [Complex.sub_im, Complex.ofReal_im]; linarith)
    (by simp only [Complex.sub_im, Complex.ofReal_im]; linarith)
  have hln : (Real.log (multiplier s a) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.log (multiplier s a) ≠ 0)
  unfold lensModel bandTime residueSum pairedModel
  rw [log_neg_of_im_neg _ hqa, hqeq, hl, hθeq]
  push_cast
  field_simp
  ring

theorem lensModel_eq_paired_lower (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hθeq : θ = -Real.log (multiplier s a)) (hu : u.im < 0) :
    lensModel s a b θ e₁ e₂ u = pairedModel s a b e₁ e₂ u +
      (height θ : ℂ) * Complex.I := by
  have hqa := crossRatio_im_pos a b u hab hu
  have hqeq : crossRatio a b u = ((a : ℂ) - u) / ((b : ℂ) - u) := by
    unfold crossRatio
    rw [show u - (a : ℂ) = -((a : ℂ) - u) by ring,
      show u - (b : ℂ) = -((b : ℂ) - u) by ring]
    rw [neg_div_neg_eq]
  have hl := log_div_of_im_pos ((b : ℂ) - u) ((a : ℂ) - u)
    (by simp only [Complex.sub_im, Complex.ofReal_im]; linarith)
    (by simp only [Complex.sub_im, Complex.ofReal_im]; linarith)
  have hln : (Real.log (multiplier s a) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.log (multiplier s a) ≠ 0)
  unfold lensModel bandTime residueSum pairedModel height
  rw [log_neg_of_im_pos _ hqa, hqeq, hl, hθeq]
  push_cast
  field_simp
  ring

theorem unfolding_im_pos (s : ℝ) (u : ℂ) (hs : 0 ≤ s) (hs1 : s < 1)
    (hu : ‖u‖ ≤ 1) (hi : 0 < u.im) : 0 < (unfolding s u).im := by
  have harg : 0 < (1 - s) * u.im := mul_pos (by linarith) hi
  have harghi : (1 - s) * u.im < Real.pi := by
    have hh := (Complex.abs_im_le_norm u).trans hu
    have huim := (abs_le.mp hh).2
    have hm := mul_le_mul_of_nonneg_left huim (show 0 ≤ 1 - s by linarith)
    linarith [Real.two_le_pi]
  have him : (-(s : ℂ) + (1 - (s : ℂ)) * u).im = (1 - s) * u.im := by simp
  simp only [unfolding, Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_im, him]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi harg harghi)

theorem unfolding_im_neg (s : ℝ) (u : ℂ) (hs : 0 ≤ s) (hs1 : s < 1)
    (hu : ‖u‖ ≤ 1) (hi : u.im < 0) : (unfolding s u).im < 0 := by
  have harg : 0 < -((1 - s) * u.im) := by nlinarith
  have harghi : -((1 - s) * u.im) < Real.pi := by
    have hh := (Complex.abs_im_le_norm u).trans hu
    have huim := (abs_le.mp hh).1
    have hm := mul_le_mul_of_nonneg_left huim (show 0 ≤ 1 - s by linarith)
    linarith [Real.two_le_pi]
  have hsine : Real.sin ((1 - s) * u.im) < 0 := by
    have hh := Real.sin_pos_of_pos_of_lt_pi harg harghi
    rw [Real.sin_neg] at hh
    linarith
  have him : (-(s : ℂ) + (1 - (s : ℂ)) * u).im = (1 - s) * u.im := by simp
  simp only [unfolding, Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_im, him]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hsine

/-- The actual paired preparation has the correct one-step defect on
either physical half-plane. A real-part restriction on the initial point
is unnecessary: sign preservation fixes the logarithmic branch. -/
theorem preparedModelTime_one_step_of_same_halfplane (U H e₁ e₂ : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u F : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hreal₁ : (U x).im = 0) (hreal₂ : (U (-x)).im = 0)
    (hf : unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hF : F =
      Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U x) +
      Complex.log (1 + (u - U x) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U (-x)) - 1)
    (hsign : (0 < u.im ∧ 0 < (unfolding (x ^ 2) u).im) ∨
      (u.im < 0 ∧ (unfolding (x ^ 2) u).im < 0)) :
    preparedModelTime U H e₁ e₂ (x ^ 2) (unfolding (x ^ 2) u) -
      preparedModelTime U H e₁ e₂ (x ^ 2) u - 1 =
      F + polynomialCorrection e₁ e₂ (x ^ 2) (unfolding (x ^ 2) u) -
        polynomialCorrection e₁ e₂ (x ^ 2) u := by
  have hpa : U x - unfolding (x ^ 2) u =
      (U x - u) * (1 + (u - U (-x)) * symmetricCofactor U x u) := by
    dsimp [rootProduct] at hf
    linear_combination -hf
  have hpb : U (-x) - unfolding (x ^ 2) u =
      (U (-x) - u) * (1 + (u - U x) * symmetricCofactor U x u) := by
    dsimp [rootProduct] at hf
    linear_combination -hf
  have hlogs (r : ℂ) (hr : r.im = 0) :
      Complex.log ((r - unfolding (x ^ 2) u) / (r - u)) =
        Complex.log (r - unfolding (x ^ 2) u) - Complex.log (r - u) := by
    rcases hsign with ⟨hi, hfi⟩ | ⟨hi, hfi⟩
    · exact log_div_of_im_neg _ _ (by simp only [Complex.sub_im, hr]; linarith)
        (by simp only [Complex.sub_im, hr]; linarith)
    · exact log_div_of_im_pos _ _ (by simp only [Complex.sub_im, hr]; linarith)
        (by simp only [Complex.sub_im, hr]; linarith)
  have hne (r : ℂ) (hr : r.im = 0) : r - u ≠ 0 := by
    intro hz
    have hh := congrArg Complex.im hz
    simp only [Complex.sub_im, hr, Complex.zero_im] at hh
    rcases hsign with ⟨hi, _⟩ | ⟨hi, _⟩ <;> linarith
  have hla := hlogs (U x) hreal₁
  have hlb := hlogs (U (-x)) hreal₂
  conv_lhs at hla => rw [hpa, mul_div_cancel_left₀ _ (hne _ hreal₁)]
  conv_lhs at hlb => rw [hpb, mul_div_cancel_left₀ _ (hne _ hreal₂)]
  rw [preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx,
    preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx]
  linear_combination -(1 / Complex.log (rootMultiplier U x)) * hla -
    (1 / Complex.log (rootMultiplier U (-x))) * hlb - hF

/-- The actual preparation, roots, and logarithmic branches give the lens
model's actual residual. No one-step or orbit estimate is supplied. -/
theorem exists_actual_lensModel_one_step (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        ∀ u : ℂ, ‖u‖ < η → u.im ≠ 0 →
          lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) (unfolding s u) -
            lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) u - 1 =
              descendedTerm A B Γ 2 u s 0 := by
  obtain ⟨ηm, sm, hηm, hsm, hηmq, hmodel⟩ :=
    exists_actual_model_neighborhood U H e₁ e₂ A B K F Γ hdata
  obtain ⟨ηr, sr, hηr, hsr, hmatch⟩ :=
    exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, _hA, _hB, _hA0, _hB0, _he₁, _he₂,
    _hF, _hΓ, _hEven, _hK0, _hK, _hq, hroots, _hfactor, hprepared, hresidue⟩
  have hcofactor := eventually_symmetricCofactor_factor hU hroots (eventually_distinct_roots U hU hUd)
  have hHnear := hH.continuousAt.eventually_ne hHne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  obtain ⟨δ, hδ, hgerm⟩ := Metric.eventually_nhds_iff.mp
    (hprepared.and (hresidue.and ((hfst.eventually hHnear).and
      ((hfst.eventually (hneg.eventually hHnear)).and (hfst.eventually hcofactor)))))
  let η := min ηm (min ηr (δ / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηm' : η ≤ ηm := min_le_left _ _
  have hηr' : η ≤ ηr := (min_le_left _ _).trans' (min_le_right _ _)
  have hηδ : η ≤ δ / 4 := (min_le_right _ _).trans' (min_le_right _ _)
  have hηq : η ≤ 1 / 4 := hηm'.trans hηmq
  let s₀ := min sm (min sr (min (η ^ 2) (1 / 2)))
  refine ⟨η, s₀, hη, hηq, by dsimp [s₀]; positivity,
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb u hu him
  have hsm' : s < sm := hss.trans_le (min_le_left _ _)
  have hsr' : s < sr := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsη : s < η ^ 2 := hss.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hshalf : s < 1 / 2 := hss.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have haa : -1 < a := by have hh := (abs_lt.mp ha).1; linarith
  have hab : a < b := by linarith
  have hμ : 0 < multiplier s a := by dsimp [multiplier]; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by dsimp [multiplier]; nlinarith
  have hθ : 0 < -Real.log (multiplier s a) := neg_pos.mpr (Real.log_neg hμ hμ1)
  have hpair := (hmodel s a b hs hsm' (ha.trans_le hηm') (hb.trans_le hηm') ha0 hb0 hfa hfb).1
  let x := Complex.sqrt (s : ℂ)
  have hx : x ^ 2 = (s : ℂ) := Kneser.AnalyticEvenDescent.square_sqrt _
  have hxne : x ≠ 0 := by
    intro he
    have hz := hx
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hz
    exact (by exact_mod_cast ne_of_gt hs : (s : ℂ) ≠ 0) hz.symm
  have hxsq : ‖x‖ ^ 2 = s := by
    rw [← norm_pow, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hxn : ‖x‖ < η := by nlinarith [norm_nonneg x]
  have hp : dist (x, u) (0 : ℂ × ℂ) < δ := by
    rw [dist_zero_right, Prod.norm_def]
    exact max_lt (by linarith) (by linarith)
  have hg := hgerm hp
  have hm := hmatch s a b hs hsr' (ha.trans_le hηr') (hb.trans_le hηr') hab hfa hfb x hx
  have hreal₁ : (U x).im = 0 := by rcases hm with hm | hm <;> simp only [hm.1, Complex.ofReal_im]
  have hreal₂ : (U (-x)).im = 0 := by rcases hm with hm | hm <;> simp only [hm.2, Complex.ofReal_im]
  have hu1 : ‖u‖ ≤ 1 := hu.le.trans (by linarith)
  have hsign : (0 < u.im ∧ 0 < (unfolding (x ^ 2) u).im) ∨
      (u.im < 0 ∧ (unfolding (x ^ 2) u).im < 0) := by
    rcases lt_or_gt_of_ne him with hi | hi
    · exact Or.inr ⟨hi, by rw [hx]; exact unfolding_im_neg s u hs.le (by linarith) hu1 hi⟩
    · exact Or.inl ⟨hi, by rw [hx]; exact unfolding_im_pos s u hs.le (by linarith) hu1 hi⟩
  have hstep := preparedModelTime_one_step_of_same_halfplane U H e₁ e₂ hHlog x u (F (x, u))
    hxne hg.2.2.1 hg.2.2.2.1 hreal₁ hreal₂ (hg.2.2.2.2 u) (hg.2.1 hxne) hsign
  have hprep := hg.1
  dsimp only at hprep
  rw [hx] at hprep
  rw [hx, hprep] at hstep
  have hpaired : pairedModel s a b (e₁ s) (e₂ s) (unfolding s u) -
      pairedModel s a b (e₁ s) (e₂ s) u - 1 = descendedTerm A B Γ 2 u s 0 := by
    simpa only [hpair, descendedTerm, splitTerm, orbit_zero, x,
      Kneser.AnalyticEvenDescent.square_sqrt] using hstep
  rcases hsign with ⟨hi, hfi⟩ | ⟨hi, hfi⟩
  · rw [hx] at hfi
    rw [lensModel_eq_paired_upper s a b _ _ _ _ hab hθ rfl hfi,
      lensModel_eq_paired_upper s a b _ _ _ _ hab hθ rfl hi]
    exact hpaired
  · rw [hx] at hfi
    rw [lensModel_eq_paired_lower s a b _ _ _ _ hab hθ rfl hfi,
      lensModel_eq_paired_lower s a b _ _ _ _ hab hθ rfl hi]
    linear_combination hpaired

end Kneser.ActualLensModel

end
