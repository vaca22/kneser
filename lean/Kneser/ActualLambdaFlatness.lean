import Kneser.RealExponentialRoots
import Kneser.RealNormalizationAnchor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field

/-!
The actual exponentially small factor is flat to every algebraic order.
It is defined by the genuine negative fixed point's multiplier, and its
quantitative exponential majorant is derived from the exponential map.
This does not assume or assert the Kneser sewing coefficient comparison.
-/

noncomputable section
namespace Kneser.ActualLambdaFlatness

open Filter Set Kneser.ExponentialUnfolding
open scoped Topology

def attractingMultiplier (s a : ℝ) : ℝ := (1 - s) * (1 + a)

def lambdaFactor (s a : ℝ) : ℝ :=
  Real.exp (4 * Real.pi ^ 2 / Real.log (attractingMultiplier s a))

theorem negative_root_sqrt_bound (s a : ℝ) (hs : 0 < s) (hsmall : s ≤ 1 / 4)
    (ha : -1 / 2 ≤ a) (haneg : a < 0)
    (hroot : unfolding (s : ℂ) (a : ℂ) = (a : ℂ)) : -a ≤ 2 * Real.sqrt s := by
  let t : ℝ := -s + (1 - s) * a
  have hreal : Real.exp t - 1 = a := by
    have h := congrArg Complex.re hroot
    have he : -(s : ℂ) + (1 - (s : ℂ)) * (a : ℂ) = (t : ℂ) := by
      dsimp [t]
      push_cast
      ring
    simpa only [unfolding, he, Complex.sub_re, Complex.one_re,
      Complex.exp_ofReal_re, Complex.ofReal_re] using h
  have htlow : -1 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) (show 0 ≤ a + 1 / 2 by linarith)]
  have htneg : t < 0 := by
    dsimp [t]
    have hm := mul_neg_of_pos_of_neg (show 0 < 1 - s by linarith) haneg
    linarith
  have htle : t ≤ a := by
    dsimp [t]
    nlinarith [mul_nonneg hs.le (show 0 ≤ 1 + a by linarith)]
  have hi := RealNormalizationAnchor.realMap_increment t htlow htneg
  change t ^ 2 / 4 ≤ Real.exp t - 1 - t at hi
  rw [hreal] at hi
  have hasq : a ^ 2 ≤ 4 * s := by
    have hmul : 0 ≤ (a - t) * (-a - t) := mul_nonneg (by linarith) (by linarith)
    have hsa : s * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le haneg.le
    have hdiff : a - t ≤ s := by dsimp [t]; nlinarith
    nlinarith
  have hsq := Real.sq_sqrt hs.le
  nlinarith [Real.sqrt_nonneg s]

theorem actual_multiplier_derivative (s a : ℝ)
    (hroot : unfolding (s : ℂ) (a : ℂ) = (a : ℂ)) :
    deriv (unfolding (s : ℂ)) (a : ℂ) = (attractingMultiplier s a : ℂ) := by
  have h : Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * (a : ℂ)) = 1 + (a : ℂ) := by
    change Complex.exp _ - 1 = (a : ℂ) at hroot
    linear_combination hroot
  rw [(hasDerivAt_unfolding_spatial (s : ℂ) (a : ℂ)).deriv, h]
  simp only [attractingMultiplier, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_one]
  ring

theorem lambda_exponential_majorant (s a : ℝ) (hs : 0 < s) (hsmall : s ≤ 1 / 4)
    (ha : -1 / 2 ≤ a) (haneg : a < 0)
    (hroot : unfolding (s : ℂ) (a : ℂ) = (a : ℂ)) :
    0 < attractingMultiplier s a ∧ attractingMultiplier s a < 1 ∧
      0 < lambdaFactor s a ∧
      lambdaFactor s a ≤ Real.exp (-(Real.pi ^ 2 / 3) / Real.sqrt s) := by
  let l : ℝ := attractingMultiplier s a
  have hlpos : 0 < l := by
    exact mul_pos (by linarith) (by linarith)
  have hllow : 1 / 4 ≤ l := by
    dsimp [l, attractingMultiplier]
    have h := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - s by linarith)
      (show (1 / 2 : ℝ) ≤ 1 + a by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show 0 ≤ 1 - s by linarith)
    norm_num at h
    linarith
  have hllt : l < 1 := by
    dsimp [l, attractingMultiplier]
    nlinarith [mul_neg_of_pos_of_neg (show 0 < 1 - s by linarith) haneg]
  have hlneg : Real.log l < 0 := Real.log_neg hlpos hllt
  have har := negative_root_sqrt_bound s a hs hsmall ha haneg hroot
  have hsqrt := Real.sqrt_pos.mpr hs
  have hsle : s ≤ Real.sqrt s := by nlinarith [Real.sq_sqrt hs.le]
  have hdiff : 1 - l ≤ 3 * Real.sqrt s := by
    dsimp [l, attractingMultiplier]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.le haneg.le]
  have hlog : -Real.log l ≤ 4 * (1 - l) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hlpos)
    rw [Real.log_inv] at h
    have he : l⁻¹ - 1 = (1 - l) / l := by field_simp
    rw [he] at h
    have hd : (1 - l) / l ≤ 4 * (1 - l) := by
      apply (div_le_iff₀ hlpos).mpr
      nlinarith [mul_nonneg (show 0 ≤ 1 - l by linarith) (show 0 ≤ 4 * l - 1 by linarith)]
    exact h.trans hd
  have hlogbound : -Real.log l ≤ 12 * Real.sqrt s := by linarith
  refine ⟨hlpos, hllt, Real.exp_pos _, ?_⟩
  apply Real.exp_le_exp.mpr
  change 4 * Real.pi ^ 2 / Real.log l ≤ -(Real.pi ^ 2 / 3) / Real.sqrt s
  have hden : 0 < -Real.log l := neg_pos.mpr hlneg
  have hdiv : (Real.pi ^ 2 / 3) / Real.sqrt s ≤ 4 * Real.pi ^ 2 / (-Real.log l) := by
    apply (div_le_div_iff₀ hsqrt hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogbound (sq_nonneg Real.pi)]
  have he : 4 * Real.pi ^ 2 / Real.log l = -(4 * Real.pi ^ 2 / (-Real.log l)) := by ring
  rw [he]
  simpa only [neg_div] using neg_le_neg hdiv


/-- The proved exponential majorant is smaller than every power of the
actual unfolding parameter on one common positive interval. -/
theorem exponential_majorant_flat (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      Real.exp (-(Real.pi ^ 2 / 3) / Real.sqrt s) ≤ s ^ m := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.mpr hs
  have ht : Tendsto (fun s : ℝ => (Real.sqrt s)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsqrt
  have hb : 0 < Real.pi ^ 2 / 3 := by positivity
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2 * m : ℕ) : ℝ) (Real.pi ^ 2 / 3) hb).comp ht
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (Real.sqrt s)⁻¹ ^ (2 * m) * Real.exp (-(Real.pi ^ 2 / 3) * (Real.sqrt s)⁻¹) < 1 := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hsp
  have hpos : 0 < s := hsp
  have hsne : s ≠ 0 := hpos.ne'
  have hcancel : (Real.sqrt s)⁻¹ ^ (2 * m) * s ^ m = 1 := by
    rw [pow_mul, ← mul_pow]
    simp only [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hsne, one_pow]
  have hm := mul_le_mul_of_nonneg_right hs.le (pow_nonneg hpos.le m)
  have he : (Real.sqrt s)⁻¹ ^ (2 * m) *
      Real.exp (-(Real.pi ^ 2 / 3) * (Real.sqrt s)⁻¹) * s ^ m =
      Real.exp (-(Real.pi ^ 2 / 3) * (Real.sqrt s)⁻¹) := by
    calc
      _ = ((Real.sqrt s)⁻¹ ^ (2 * m) * s ^ m) *
        Real.exp (-(Real.pi ^ 2 / 3) * (Real.sqrt s)⁻¹) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [he, one_mul] at hm
  simpa only [div_eq_mul_inv] using hm

/-- For every order, the factor associated with any genuine negative
small fixed point satisfies the flat bound; no selected root branch
or exponential-flatness assumption is an input. -/
theorem actual_lambda_flat (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a : ℝ, -1 / 2 ≤ a → a < 0 →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → lambdaFactor s a ≤ s ^ m := by
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 / 4 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [exponential_majorant_flat m, hsmall, self_mem_nhdsWithin] with s hs hss hsp a ha han hroot
  exact (lambda_exponential_majorant s a hsp hss ha han hroot).2.2.2.trans hs

/-- The actual negative fixed point and its genuine multiplier/factor
exist on the same positive interval as every requested flatness order. -/
theorem exists_actual_flat_lambda (m : ℕ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ a : ℝ, -1 / 2 < a ∧ a < 0 ∧
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) ∧
      deriv (unfolding (s : ℂ)) (a : ℂ) = (attractingMultiplier s a : ℂ) ∧
      0 < attractingMultiplier s a ∧ attractingMultiplier s a < 1 ∧
      0 < lambdaFactor s a ∧ lambdaFactor s a ≤ s ^ m := by
  obtain ⟨s₀, hs₀, _hss, hr⟩ := RealExponentialRoots.exists_ordered_small_real_roots
    (1 / 2) (by norm_num)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ ∧ s ≤ 1 / 4 :=
    ((eventually_lt_nhds hs₀).and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).mono fun _ h => h.le)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [actual_lambda_flat m, hsmall, self_mem_nhdsWithin] with s hs hss hsp
  obtain ⟨a, _b, ha, han, _hb, _hbb, hroot, _hrootb⟩ := hr s hsp hss.1
  have ha' : -1 / 2 < a := by simpa only [neg_div] using ha
  obtain ⟨hlpos, hllt, hΛpos, _hΛb⟩ := lambda_exponential_majorant s a hsp hss.2 ha'.le han hroot
  exact ⟨a, ha', han, hroot, actual_multiplier_derivative s a hroot,
    hlpos, hllt, hΛpos, hs a ha'.le han hroot⟩

end Kneser.ActualLambdaFlatness
end
