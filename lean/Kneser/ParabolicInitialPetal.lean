import Kneser.RealExponentialPetal
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Positive-parameter petal membership from the actual parabolic petal

The initial-point condition is measured in the parabolic coordinate `-2/u`.
All logarithmic estimates below are proved for the constructed exponential
quotient, rather than supplied as hypotheses about the dynamics.
-/

namespace Kneser.ParabolicInitialPetal

open Filter Metric Set Kneser.RealExponentialPetal
open Kneser.ParabolicExponentialOrbit Kneser.ApolloniusGeometry
open Kneser.ExponentialUnfolding Kneser.RealExponentialRoots
open scoped Topology

noncomputable section

theorem quotient_log_quadratic_bound (Q : QuotientControl) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ < r → ‖Complex.log (Q.E z) - z / 2‖ ≤ C * ‖z‖ ^ 2 := by
  let F : ℂ → ℂ := fun z => Complex.log (Q.E z) - z / 2
  have hslit : Q.E 0 ∈ Complex.slitPlane := by simp [Q.E_zero, Complex.mem_slitPlane_iff]
  have hFa : AnalyticAt ℂ F 0 := (Q.analytic.clog hslit).sub (analyticAt_id.div_const)
  have hdE : HasDerivAt Q.E (1 / 2) 0 := by
    simpa only [Q.deriv_zero] using Q.analytic.hasStrictDerivAt.hasDerivAt
  have hdF : HasDerivAt F 0 0 := by
    have h := (hdE.clog hslit).sub ((hasDerivAt_id (0 : ℂ)).div_const 2)
    change HasDerivAt (fun z => Complex.log (Q.E z) - z / 2) ((1 / 2) / Q.E 0 - 1 / 2) 0 at h
    simpa [F, Q.E_zero] using h
  obtain ⟨G, hGa, hG⟩ := hFa.exists_eq_sum_add_pow_mul 2
  have hFzero : F 0 = 0 := by simp [F, Q.E_zero]
  have hfactor : ∀ z, F z = z ^ 2 * G z := by
    intro z
    simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
      hFzero, hdF.deriv, smul_eq_mul] using hG z
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G z‖ ≤ ‖G 0‖ + 1 := by
    exact (hGa.continuousAt.norm.eventually (Iio_mem_nhds (by linarith))).mono (fun _ h => h.le)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hbound
  refine ⟨r, ‖G 0‖ + 1, hr, by positivity, ?_⟩
  intro z hz
  have hm : z ∈ ball (0 : ℂ) r := by simpa [mem_ball, dist_zero_right] using hz
  change ‖F z‖ ≤ _
  rw [hfactor, norm_mul, norm_pow]
  calc
    ‖z‖ ^ 2 * ‖G z‖ ≤ ‖z‖ ^ 2 * (‖G 0‖ + 1) :=
      mul_le_mul_of_nonneg_left (hb z hm) (sq_nonneg _)
    _ = _ := by ring

theorem norm_log_one_sub_remainder {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 := by
  have hh := Complex.norm_log_one_add_sub_self_le
    (z := -z) (by simpa only [norm_neg] using (show ‖z‖ < 1 by linarith))
  simp only [norm_neg, sub_neg_eq_add] at hh
  have hden : 0 < 1 - ‖z‖ := by linarith
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hden]
    linarith
  calc
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by simpa [sub_eq_add_neg] using hh
    _ ≤ ‖z‖ ^ 2 * 2 / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem crossRatio_norm_log_upper (a b u : ℂ) (hu : u ≠ 0)
    (ha : ‖a / u‖ ≤ 1 / 2) (hb : ‖b / u‖ ≤ 1 / 2) :
    ‖crossRatio a b u‖ ≤
      Real.exp (((b - a) / u).re + ‖a / u‖ ^ 2 + ‖b / u‖ ^ 2) := by
  have hna : 1 - a / u ≠ 0 := by
    intro h
    have hn : ‖a / u‖ = 1 := by rw [← sub_eq_zero.mp h]; norm_num
    linarith
  have hnb : 1 - b / u ≠ 0 := by
    intro h
    have hn : ‖b / u‖ = 1 := by rw [← sub_eq_zero.mp h]; norm_num
    linarith
  have hq : crossRatio a b u = (1 - a / u) / (1 - b / u) := by
    dsimp [crossRatio]
    field_simp
  have hnorma := Complex.norm_exp (Complex.log (1 - a / u))
  have hnormb := Complex.norm_exp (Complex.log (1 - b / u))
  rw [Complex.exp_log hna] at hnorma
  rw [Complex.exp_log hnb] at hnormb
  have hrem := (norm_sub_le (Complex.log (1 - a / u) + a / u)
    (Complex.log (1 - b / u) + b / u)).trans
    (add_le_add (norm_log_one_sub_remainder ha) (norm_log_one_sub_remainder hb))
  have hre := (Complex.re_le_norm _).trans hrem
  have heq : Complex.log (1 - a / u) + a / u -
      (Complex.log (1 - b / u) + b / u) =
      Complex.log (1 - a / u) - Complex.log (1 - b / u) - (b - a) / u := by ring
  rw [heq] at hre
  simp only [Complex.sub_re] at hre
  rw [hq, norm_div, hnorma, hnormb, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

theorem real_quotient_norm (a : ℝ) (u : ℂ) :
    ‖(a : ℂ) / u‖ = |a| * ‖inverseCoordinate u‖ / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, inverseCoordinate_norm]
  ring

theorem real_gap_inverse_re (a b : ℝ) (u : ℂ) :
    (((b : ℂ) - (a : ℂ)) / u).re = -(b - a) * (inverseCoordinate u).re / 2 := by
  have h : ((b : ℂ) - (a : ℂ)) / u = -((b - a : ℝ) : ℂ) * inverseCoordinate u / 2 := by
    dsimp [inverseCoordinate]
    push_cast
    ring
  rw [h]
  simp [Complex.mul_re, Complex.div_ofNat_re]

theorem initial_crossRatio_bound_of_time_upper (C R Z s a b θ : ℝ) (u : ℂ)
    (_hC : 0 ≤ C) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hb : 0 < b)
    (hζre : R + 1 ≤ (inverseCoordinate u).re) (hζnorm : ‖inverseCoordinate u‖ ≤ Z)
    (hdZ : (b - a) * Z ≤ 1)
    (hdsmall : (b - a) * (Z ^ 2 / 2 + C * R) ≤ 1 / 4)
    (hθ : θ ≤ (b - a) / 2 + C * (b - a) ^ 2) :
    u ≠ (b : ℂ) ∧ ‖crossRatio a b u‖ ≤
      Real.exp (-(θ * R)) := by
  let d := b - a
  have hd : 0 < d := by dsimp [d]; linarith
  have hu : u ≠ 0 := by
    intro h
    simp [h, inverseCoordinate] at hζre
    linarith
  have hub : u ≠ (b : ℂ) := by
    have hn := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate u).re by linarith)
    intro h
    simp [h] at hn
    linarith
  have haabs : |a| ≤ d := by rw [abs_of_neg ha]; dsimp [d]; linarith
  have hbabs : |b| ≤ d := by rw [abs_of_pos hb]; dsimp [d]; linarith
  have hqa : ‖(a : ℂ) / u‖ ≤ d * Z / 2 := by
    rw [real_quotient_norm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul haabs hζnorm (norm_nonneg _) hd.le) (by norm_num)
  have hqb : ‖(b : ℂ) / u‖ ≤ d * Z / 2 := by
    rw [real_quotient_norm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul hbabs hζnorm (norm_nonneg _) hd.le) (by norm_num)
  have hqa' : ‖(a : ℂ) / u‖ ≤ 1 / 2 := by dsimp [d] at hqa; linarith
  have hqb' : ‖(b : ℂ) / u‖ ≤ 1 / 2 := by dsimp [d] at hqb; linarith
  have herr : ‖(a : ℂ) / u‖ ^ 2 + ‖(b : ℂ) / u‖ ^ 2 ≤ d ^ 2 * Z ^ 2 / 2 := by
    have hda : 0 ≤ d * Z / 2 := by positivity
    have hsa := sq_le_sq₀ (norm_nonneg ((a : ℂ) / u)) hda |>.mpr hqa
    have hsb := sq_le_sq₀ (norm_nonneg ((b : ℂ) / u)) hda |>.mpr hqb
    nlinarith
  refine ⟨hub, (crossRatio_norm_log_upper (a : ℂ) b u hu hqa' hqb').trans ?_⟩
  rw [real_gap_inverse_re]
  apply Real.exp_le_exp.mpr
  have hlin := mul_le_mul_of_nonneg_left hζre hd.le
  have hθR := mul_le_mul_of_nonneg_right hθ hR
  have hsmall := mul_le_mul_of_nonneg_left hdsmall hd.le
  dsimp [d] at *
  nlinarith


theorem initial_crossRatio_bound (Q : QuotientControl) (r C R Z s a b : ℝ) (u : ℂ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hb : 0 < b)
    (hζre : R + 1 ≤ (inverseCoordinate u).re) (hζnorm : ‖inverseCoordinate u‖ ≤ Z)
    (hdZ : (b - a) * Z ≤ 1)
    (hdsmall : (b - a) * (Z ^ 2 / 2 + C * R) ≤ 1 / 4)
    (hκr : (1 - s) * (b - a) < r)
    (hquad : ∀ z : ℂ, ‖z‖ < r → ‖Complex.log (Q.E z) - z / 2‖ ≤ C * ‖z‖ ^ 2) :
    u ≠ (b : ℂ) ∧ ‖crossRatio a b u‖ ≤
      Real.exp (-(timeScale Q ((1 - s) * (b - a)) * R)) := by
  let d := b - a
  have hd : 0 < d := by dsimp [d]; linarith
  have hu : u ≠ 0 := by
    intro h
    simp [h, inverseCoordinate] at hζre
    linarith
  have hub : u ≠ (b : ℂ) := by
    have hn := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate u).re by linarith)
    intro h
    simp [h] at hn
    linarith
  have haabs : |a| ≤ d := by rw [abs_of_neg ha]; dsimp [d]; linarith
  have hbabs : |b| ≤ d := by rw [abs_of_pos hb]; dsimp [d]; linarith
  have hqa : ‖(a : ℂ) / u‖ ≤ d * Z / 2 := by
    rw [real_quotient_norm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul haabs hζnorm (norm_nonneg _) hd.le) (by norm_num)
  have hqb : ‖(b : ℂ) / u‖ ≤ d * Z / 2 := by
    rw [real_quotient_norm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul hbabs hζnorm (norm_nonneg _) hd.le) (by norm_num)
  have hqa' : ‖(a : ℂ) / u‖ ≤ 1 / 2 := by dsimp [d] at hqa; linarith
  have hqb' : ‖(b : ℂ) / u‖ ≤ 1 / 2 := by dsimp [d] at hqb; linarith
  have herr : ‖(a : ℂ) / u‖ ^ 2 + ‖(b : ℂ) / u‖ ^ 2 ≤ d ^ 2 * Z ^ 2 / 2 := by
    have hda : 0 ≤ d * Z / 2 := by positivity
    have hsa := sq_le_sq₀ (norm_nonneg ((a : ℂ) / u)) hda |>.mpr hqa
    have hsb := sq_le_sq₀ (norm_nonneg ((b : ℂ) / u)) hda |>.mpr hqb
    nlinarith
  have hκ : 0 < (1 - s) * d := mul_pos (by linarith) hd
  have hκd : (1 - s) * d ≤ d := by nlinarith
  have hmem : ‖(((1 - s) * d : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    exact hκr
  have hquad' := hquad (((1 - s) * d : ℝ) : ℂ) hmem
  have hθ : timeScale Q ((1 - s) * d) ≤ d / 2 + C * d ^ 2 := by
    have hh := (Complex.re_le_norm _).trans hquad'
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] at hh
    have hsq : ((1 - s) * d) ^ 2 ≤ d ^ 2 := (sq_le_sq₀ hκ.le hd.le).mpr hκd
    have hmul := mul_le_mul_of_nonneg_left hsq hC
    dsimp [timeScale]
    linarith
  refine ⟨hub, (crossRatio_norm_log_upper (a : ℂ) b u hu hqa' hqb').trans ?_⟩
  rw [real_gap_inverse_re]
  apply Real.exp_le_exp.mpr
  have hlin := mul_le_mul_of_nonneg_left hζre hd.le
  have hθR := mul_le_mul_of_nonneg_right hθ hR
  have hsmall := mul_le_mul_of_nonneg_left hdsmall hd.le
  dsimp [d] at *
  nlinarith

/-- For every bounded set in a parabolic petal with one unit of buffer, all
sufficiently small positive parameters have actual ordered real roots and
the actual infinite orbit satisfies the two-root decay bound. The only
initial condition is the parabolic coordinate, not parameter-petal membership. -/
theorem exists_uniform_initial_parabolic_petals :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ |a| < 1 / (4 * (Z + 1)) ∧
          |b| < 1 / (4 * (Z + 1)) ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log ((1 - s) * (1 + a)) ∧
          ∀ u : ℂ, R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
            ‖crossRatio a b u‖ ≤ Real.exp (-(θ * R)) ∧
            ∀ k : ℕ, ‖orbit u s k - (a : ℂ)‖ * ‖orbit u s k - (b : ℂ)‖ ≤
              100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
  obtain ⟨Q⟩ := exists_quotientControl
  have hQr : 0 < Q.radius := Q.radius_pos
  obtain ⟨r, C, hr, hC, hquad⟩ := quotient_log_quadratic_bound Q
  refine ⟨max (80 / Q.radius) 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR Z hZ
  have hRbase : 80 / Q.radius ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := by linarith
  let B : ℝ := Z ^ 2 / 2 + C * R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ : ℝ := min (Q.radius / 16)
    (min (r / 4) (min (1 / 4) (min (1 / (4 * (Z + 1))) (1 / (16 * (B + 1))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδQ : δ ≤ Q.radius / 16 := min_le_left _ _
  have hδr : δ ≤ r / 4 := (min_le_left _ _).trans' (min_le_right _ _)
  have hδsmall : δ ≤ 1 / 4 :=
    (min_le_left _ _).trans' ((min_le_right _ _).trans (min_le_right _ _))
  have hδZ : δ ≤ 1 / (4 * (Z + 1)) :=
    (min_le_left _ _).trans' ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hδB : δ ≤ 1 / (16 * (B + 1)) :=
    (min_le_right _ _).trans' ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := exists_ordered_small_real_roots δ hδ
  refine ⟨s₀, hs₀, hs₀half, ?_⟩
  intro s hs hss
  have hshalf : s < 1 / 2 := hss.trans_le hs₀half
  obtain ⟨a, b, haδ, ha, hb, hbδ, hroota, hrootb⟩ := hroots s hs hss
  have hab : a < b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hgap : b - a < Q.radius / 8 := by linarith
  have hκQ : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  have hκr : (1 - s) * (b - a) < r := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith
  have hmulZ : δ * (4 * (Z + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * (Z + 1))).mp hδZ
  have hdZ : (b - a) * Z ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ 2 * δ by linarith) hZ
    nlinarith
  have hmulB : δ * (16 * (B + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (B + 1))).mp hδB
  have hdsmall : (b - a) * (Z ^ 2 / 2 + C * R) ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ 2 * δ by linarith) hB
    change (b - a) * B ≤ _
    nlinarith
  have haZ : |a| < 1 / (4 * (Z + 1)) := by rw [abs_of_neg ha]; linarith
  have hbZ : |b| < 1 / (4 * (Z + 1)) := by rw [abs_of_pos hb]; linarith
  refine ⟨a, b, timeScale Q ((1 - s) * (b - a)), ha, hb, haZ, hbZ,
    (timeScale_pos_and_gap_bound Q s a b hs hshalf hab hκQ).1, hroota, hrootb,
    timeScale_eq_neg_log_multiplier Q s a b (by linarith) (by linarith)
      hab hroota hrootb, ?_⟩
  intro u hζre hζnorm
  obtain ⟨hub, hq⟩ := initial_crossRatio_bound Q r C R Z s a b u
    hC.le hRpos.le hZ hs hshalf ha hb hζre hζnorm hdZ hdsmall hκr hquad
  refine ⟨hq, ?_⟩
  intro k
  exact infinite_orbit_root_product_bound Q s a b R u hs hshalf hab hb
    hroota hrootb hgap hRbase hub hq k

end

end Kneser.ParabolicInitialPetal
