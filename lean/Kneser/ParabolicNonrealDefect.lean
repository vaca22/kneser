import Kneser.CanonicalDepthIndependence
import Mathlib.Analysis.Analytic.Uniqueness

/-! The genuine quadratic parabolic model defects extend to both nonreal
halves of a small disc. This supplies the actual branch-safe defects on an
upper overlap gate, rather than assuming positive reciprocal real part. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Kneser.ParabolicNonrealDefect

open Filter Set Metric Complex Kneser.ParabolicExponentialOrbit
open Kneser.ParabolicFatouCoordinate Kneser.RepellingExponentialOrbit
open scoped Topology BigOperators

theorem inverse_re_pos_of_re_neg (u : ℂ) (hu : u.re < 0) : 0 < (inverseCoordinate u).re := by
  have hne : u ≠ 0 := by intro he; simp [he] at hu
  have hn := Complex.normSq_pos.mpr hne
  simp only [inverseCoordinate, Complex.div_re]
  norm_num
  exact div_pos (by linarith) hn

theorem analyticAt_logarithmic_model (sign u : ℂ) (hu : u.im ≠ 0) :
    AnalyticAt ℂ (fun v : ℂ => (-2 : ℂ) / v + sign * Complex.log (-v) / 3) u := by
  have hn : u ≠ 0 := by intro he; simp [he] at hu
  have hs : -u ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hu))
  exact (analyticAt_const.div analyticAt_id hn).add
    ((analyticAt_const.mul (analyticAt_id.neg.clog hs)).div_const)

/-- Identity continuation on either half disc. Agreement on the genuine
left petal determines the analytic defect throughout that same half disc. -/
theorem exists_half_disc_extension (F D : ℂ → ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hD : AnalyticAt ℂ D 0)
    (hident : ∀ᶠ u in 𝓝 (0 : ℂ), 0 < (inverseCoordinate u).re → F u = D u)
    (hF : ∀ u : ℂ, ‖u‖ < 1 → u.im ≠ 0 → AnalyticAt ℂ F u) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℂ, ‖u‖ < r → 0 < ε * u.im → F u = D u := by
  have hn : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ < 1 := by
    have hh : ∀ᶠ u : ℂ in 𝓝 0, u ∈ ball (0 : ℂ) 1 :=
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp
    ((hD.eventually_analyticAt.and hident).and hn)
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  let V : Set ℂ := ball 0 r ∩ {u : ℂ | 0 < ε * u.im}
  have hlin : IsLinearMap ℝ (fun u : ℂ => ε * u.im) := by
    constructor
    · intro x y; simp only [Complex.add_im]; ring
    · intro a u; simp only [Complex.smul_im]; ring
  have hconn : IsPreconnected V :=
    ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_gt hlin 0)).isPreconnected
  have hFa : AnalyticOnNhd ℂ F V := by
    intro u hu
    have hnorm : ‖u‖ < r := by simpa using hu.1
    have hh := hb (by simpa using hnorm)
    have hi : u.im ≠ 0 := by
      intro he
      have hh : 0 < ε * u.im := hu.2
      simp only [he, mul_zero, lt_self_iff_false] at hh
    exact hF u hh.2 hi
  have hDa : AnalyticOnNhd ℂ D V := by
    intro u hu
    exact (hb hu.1).1.1
  let u₀ : ℂ := (-r / 4 : ℝ) + (ε * r / 4 : ℝ) * I
  have hure : u₀.re = -r / 4 := by simp [u₀]
  have huim : u₀.im = ε * r / 4 := by simp [u₀]
  have hunorm : ‖u₀‖ < r := by
    have hb' := norm_add_le ((-r / 4 : ℝ) : ℂ) (((ε * r / 4 : ℝ) : ℂ) * I)
    have h₁ : ‖((-r / 4 : ℝ) : ℂ)‖ = r / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hr]
      norm_num
    have h₂ : ‖((ε * r / 4 : ℝ) : ℂ) * I‖ = r / 4 := by
      rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_mul, hεabs, abs_of_pos hr]
      norm_num
    rw [h₁, h₂] at hb'
    dsimp only [u₀]
    linarith
  have huV : u₀ ∈ V := by
    refine ⟨by simpa using hunorm, ?_⟩
    change 0 < ε * u₀.im
    rw [huim]
    have he : ε * (ε * r / 4) = r / 4 := by rw [← mul_div_assoc, ← mul_assoc, hεsq, one_mul]
    rw [he]
    positivity
  have heq : F =ᶠ[𝓝 u₀] D := by
    have hball : ∀ᶠ u in 𝓝 u₀, u ∈ ball (0 : ℂ) r :=
      isOpen_ball.mem_nhds (by simpa using hunorm)
    have hre : ∀ᶠ u : ℂ in 𝓝 u₀, u.re < 0 :=
      Complex.continuous_re.continuousAt.eventually (gt_mem_nhds (by rw [hure]; linarith))
    filter_upwards [hball, hre] with u hu hur
    exact (hb hu).1.2 (inverse_re_pos_of_re_neg u hur)
  refine ⟨r, hr, ?_⟩
  intro u hu hi
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hDa hconn huV heq
    ⟨by simpa using hu, hi⟩

theorem exp_map_im_ne_zero (u : ℂ) (hsmall : ‖u‖ < 1) (hi : u.im ≠ 0) :
    (parabolicMap u).im ≠ 0 := by
  have ha := Complex.abs_im_le_norm u
  have hsin : Real.sin u.im ≠ 0 := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt h (by
        have hh := (abs_le.mp ha).1
        linarith [Real.pi_gt_three]))
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h (by
        have hh := (abs_le.mp ha).2
        linarith [Real.pi_gt_three]))
  simpa only [parabolicMap, Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_im] using
    mul_ne_zero (Real.exp_pos u.re).ne' hsin

theorem inverse_map_im_ne_zero (u : ℂ) (hi : u.im ≠ 0) :
    (parabolicInverse u).im ≠ 0 := by
  have harg : Complex.arg (1 - u) ≠ 0 := by
    intro he
    have hh := (Complex.arg_eq_zero_iff.mp he).2
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at hh
    exact hi (neg_eq_zero.mp hh)
  simpa only [parabolicInverse, Complex.neg_im, Complex.log_im, neg_ne_zero] using harg

theorem analyticAt_forward_nonreal_defect (u : ℂ) (hsmall : ‖u‖ < 1) (hi : u.im ≠ 0) :
    AnalyticAt ℂ (coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u := by
  have hf : AnalyticAt ℂ parabolicMap u := ParabolicFatouHolomorphic.differentiable_parabolicMap.analyticAt u
  have hm : AnalyticAt ℂ ParabolicFatouCoordinate.model u := by
    change AnalyticAt ℂ (fun v : ℂ => (-2 : ℂ) / v + Complex.log (-v) / 3) u
    simpa only [one_mul] using analyticAt_logarithmic_model 1 u hi
  have hmf : AnalyticAt ℂ ParabolicFatouCoordinate.model (parabolicMap u) := by
    change AnalyticAt ℂ (fun v : ℂ => (-2 : ℂ) / v + Complex.log (-v) / 3) (parabolicMap u)
    simpa only [one_mul] using
      analyticAt_logarithmic_model 1 (parabolicMap u) (exp_map_im_ne_zero u hsmall hi)
  exact ((hmf.comp hf).sub hm).sub analyticAt_const

theorem analyticAt_inverse_nonreal_defect (u : ℂ) (hsmall : ‖u‖ < 1) (hi : u.im ≠ 0) :
    AnalyticAt ℂ (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u := by
  have hs : 1 - u ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simpa using hi))
  have hf : AnalyticAt ℂ parabolicInverse u := ((analyticAt_const.sub analyticAt_id).clog hs).neg
  have hm : AnalyticAt ℂ RepellingFatouCoordinate.model u := by
    change AnalyticAt ℂ (fun v : ℂ => (-2 : ℂ) / v - Complex.log (-v) / 3) u
    simpa only [neg_one_mul, neg_div, sub_eq_add_neg] using
      analyticAt_logarithmic_model (-1) u hi
  have hmf : AnalyticAt ℂ RepellingFatouCoordinate.model (parabolicInverse u) := by
    change AnalyticAt ℂ (fun v : ℂ => (-2 : ℂ) / v - Complex.log (-v) / 3) (parabolicInverse u)
    simpa only [neg_one_mul, neg_div, sub_eq_add_neg] using
      analyticAt_logarithmic_model (-1) (parabolicInverse u) (inverse_map_im_ne_zero u hi)
  exact ((hmf.comp hf).sub hm).sub analyticAt_const

theorem exists_nonreal_quadratic_bound (F D Q : ℂ → ℂ)
    (hD : AnalyticAt ℂ D 0) (hQ : AnalyticAt ℂ Q 0) (hfactor : ∀ u, D u = u ^ 2 * Q u)
    (hident : ∀ᶠ u in 𝓝 (0 : ℂ), 0 < (inverseCoordinate u).re → F u = D u)
    (hF : ∀ u : ℂ, ‖u‖ < 1 → u.im ≠ 0 → AnalyticAt ℂ F u) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ < r → u.im ≠ 0 → ‖F u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨rp, hrp, hp⟩ := exists_half_disc_extension F D 1 (Or.inl rfl) hD hident hF
  obtain ⟨rm, hrm, hm⟩ := exists_half_disc_extension F D (-1) (Or.inr rfl) hD hident hF
  have hqb : ∀ᶠ u : ℂ in 𝓝 0, ‖Q u‖ < ‖Q 0‖ + 1 :=
    hQ.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨rq, hrq, hq⟩ := Metric.eventually_nhds_iff.mp hqb
  refine ⟨min rp (min rm rq), ‖Q 0‖ + 1, lt_min hrp (lt_min hrm hrq), by positivity, ?_⟩
  intro u hu hi
  have he : F u = D u := by
    rcases lt_or_gt_of_ne hi with hh | hh
    · exact hm u (hu.trans_le ((min_le_right rp (min rm rq)).trans (min_le_left rm rq))) (by simpa using hh)
    · exact hp u (hu.trans_le (min_le_left _ _)) (by simpa using hh)
  rw [he, hfactor, norm_mul, norm_pow]
  have hh := (hq (by simpa using hu.trans_le ((min_le_right rp (min rm rq)).trans (min_le_right rm rq)))).le
  nlinarith [sq_nonneg ‖u‖]

theorem exists_forward_nonreal_defect_bound :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ < r → u.im ≠ 0 →
      ‖coordinateDefect parabolicMap ParabolicFatouCoordinate.model u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨D, Q, hD, hQ, hf, hi⟩ := ParabolicFatouCoordinate.exists_analytic_defect_factor
  exact exists_nonreal_quadratic_bound _ D Q hD hQ hf hi analyticAt_forward_nonreal_defect

theorem exists_inverse_nonreal_defect_bound :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ < r → u.im ≠ 0 →
      ‖coordinateDefect parabolicInverse RepellingFatouCoordinate.model u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨D, Q, hD, hQ, hf, hi⟩ := RepellingFatouCoordinate.exists_analytic_defect_factor
  exact exists_nonreal_quadratic_bound _ D Q hD hQ hf hi analyticAt_inverse_nonreal_defect

end Kneser.ParabolicNonrealDefect
end
