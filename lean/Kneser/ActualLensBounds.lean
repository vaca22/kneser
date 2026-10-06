import Kneser.ActualLensGeometry
import Kneser.ActualResidueValue

/-! Uniform local bounds for the actual prepared lens, derived from its
analytic preparation. They contain no orbit or invariant-strip hypothesis. -/

noncomputable section
namespace Kneser.ActualLensBounds

open Filter Metric Kneser.ActualLensModel Kneser.ActualLensGeometry
open Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.EvenPreparedOrbitDiscs Kneser.ActualPreparedRootMatching
open Kneser.ReflectedOrbitChainCoefficient Kneser.PositiveKoenigsOrbit
open Kneser.GrowingBandGeometry
open scoped Topology

theorem residueSum_im (s a b : ℝ) : (residueSum s a b).im = 0 := by
  simp [residueSum, ← Complex.ofReal_inv]

theorem lensModel_phase_bound (s a b θ P : ℝ) (c₁ c₂ u : ℂ)
    (hres : ‖residueSum s a b‖ ≤ 1) (hP : 0 ≤ P)
    (hc₁ : ‖c₁‖ ≤ P) (hc₂ : ‖c₂‖ ≤ P) (hu : ‖u‖ ≤ 1) :
    |(lensModel s a b θ c₁ c₂ u - bandTime a b θ u).im| ≤ Real.pi + 2 * P := by
  have hr : |(residueSum s a b * Complex.log ((b : ℂ) - u)).im| ≤ Real.pi := by
    simp only [Complex.mul_im, residueSum_im, zero_mul, add_zero, Complex.log_im, abs_mul]
    have hh := mul_le_mul ((Complex.abs_re_le_norm _).trans hres)
      (Complex.abs_arg_le_pi ((b : ℂ) - u)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have h₁ : |(c₁ * u).im| ≤ P := by
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul]
    exact (mul_le_mul hc₁ hu (norm_nonneg _) hP).trans_eq (mul_one _)
  have h₂ : |(c₂ * u ^ 2).im| ≤ P := by
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, norm_pow]
    exact (mul_le_mul hc₂ (pow_le_one₀ (norm_nonneg _) hu)
      (by positivity) hP).trans_eq (mul_one _)
  have he : lensModel s a b θ c₁ c₂ u - bandTime a b θ u =
      residueSum s a b * Complex.log ((b : ℂ) - u) + c₁ * u + c₂ * u ^ 2 := by
    unfold lensModel
    ring
  rw [he, Complex.add_im, Complex.add_im]
  calc
    _ ≤ |(residueSum s a b * Complex.log ((b : ℂ) - u)).im + (c₁ * u).im| + |(c₂ * u ^ 2).im| := abs_add_le _ _
    _ ≤ (|(residueSum s a b * Complex.log ((b : ℂ) - u)).im| + |(c₁ * u).im|) + |(c₂ * u ^ 2).im| := by gcongr; exact abs_add_le _ _
    _ ≤ Real.pi + 2 * P := by linarith

/-- The actual exponential step stays in a common local neighborhood from
its half-sized input and a sufficiently small positive parameter. -/
theorem unfolding_norm_le (s : ℝ) (u : ℂ) (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hs : 0 ≤ s) (hsη : s ≤ η / 8)
    (hu : ‖u‖ ≤ η / 4) : ‖unfolding s u‖ ≤ 3 * η / 4 := by
  have hs1 : s ≤ 1 := by linarith
  have hnorm : ‖-(s : ℂ) + (1 - (s : ℂ)) * u‖ ≤ s + ‖u‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, norm_mul,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    nlinarith [norm_nonneg u]
  have harg : ‖-(s : ℂ) + (1 - (s : ℂ)) * u‖ ≤ 1 := by linarith
  exact (Complex.norm_exp_sub_one_le harg).trans (by nlinarith)

theorem exists_actual_lens_bounds (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ M P : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      0 < M ∧ 0 < P ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        ‖e₁ s‖ ≤ P ∧ ‖e₂ s‖ ≤ P ∧ ‖residueSum s a b‖ ≤ 1 ∧
        (∀ u : ℂ, ‖u‖ < η →
          ‖descendedTerm A B Γ 2 u s 0‖ ≤
            M * (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) ^ 2) ∧
        (∀ u : ℂ, ‖u‖ < η →
          |(lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) u -
            bandTime a b (-Real.log (multiplier s a)) u).im| ≤ Real.pi + 2 * P) ∧
        (∀ u : ℂ, ‖u‖ < η → u.im ≠ 0 →
          lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) (unfolding s u) -
            lensModel s a b (-Real.log (multiplier s a)) (e₁ s) (e₂ s) u - 1 =
              descendedTerm A B Γ 2 u s 0) := by
  obtain ⟨η₁, s₁, hη₁, hη₁q, hs₁, hs₁h, hstep⟩ :=
    exists_actual_lensModel_one_step U H e₁ e₂ A B K F Γ hdata
  obtain ⟨η₂, s₂, hη₂, hs₂, _hη₂q, _hs₂h, hres⟩ :=
    Kneser.ActualResidueValue.exists_actual_residue_unit_bound U H e₁ e₂ A B K F Γ hdata
  obtain ⟨η₃, s₃, hη₃, hs₃, hmatch⟩ :=
    exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  rcases hdata with ⟨_hU, _hU0, _hUd, _hH, _hHne, _hHlog, _hA, _hB, _hA0, _hB0,
    he₁, he₂, _hF, hΓ, _hEven, _hK0, _hK, hq, _hroots, _hfactor, _hprepared, _hresidue⟩
  let M : ℝ := ‖Γ 0‖ + 1
  let P : ℝ := ‖e₁ 0‖ + ‖e₂ 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  obtain ⟨δ, hδ, hΓb⟩ := Metric.eventually_nhds_iff.mp
    (hΓ.continuousAt.norm.eventually (gt_mem_nhds (show ‖Γ 0‖ < M by dsimp [M]; linarith)))
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp
    ((he₁.continuousAt.norm.eventually (gt_mem_nhds (show ‖e₁ 0‖ < P by dsimp [P]; linarith [norm_nonneg (e₂ 0)]))).and
      (he₂.continuousAt.norm.eventually (gt_mem_nhds (show ‖e₂ 0‖ < P by dsimp [P]; linarith [norm_nonneg (e₁ 0)]))))
  let η := min η₁ (min η₂ (min η₃ (δ / 2)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₁' : η ≤ η₁ := min_le_left _ _
  have hη₂' : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hη₃' : η ≤ η₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηδ : η ≤ δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let s₀ := min s₁ (min s₂ (min s₃ (min r (η ^ 2))))
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  refine ⟨η, s₀, M, P, hη, hη₁'.trans hη₁q, hs₀,
    (min_le_left _ _).trans hs₁h, hM, hP, ?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb
  have hs₁' : s < s₁ := hss.trans_le (min_le_left _ _)
  have hs₂' : s < s₂ := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₃' : s < s₃ := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsr : s < r := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hsη : s < η ^ 2 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hep := he (y := (s : ℂ)) (by simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr)
  have hrp : ‖residueSum s a b‖ ≤ 1 := hres s a b hs hs₂' (ha.trans_le hη₂')
    (hb.trans_le hη₂') ha0 hb0 hfa hfb
  refine ⟨hep.1.le, hep.2.le, hrp, ?_, ?_, ?_⟩
  · intro u hu
    let x := Complex.sqrt (s : ℂ)
    have hx : x ^ 2 = (s : ℂ) := Kneser.AnalyticEvenDescent.square_sqrt _
    have hxsq : ‖x‖ ^ 2 = s := by
      rw [← norm_pow, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hxn : ‖x‖ < η := by nlinarith [norm_nonneg x]
    have hΓu : ‖Γ (x, u)‖ ≤ M := by
      apply (hΓb (y := (x, u)) ?_).le
      rw [dist_zero_right, Prod.norm_def]
      exact max_lt (by linarith) (by linarith)
    have hm := hmatch s a b hs hs₃' (ha.trans_le hη₃') (hb.trans_le hη₃')
      (by linarith) hfa hfb x hx
    have hqu : rootPolynomial A B (s : ℂ) u = (u - (a : ℂ)) * (u - (b : ℂ)) := by
      rw [← hx, hq]
      rcases hm with hm | hm <;> simp only [hm.1, hm.2, mul_comm]
    simp only [descendedTerm, splitTerm, orbit_zero, Kneser.AnalyticEvenDescent.square_sqrt,
      hqu, norm_mul, norm_pow]
    simpa [x, mul_comm] using mul_le_mul_of_nonneg_left hΓu
      (sq_nonneg (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖))
  · intro u hu
    exact lensModel_phase_bound s a b _ P (e₁ s) (e₂ s) u hrp hP.le hep.1.le hep.2.le
      (hu.le.trans (by linarith [hη₁'.trans hη₁q]))
  · intro u hu hi
    exact hstep s a b hs hs₁' (ha.trans_le hη₁') (hb.trans_le hη₁') ha0 hb0 hfa hfb u (hu.trans_le hη₁') hi

end Kneser.ActualLensBounds
end
