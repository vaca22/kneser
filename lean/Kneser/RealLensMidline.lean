import Kneser.ActualLensGeometry

/-! The real midline of the actual lens is preserved by the true exponential
map and has exactly half of the genuine multiplier height. -/

noncomputable section
namespace Kneser.RealLensMidline

open Kneser.ExponentialUnfolding Kneser.ActualLensGeometry Kneser.GrowingBandGeometry
open Kneser.ApolloniusGeometry

def realStep (s r : ℝ) : ℝ := Real.exp (-s + (1 - s) * r) - 1

theorem unfolding_ofReal (s r : ℝ) : unfolding s r = (realStep s r : ℂ) := by
  simp [realStep, unfolding, Complex.ofReal_exp]

theorem unfolding_real_between (s a b r : ℝ) (hs : s < 1)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (har : a < r) (hrb : r < b) : a < realStep s r ∧ realStep s r < b := by
  have hRa : realStep s a = a := by exact_mod_cast ((unfolding_ofReal s a).symm.trans hfa)
  have hRb : realStep s b = b := by exact_mod_cast ((unfolding_ofReal s b).symm.trans hfb)
  have h₁ : realStep s a < realStep s r := by
    unfold realStep
    exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by nlinarith)) _
  have h₂ : realStep s r < realStep s b := by
    unfold realStep
    exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by nlinarith)) _
  exact ⟨by rwa [hRa] at h₁, by rwa [hRb] at h₂⟩

theorem real_between_orbit (s a b r : ℝ) (hs : s < 1)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (har : a < r) (hrb : r < b) :
    ∀ k : ℕ, (orbit r s k).im = 0 ∧ a < (orbit r s k).re ∧ (orbit r s k).re < b := by
  intro k
  induction k with
  | zero => simpa using And.intro (show (r : ℂ).im = 0 by simp) (And.intro har hrb)
  | succ k ih =>
    have he : orbit r s k = ((orbit r s k).re : ℂ) := by
      apply Complex.ext <;> simp [ih.1]
    rw [orbit_succ, he, unfolding_ofReal]
    have hi := unfolding_real_between s a b (orbit r s k).re hs hfa hfb ih.2.1 ih.2.2
    simpa using And.intro (show ((realStep s (orbit r s k).re : ℝ) : ℂ).im = 0 by simp) hi

theorem bandTime_real_between (a b θ r : ℝ) (har : a < r) (hrb : r < b) :
    (bandTime a b θ (r : ℂ)).im = Real.pi / θ := by
  have hq : (r - a) / (r - b) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have he : crossRatio a b (r : ℂ) = (((r - a) / (r - b) : ℝ) : ℂ) := by
    simp [crossRatio]
  have harg : Complex.arg (-crossRatio a b (r : ℂ)) = 0 := by
    rw [he, ← Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_nonneg (by linarith)
  simp [bandTime, Complex.div_ofReal_im, Complex.log_im, harg]

theorem real_bandTime_between (a b θ r : ℝ) (hab : a < b) (_hθ : 0 < θ)
    (hra : r ≠ a) (hrb : r ≠ b) (hi : 0 < (bandTime a b θ (r : ℂ)).im) :
    a < r ∧ r < b := by
  have he : crossRatio a b (r : ℂ) = (((r - a) / (r - b) : ℝ) : ℂ) := by simp [crossRatio]
  have hqne : (r - a) / (r - b) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hra) (sub_ne_zero.mpr hrb)
  have hqn : (r - a) / (r - b) < 0 := by
    by_contra hh
    have hp : 0 < (r - a) / (r - b) := lt_of_le_of_ne (by linarith) (Ne.symm hqne)
    have harg : Complex.arg (-crossRatio a b (r : ℂ)) = Real.pi := by
      rw [he, ← Complex.ofReal_neg]
      exact Complex.arg_ofReal_of_neg (by linarith)
    have hz : (bandTime a b θ (r : ℂ)).im = 0 := by
      simp [bandTime, Complex.div_ofReal_im, Complex.log_im, harg]
    linarith
  by_cases h : r < b
  · have hden : r - b < 0 := by linarith
    have hnum : 0 < r - a := (div_neg_iff.mp hqn).resolve_right (by intro hh; linarith [hh.2]) |>.1
    exact ⟨by linarith, h⟩
  · have hden : 0 < r - b := lt_of_le_of_ne (by linarith) (Ne.symm (sub_ne_zero.mpr hrb))
    have hnum : r - a < 0 := (div_neg_iff.mp hqn).resolve_left (by intro hh; linarith [hh.2]) |>.1
    linarith

/-- The entire real midline has the same actual infinite-strip conclusion
as the nonreal phase bootstrap, without a log-branch assumption. -/
theorem real_midline_invariant (s a b θ Y : ℝ) (u : ℂ)
    (hs : s < 1) (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ)) (hui : u.im = 0)
    (hband : bandTime a b θ u ∈ strip θ Y) :
    ∀ k : ℕ, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ) ∧
      bandTime a b θ (orbit u s k) ∈ strip θ (Y / 2) := by
  have hu : u = (u.re : ℂ) := by apply Complex.ext <;> simp [hui]
  have hbetween := real_bandTime_between a b θ u.re hab hθ
    (by intro he; apply hua; rw [hu, he]) (by intro he; apply hub; rw [hu, he])
    (by rw [← hu]; exact lt_trans hY hband.1)
  have ht : (bandTime a b θ u).im = Real.pi / θ := by rw [hu]; exact bandTime_real_between _ _ _ _ hbetween.1 hbetween.2
  have hlevels := hband
  change Y < (bandTime a b θ u).im ∧ (bandTime a b θ u).im < height θ - Y at hlevels
  rw [ht] at hlevels
  intro k
  rw [hu]
  have hk := real_between_orbit s a b u.re hs hfa hfb hbetween.1 hbetween.2 k
  have hreal : orbit u.re s k = ((orbit u.re s k).re : ℂ) := by apply Complex.ext <;> simp [hk.1]
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [hk.2.1]
  · intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [hk.2.2]
  · rw [hreal]
    have he := bandTime_real_between a b θ (orbit u.re s k).re hk.2.1 hk.2.2
    constructor <;> rw [he] <;> linarith [hlevels.1, hlevels.2]

end Kneser.RealLensMidline
end
