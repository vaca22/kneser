import Kneser.ExponentialDividedDifference
import Kneser.RealExponentialRoots

/-!
# Infinite attracting petals for positive real parameters

The scalar divided difference is constructed from the actual exponential.
For two actual real fixed points its logarithmic derivative estimate gives a
strict contraction of the cross-ratio, and thus reciprocal orbit decay.
-/

namespace Kneser.RealExponentialPetal

open Metric Set Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialDividedDifference Kneser.ApolloniusGeometry

noncomputable section

/-- Quantitative local data whose existence is proved for the true exponential. -/
structure QuotientControl where
  E : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  analytic : AnalyticAt ℂ E 0
  E_zero : E 0 = 1
  deriv_zero : deriv E 0 = 1 / 2
  factor : ∀ z, parabolicMap z = z * E z
  ne_zero : ∀ z ∈ ball (0 : ℂ) radius, E z ≠ 0
  increment : ∀ z₁ ∈ ball (0 : ℂ) radius, ∀ z₂ ∈ ball (0 : ℂ) radius,
    ‖Complex.log (E z₂) - Complex.log (E z₁) - (z₂ - z₁) / 2‖ ≤ (1 / 16) * ‖z₂ - z₁‖

theorem exists_quotientControl : Nonempty QuotientControl := by
  obtain ⟨E, r, hr, ha, hE0, hd, hE, hne, hinc⟩ := exists_quotient_log_increment (1 / 16) (by norm_num)
  exact ⟨⟨E, r, hr, ha, hE0, hd, hE, hne, hinc⟩⟩

def timeScale (Q : QuotientControl) (κ : ℝ) : ℝ := (Complex.log (Q.E (κ : ℂ))).re

/-- The genuine logarithmic time satisfies uniform numerical gap bounds. -/
theorem timeScale_bounds (Q : QuotientControl) (κ : ℝ) (hκ : 0 < κ) (hκr : κ < Q.radius) :
    (7 / 16) * κ ≤ timeScale Q κ ∧ timeScale Q κ ≤ (9 / 16) * κ := by
  have hzero : (0 : ℂ) ∈ ball 0 Q.radius := mem_ball_self Q.radius_pos
  have hmem : (κ : ℂ) ∈ ball 0 Q.radius := by
    simpa [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] using hκr
  have h := Q.increment 0 hzero κ hmem
  have he : ‖Complex.log (Q.E κ) - (κ : ℂ) / 2‖ ≤ κ / 16 := by
    simpa [Q.E_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      div_eq_mul_inv, mul_comm] using h
  have hab := (Complex.abs_re_le_norm (Complex.log (Q.E κ) - (κ : ℂ) / 2)).trans he
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re] at hab
  obtain ⟨hl, hu⟩ := abs_le.mp hab
  dsimp [timeScale]
  constructor <;> linarith

/-- The actual positive-parameter map contracts the Apollonius cross-ratio.
Only fixed-point equations and membership in the constructed local disc enter
the statement; no dynamical step estimate is assumed. -/
theorem actual_crossRatio_contraction (Q : QuotientControl) (s a b : ℝ) (u : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < b) (hb : 0 < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hub : u ≠ (b : ℂ))
    (hκr : (1 - s) * (b - a) < Q.radius)
    (hma : (1 - (s : ℂ)) * (u - (a : ℂ)) ∈ ball 0 Q.radius)
    (hmb : (1 - (s : ℂ)) * (u - (b : ℂ)) ∈ ball 0 Q.radius) :
    unfolding s u ≠ (b : ℂ) ∧
    ‖crossRatio a b (unfolding s u)‖ ≤ ‖crossRatio a b u‖ *
      Real.exp (-(3 / 4) * timeScale Q ((1 - s) * (b - a))) := by
  let κ : ℝ := (1 - s) * (b - a)
  have hκ : 0 < κ := mul_pos (by linarith) (sub_pos.mpr ha)
  have hκeq : (1 - (s : ℂ)) * ((b : ℂ) - (a : ℂ)) = (κ : ℂ) := by simp [κ]
  have hsne : (s : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hbne : (b : ℂ) ≠ -1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hEa := Q.ne_zero _ hma
  have hEb := Q.ne_zero _ hmb
  have hmapb := unfolding_fixedPoint_factor Q.E Q.factor s b u hrootb
  have hnew : unfolding s u ≠ (b : ℂ) := by
    apply sub_ne_zero.mp
    rw [hmapb]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact sub_ne_zero.mpr (Ne.symm hsne)
        · intro h
          have hr := congrArg Complex.re h
          simp at hr
          linarith
      · exact sub_ne_zero.mpr hub
    · exact hEb
  have hstep := crossRatio_step Q.E Q.factor s a b u hroota hrootb hsne hbne hub hEb
  rw [hκeq] at hstep
  have hdiff : (1 - (s : ℂ)) * (u - (a : ℂ)) -
      (1 - (s : ℂ)) * (u - (b : ℂ)) = (κ : ℂ) := by rw [← hκeq]; ring
  have hl := Q.increment _ hmb _ hma
  rw [hdiff] at hl
  have hab : |(Complex.log (Q.E ((1 - (s : ℂ)) * (u - (a : ℂ)))) -
      Complex.log (Q.E ((1 - (s : ℂ)) * (u - (b : ℂ)))) - (κ : ℂ) / 2).re| ≤ κ / 16 := by
    have hh := (Complex.abs_re_le_norm _).trans hl
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      div_eq_mul_inv, mul_comm] using hh
  have hlogupper := (abs_le.mp hab).2
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re] at hlogupper
  have hθ := (timeScale_bounds Q κ hκ hκr).2
  have hnorma := Complex.norm_exp (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (a : ℂ)))))
  have hnormb := Complex.norm_exp (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (b : ℂ)))))
  rw [Complex.exp_log hEa] at hnorma
  rw [Complex.exp_log hEb] at hnormb
  refine ⟨hnew, ?_⟩
  rw [hstep, Complex.norm_mul, Complex.norm_mul, Complex.norm_div,
    Complex.norm_exp, hnorma, hnormb]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have heq : ‖crossRatio a b u‖ * Real.exp (-κ) *
      (Real.exp (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (a : ℂ))))).re /
       Real.exp (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (b : ℂ))))).re) =
      ‖crossRatio a b u‖ * Real.exp (-κ +
        (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (a : ℂ))))).re -
        (Complex.log (Q.E ((1 - (s : ℂ)) * (u - (b : ℂ))))).re) := by
    rw [← Real.exp_sub, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _)

theorem timeScale_pos_and_gap_bound (Q : QuotientControl) (s a b : ℝ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < b)
    (hκr : (1 - s) * (b - a) < Q.radius) :
    0 < timeScale Q ((1 - s) * (b - a)) ∧
      (b - a) / timeScale Q ((1 - s) * (b - a)) ≤ 5 := by
  have hd : 0 < b - a := sub_pos.mpr ha
  have hκ : 0 < (1 - s) * (b - a) := mul_pos (by linarith) hd
  have hl := (timeScale_bounds Q _ hκ hκr).1
  have hp : 0 < timeScale Q ((1 - s) * (b - a)) := lt_of_lt_of_le (by positivity) hl
  refine ⟨hp, (div_le_iff₀ hp).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - s by linarith) hd.le
  linarith

/-- An Apollonius condition forces both divided-difference arguments into the
constructed analytic disc. -/
theorem petal_arguments_mem (Q : QuotientControl) (s a b x : ℝ) (u : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < b)
    (hgap : b - a < Q.radius / 8) (hx : 80 / Q.radius ≤ x)
    (hub : u ≠ (b : ℂ))
    (hq : ‖crossRatio a b u‖ ≤ Real.exp (-(timeScale Q ((1 - s) * (b - a)) * x))) :
    (1 - (s : ℂ)) * (u - (a : ℂ)) ∈ ball 0 Q.radius ∧
      (1 - (s : ℂ)) * (u - (b : ℂ)) ∈ ball 0 Q.radius := by
  have hd : 0 < b - a := sub_pos.mpr ha
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs' ha hκr
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos (by norm_num) Q.radius_pos) hx
  have hnormgap : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
    rw [← Complex.ofReal_sub, Complex.norm_of_nonneg hd.le]
  have hn := attracting_root_distance_bound (a : ℂ) b u
    (timeScale Q ((1 - s) * (b - a)) * x) (mul_pos hθ hxpos) hub hq
  rw [hnormgap] at hn
  have heq : (b - a) / (timeScale Q ((1 - s) * (b - a)) * x) =
      ((b - a) / timeScale Q ((1 - s) * (b - a))) / x := by ring
  rw [heq] at hn
  have hdist : ‖u - (a : ℂ)‖ ≤ 5 / x := hn.trans (div_le_div_of_nonneg_right hratio hxpos.le)
  have hfrac : (5 : ℝ) / x ≤ Q.radius / 16 := by
    apply (div_le_iff₀ hxpos).mpr
    have hm := (div_le_iff₀ Q.radius_pos).mp hx
    linarith
  have hda : ‖u - (a : ℂ)‖ ≤ Q.radius / 16 := hdist.trans hfrac
  have hdb : ‖u - (b : ℂ)‖ ≤ Q.radius / 16 + (b - a) := by
    have heq : u - (b : ℂ) = (u - (a : ℂ)) + ((a : ℂ) - (b : ℂ)) := by ring
    rw [heq]
    have habnorm : ‖(a : ℂ) - (b : ℂ)‖ = b - a := by rw [norm_sub_rev, hnormgap]
    exact (norm_add_le _ _).trans (by rw [habnorm]; linarith)
  have hh : ‖(1 - (s : ℂ))‖ = 1 - s := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  constructor
  · simp only [mem_ball, dist_zero_right, Complex.norm_mul, hh]
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) (norm_nonneg (u - (a : ℂ)))
    linarith [Q.radius_pos]
  · simp only [mem_ball, dist_zero_right, Complex.norm_mul, hh]
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) (norm_nonneg (u - (b : ℂ)))
    linarith [Q.radius_pos]

/-- Every true orbit in the numerical Apollonius petal contracts at the uniform
model-time rate `3/4`. -/
theorem infinite_orbit_crossRatio_bound (Q : QuotientControl) (s a b R : ℝ) (u : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < b) (hb : 0 < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hR : 80 / Q.radius ≤ R)
    (hub : u ≠ (b : ℂ))
    (hq : ‖crossRatio a b u‖ ≤ Real.exp (-(timeScale Q ((1 - s) * (b - a)) * R)))
    (k : ℕ) :
    orbit u s k ≠ (b : ℂ) ∧
      ‖crossRatio a b (orbit u s k)‖ ≤
        Real.exp (-(timeScale Q ((1 - s) * (b - a)) * (R + (3 / 4) * (k : ℝ)))) := by
  have hd : 0 < b - a := sub_pos.mpr ha
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  induction k with
  | zero => simpa using And.intro hub hq
  | succ k ih =>
    obtain ⟨hne, hn⟩ := ih
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hx : 80 / Q.radius ≤ R + (3 / 4) * (k : ℝ) := by linarith
    obtain ⟨hmemA, hmemB⟩ := petal_arguments_mem Q s a b _ (orbit u s k)
      hs hs' ha hgap hx hne hn
    obtain ⟨hnew, hcon⟩ := actual_crossRatio_contraction Q s a b (orbit u s k)
      hs hs' ha hb hroota hrootb hne hκr hmemA hmemB
    rw [← orbit_succ] at hnew hcon
    refine ⟨hnew, hcon.trans ?_⟩
    calc
      _ ≤ Real.exp (-(timeScale Q ((1 - s) * (b - a)) * (R + (3 / 4) * (k : ℝ)))) *
          Real.exp (-(3 / 4) * timeScale Q ((1 - s) * (b - a))) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- Uniform quadratic decay of the actual infinite positive-parameter orbit's
two-root factor, with a parameter-independent numerical constant. -/
theorem infinite_orbit_root_product_bound (Q : QuotientControl) (s a b R : ℝ) (u : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < b) (hb : 0 < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hR : 80 / Q.radius ≤ R)
    (hub : u ≠ (b : ℂ))
    (hq : ‖crossRatio a b u‖ ≤ Real.exp (-(timeScale Q ((1 - s) * (b - a)) * R)))
    (k : ℕ) :
    ‖orbit u s k - (a : ℂ)‖ * ‖orbit u s k - (b : ℂ)‖ ≤
      100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
  have hd : 0 < b - a := sub_pos.mpr ha
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs' ha hκr
  obtain ⟨hne, hn⟩ := infinite_orbit_crossRatio_bound Q s a b R u
    hs hs' ha hb hroota hrootb hgap hR hub hq k
  have hx : 0 < R + (3 / 4) * (k : ℝ) := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hRp : 0 < R := lt_of_lt_of_le (div_pos (by norm_num) Q.radius_pos) hR
    linarith
  have hp := root_product_bound_model_time (a : ℂ) b (orbit u s k)
    (timeScale Q ((1 - s) * (b - a))) _ hθ hx hne hn
  have hnormgap : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
    rw [← Complex.ofReal_sub, Complex.norm_of_nonneg hd.le]
  rw [hnormgap] at hp
  have hratioPos : 0 ≤ (b - a) / timeScale Q ((1 - s) * (b - a)) := by positivity
  have hsq := pow_le_pow_left₀ hratioPos hratio 2
  exact hp.trans (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _))

/-- The constructed time scale is exactly minus the logarithm of the true
attracting multiplier, by the actual fixed-point equation. -/
theorem timeScale_eq_neg_log_multiplier (Q : QuotientControl) (s a b : ℝ)
    (hs : s < 1) (ha : -1 < a) (hab : a < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ)) :
    timeScale Q ((1 - s) * (b - a)) = -Real.log ((1 - s) * (1 + a)) := by
  let μ : ℝ := (1 - s) * (1 + a)
  let κ : ℝ := (1 - s) * (b - a)
  have hμ : 0 < μ := mul_pos (by linarith) (by linarith)
  have hμne : (μ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hμ
  have hdne : ((b : ℂ) - (a : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr hab)
  have hκeq : (1 - (s : ℂ)) * ((b : ℂ) - (a : ℂ)) = (κ : ℂ) := by simp [κ]
  have hf := unfolding_fixedPoint_factor Q.E Q.factor s a b hroota
  rw [hrootb, hκeq] at hf
  have hmul : (μ : ℂ) * Q.E κ = 1 := by
    apply mul_right_cancel₀ hdne
    dsimp [μ]
    push_cast
    linear_combination -hf
  have hEq : Q.E κ = (μ : ℂ)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hμne).mpr
    simpa only [mul_comm] using hmul
  change (Complex.log (Q.E κ)).re = -Real.log μ
  rw [Complex.log_re, hEq, norm_inv]
  rw [Complex.norm_of_nonneg hμ.le, Real.log_inv]

/-- The actual exponential family has uniform infinite petals for every
sufficiently small positive real parameter. Root existence, root ordering,
the true multiplier scale, and infinite-orbit decay are all conclusions. -/
theorem exists_uniform_real_petals :
    ∃ R₀ s₀ : ℝ, 0 < R₀ ∧ 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log ((1 - s) * (1 + a)) ∧
          ∀ R : ℝ, R₀ ≤ R → ∀ u : ℂ, u ≠ (b : ℂ) →
            ‖crossRatio a b u‖ ≤ Real.exp (-(θ * R)) →
            ∀ k : ℕ, ‖orbit u s k - (a : ℂ)‖ * ‖orbit u s k - (b : ℂ)‖ ≤
              100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
  obtain ⟨Q⟩ := exists_quotientControl
  let δ : ℝ := min (Q.radius / 16) (1 / 4)
  have hδ : 0 < δ := lt_min (div_pos Q.radius_pos (by norm_num)) (by norm_num)
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := RealExponentialRoots.exists_ordered_small_real_roots δ hδ
  refine ⟨80 / Q.radius, s₀, div_pos (by norm_num) Q.radius_pos, hs₀, ?_⟩
  intro s hs hss₀
  obtain ⟨a, b, halower, ha, hb, hbupper, hroota, hrootb⟩ := hroots s hs hss₀
  have hs' : s < 1 / 2 := lt_of_lt_of_le hss₀ hs₀half
  have hab : a < b := lt_trans ha hb
  have hδr : δ ≤ Q.radius / 16 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
  have hgap : b - a < Q.radius / 8 := by linarith
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) (sub_pos.mpr hab).le
    linarith [Q.radius_pos]
  refine ⟨a, b, timeScale Q ((1 - s) * (b - a)), ha, hb,
    (timeScale_pos_and_gap_bound Q s a b hs hs' hab hκr).1, hroota, hrootb,
    timeScale_eq_neg_log_multiplier Q s a b (by linarith) (by linarith) hab hroota hrootb, ?_⟩
  intro R hR u hub hq k
  exact infinite_orbit_root_product_bound Q s a b R u hs hs' hab hb
    hroota hrootb hgap hR hub hq k

end

end Kneser.RealExponentialPetal
