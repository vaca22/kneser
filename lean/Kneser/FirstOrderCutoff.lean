import Kneser.OrbitDifferentiation
import Kneser.TruncationBounds
import Kneser.PowerSeriesTail
import Kneser.CauchyHeadTaylor

/-!
The first-order moving-cutoff theorem from analytic disc bounds and individual
term estimates. The Taylor remainder, infinite-tail estimates, admissibility
of the rounded cutoff, and `10/9` remainder are all conclusions.

The application to the prepared family still must supply its prepared
residual and real-parameter term majorant; these are explicit hypotheses.
-/

noncomputable section

namespace Kneser.FirstOrderCutoff

open Filter Set Kneser.TruncationBounds Kneser.PowerSeriesTail
open scoped Topology BigOperators

def finiteHead (term : ℂ → ℕ → ℂ) (J : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range J, term s k

theorem deriv_finiteHead (term : ℂ → ℕ → ℂ) (δ : ℕ → ℂ)
    (hδ : ∀ k, HasDerivAt (fun s => term s k) (δ k) 0) (J : ℕ) :
    deriv (finiteHead term J) 0 = ∑ k ∈ Finset.range J, δ k := by
  exact (HasDerivAt.fun_sum (fun k _ => hδ k)).deriv

theorem finiteHead_error_eq (term : ℂ → ℕ → ℂ) (δ : ℕ → ℂ)
    (hδ : ∀ k, HasDerivAt (fun s => term s k) (δ k) 0) (J : ℕ) (s : ℝ) :
    finiteHead term J (s : ℂ) - finiteHead term J 0 -
      (s : ℂ) * deriv (finiteHead term J) 0 =
      ∑ k ∈ Finset.range J, (term (s : ℂ) k - term 0 k - s • δ k) := by
  rw [deriv_finiteHead term δ hδ J]
  simp only [finiteHead, Complex.real_smul, Finset.sum_sub_distrib, Finset.mul_sum]

theorem norm_tail_cutoff {a : ℕ → ℂ} {C s : ℝ} (hC : 0 ≤ C) (hs : 0 < s)
    (ha : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ 6) :
    ‖∑' k : ℕ, a (k + cutoff s (2 / 9))‖ ≤
      (C * powerConstant 6) * s ^ (10 / 9 : ℝ) := by
  have h := norm_tsum_tail_le a C hC (by norm_num) ha (cutoff s (2 / 9)) (cutoff_pos (β := 2 / 9) hs)
  have ht := first_order_tail hs
  rw [Real.rpow_neg (by positivity)] at ht
  norm_num [Real.rpow_natCast] at ht
  have hm := mul_le_mul_of_nonneg_left ht
    (mul_nonneg hC (powerConstant_nonneg 6))
  apply h.trans
  simpa only [show (6 : ℕ) - 1 = 5 from rfl, div_eq_mul_inv] using hm

theorem norm_scaled_derivative_tail_cutoff {δ : ℕ → ℂ} {C s : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hδ : ∀ k, ‖δ k‖ ≤ C / ((k : ℝ) + 1) ^ 4) :
    ‖s • (∑' k : ℕ, δ (k + cutoff s (2 / 9)))‖ ≤
      (C * powerConstant 4) * s ^ (10 / 9 : ℝ) := by
  have h := norm_tsum_tail_le δ C hC (by norm_num) hδ (cutoff s (2 / 9)) (cutoff_pos (β := 2 / 9) hs)
  have ht := first_order_derivative_tail hs hs1
  rw [Real.rpow_neg (by positivity)] at ht
  norm_num [Real.rpow_natCast] at ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  calc
    s * ‖∑' k : ℕ, δ (k + cutoff s (2 / 9))‖ ≤
        s * (C * powerConstant 4 / (cutoff s (2 / 9) : ℝ) ^ (4 - 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left h hs.le
    _ = (C * powerConstant 4) * (s * ((cutoff s (2 / 9) : ℝ) ^ 3)⁻¹) := by ring
    _ ≤ (C * powerConstant 4) * s ^ (10 / 9 : ℝ) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hC (powerConstant_nonneg 4))

/-- The actual coordinate series has a `10/9` expansion and its explicit
coefficient is its right derivative. No head or tail remainder is an input. -/
theorem coordinate_expansion_from_disc_and_term_bounds
    (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (δ : ℕ → ℂ)
    (r Mψ c MH CT CD : ℝ) (hr : 0 < r) (hMψ : 0 ≤ Mψ)
    (hc : 0 < c) (hMH : 0 ≤ MH) (hCT : 0 ≤ CT) (hCD : 0 ≤ CD)
    (hψ : DiffContOnCl ℂ ψ (Metric.ball 0 r))
    (hψbound : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hH : ∀ J : ℕ, 0 < J →
      DiffContOnCl ℂ (finiteHead term J) (Metric.ball 0 (c / (J : ℝ) ^ 2)))
    (hHbound : ∀ J : ℕ, 0 < J → ∀ z ∈ Metric.sphere (0 : ℂ) (c / (J : ℝ) ^ 2),
      ‖finiteHead term J z‖ ≤ MH)
    (hδ : ∀ k, HasDerivAt (fun s => term s k) (δ k) 0)
    (hzero : ∀ k, ‖term 0 k‖ ≤ CT / ((k : ℝ) + 1) ^ 6)
    (hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖term (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 6)
    (hδbound : ∀ k, ‖δ k‖ ≤ CD / ((k : ℝ) + 1) ^ 4) :
    let A := coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ))
    let d := firstOrderCoefficient (deriv ψ 0) δ
    (∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖A s - A 0 - s • d‖ ≤
        (2 * Mψ / r ^ 2 + 32 * MH / c ^ 2 +
          2 * CT * powerConstant 6 + CD * powerConstant 4) * s ^ (10 / 9 : ℝ)) ∧
      HasDerivWithinAt A d (Ici 0) 0 := by
  dsimp only
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).filter_mono nhdsWithin_le_nhds
  have hadmissible := cutoff_admissible (β := 2 / 9) (by norm_num) (by norm_num) hc
  have hmodel : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖ψ (s : ℂ) - ψ 0 - s • deriv ψ 0‖ ≤ (2 * Mψ / r ^ 2) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [hpos, hle, hsmall] with s hs hs1 hsr
    have hb := CauchyHeadTaylor.norm_first_remainder_le ψ r Mψ (s : ℂ) hr hMψ hψ hψbound
      (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr.le)
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (10 / 9 : ℝ) ≤ 2 by norm_num)
    norm_num [Real.rpow_natCast] at hp
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.real_smul] at hb ⊢
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Mψ / r ^ 2)
    convert hh using 1
    ring
  have hhead : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑ k ∈ Finset.range (cutoff s (2 / 9)),
        (term (s : ℂ) k - term 0 k - s • δ k)‖ ≤
        (32 * MH / c ^ 2) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [hpos, hle, hadmissible] with s hs hs1 ha
    have hJ := cutoff_pos (β := 2 / 9) hs
    have hb := CauchyHeadTaylor.finite_head_remainder_le (finiteHead term) c MH
      (cutoff s (2 / 9)) s hc hMH hJ (hH _ hJ) (hHbound _ hJ)
      (by simpa [abs_of_pos hs] using ha)
    rw [finiteHead_error_eq term δ hδ] at hb
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_left (first_order_head hs hs1)
      (by positivity : 0 ≤ 2 * MH / c ^ 2)
    convert hh using 1 <;> ring
  have htail : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑' k : ℕ, term (s : ℂ) (k + cutoff s (2 / 9))‖ ≤
        (CT * powerConstant 6) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [hpos, hterms] with s hs ht
    exact norm_tail_cutoff hCT hs ht
  have htailzero : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑' k : ℕ, term 0 (k + cutoff s (2 / 9))‖ ≤
        (CT * powerConstant 6) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [hpos] with s hs
    exact norm_tail_cutoff hCT hs hzero
  have htailδ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖s • (∑' k : ℕ, δ (k + cutoff s (2 / 9)))‖ ≤
        (CD * powerConstant 4) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [hpos, hle] with s hs hs1
    exact norm_scaled_derivative_tail_cutoff hCD hs hs1 hδbound
  have hsummable : ∀ᶠ s : ℝ in 𝓝[>] 0, Summable (term (s : ℂ)) := by
    filter_upwards [hterms] with s hs
    exact summable_of_parabolic_bound _ CT (by norm_num) hs
  have he := coordinateSeries_power_error (fun s : ℝ => ψ (s : ℂ))
    (fun s : ℝ => term (s : ℂ)) (deriv ψ 0) δ (fun s => cutoff s (2 / 9))
    (2 * Mψ / r ^ 2) (32 * MH / c ^ 2) (CT * powerConstant 6) (CD * powerConstant 4)
    (10 / 9) (summable_of_parabolic_bound _ CT (by norm_num) hzero)
    (summable_norm_of_parabolic_bound _ CD (by norm_num) hδbound)
    hsummable hmodel hhead htail htailzero htailδ
  have he' : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
        coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) 0 -
        s • firstOrderCoefficient (deriv ψ 0) δ‖ ≤
        (2 * Mψ / r ^ 2 + 32 * MH / c ^ 2 +
          2 * CT * powerConstant 6 + CD * powerConstant 4) * s ^ (10 / 9 : ℝ) := by
    filter_upwards [he] with s hs
    convert hs using 1
    ring
  exact ⟨he', hasDerivWithinAt_of_power_error _ _ _ (10 / 9) (by norm_num) he'⟩

end Kneser.FirstOrderCutoff

end
