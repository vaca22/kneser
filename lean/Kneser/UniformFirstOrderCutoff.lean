import Kneser.N2FirstOrderCutoff

/-!
# Uniform first-order orbit-series estimates

The parameter conditions are fixed before the initial-point index. Exact
head/tail identities therefore yield one common error estimate, rather than
only separate eventual estimates for each initial point.
-/

noncomputable section

namespace Kneser.UniformFirstOrderCutoff

open Kneser.N2FirstOrderCutoff Kneser.TruncationBounds
open Kneser.PowerSeriesTail Kneser.PreparedResidualEstimates
open Kneser.PreparedFiniteHead Filter Set Metric
open scoped Topology BigOperators

def errorConstant (r Mψ c M CT : ℝ) : ℝ :=
  2 * Mψ / r ^ 2 + 4 * M / c ^ 2 +
    2 * (M + CT) * powerConstant 4 + (M / c) * powerConstant 2

theorem errorConstant_nonneg (r Mψ c M CT : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hMψ : 0 ≤ Mψ) (hM : 0 ≤ M) (hCT : 0 ≤ CT) :
    0 ≤ errorConstant r Mψ c M CT := by
  have hp4 := powerConstant_nonneg 4
  have hp2 := powerConstant_nonneg 2
  dsimp [errorConstant]
  positivity

/-- The actual infinite sum satisfies the cutoff error at each parameter
meeting explicitly listed common scalar conditions. -/
theorem coordinate_error_bound_at
    (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (r Mψ c M CT : ℝ)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ 4)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hsr : s < r / 2)
    (hadmissible : s ≤ c / (2 * (cutoff s (2 / 5) : ℝ) ^ 2))
    (hterms : ∀ k, ‖term (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4) :
    ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
        coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) 0 -
        s • firstOrderCoefficient (deriv ψ 0) (fun k => deriv (fun z => term z k) 0)‖ ≤
      errorConstant r Mψ c M CT * s ^ (6 / 5 : ℝ) := by
  let δ : ℕ → ℂ := fun k => deriv (fun z => term z k) 0
  let J : ℕ := cutoff s (2 / 5)
  have hδbound : ∀ k, ‖δ k‖ ≤ (M / c) / ((k : ℝ) + 1) ^ 2 :=
    norm_deriv_term_le term c M hc hdisc hbound
  have hzero : ∀ k, ‖term 0 k‖ ≤ (M + CT) / ((k : ℝ) + 1) ^ 4 := by
    intro k
    exact (hbound k 0 (by simp; positivity)).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hCT) (by positivity))
  have hterms' : ∀ k, ‖term (s : ℂ) k‖ ≤ (M + CT) / ((k : ℝ) + 1) ^ 4 := by
    intro k
    exact (hterms k).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left hM) (by positivity))
  have hmodel : ‖ψ (s : ℂ) - ψ 0 - s • deriv ψ 0‖ ≤
      (2 * Mψ / r ^ 2) * s ^ (6 / 5 : ℝ) := by
    have hb := CauchyHeadTaylor.norm_first_remainder_le ψ r Mψ (s : ℂ) hr hMψ hψ hψbound
      (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr.le)
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (6 / 5 : ℝ) ≤ 2 by norm_num)
    norm_num [Real.rpow_natCast] at hp
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.real_smul] at hb ⊢
    apply hb.trans
    convert mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Mψ / r ^ 2) using 1
    ring
  have hhead : ‖∑ k ∈ Finset.range J, (term (s : ℂ) k - term 0 k - s • δ k)‖ ≤
      (4 * M / c ^ 2) * s ^ (6 / 5 : ℝ) := by
    have hb := finite_head_remainder_le term c M hc hM J s hdisc hbound
      (by simpa only [abs_of_pos hs] using hadmissible)
    apply hb.trans
    convert mul_le_mul_of_nonneg_left (head_cutoff_bound hs hs1)
      (by positivity : 0 ≤ 2 * M / c ^ 2) using 1 <;> ring
  have htail : ‖∑' k : ℕ, term (s : ℂ) (k + J)‖ ≤
      ((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ) :=
    norm_tail_cutoff _ _ _ (add_nonneg hM hCT) hs hterms'
  have htailzero : ‖∑' k : ℕ, term 0 (k + J)‖ ≤
      ((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ) :=
    norm_tail_cutoff _ _ _ (add_nonneg hM hCT) hs hzero
  have htailδ : ‖s • (∑' k : ℕ, δ (k + J))‖ ≤
      ((M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ) :=
    norm_scaled_derivative_tail_cutoff _ _ _ (by positivity) hs hs1 hδbound
  have hsum := summable_of_parabolic_bound _ (M + CT) (by norm_num) hterms'
  have hsum0 := summable_of_parabolic_bound _ (M + CT) (by norm_num) hzero
  have hsumδ := summable_of_parabolic_bound _ (M / c) (by norm_num) hδbound
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum] at hhead
  have hS := hsum.sum_add_tsum_nat_add J
  have hS0 := hsum0.sum_add_tsum_nat_add J
  have hD := hsumδ.sum_add_tsum_nat_add J
  have hb := head_tail_error_bound s (ψ s) (ψ 0) (deriv ψ 0)
    (∑ k ∈ Finset.range J, term s k) (∑ k ∈ Finset.range J, term 0 k)
    (∑ k ∈ Finset.range J, δ k) (∑' k : ℕ, term s (k + J))
    (∑' k : ℕ, term 0 (k + J)) (∑' k : ℕ, δ (k + J))
    ((2 * Mψ / r ^ 2) * s ^ (6 / 5 : ℝ)) ((4 * M / c ^ 2) * s ^ (6 / 5 : ℝ))
    (((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ))
    (((M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ))
    hmodel hhead htail htailzero htailδ
  have heq : (2 * Mψ / r ^ 2) * s ^ (6 / 5 : ℝ) + (4 * M / c ^ 2) * s ^ (6 / 5 : ℝ) +
      2 * (((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ)) +
      (((M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ)) =
      errorConstant r Mψ c M CT * s ^ (6 / 5 : ℝ) := by dsimp [errorConstant]; ring
  rw [heq] at hb
  simpa only [coordinateSeries, firstOrderCoefficient, Complex.ofReal_zero, δ,
    add_assoc, hS, hS0, hD] using hb

/-- Shared disc and real-tail estimates give one common eventual expansion
over an arbitrary index set, and actual right derivatives at every index. -/
theorem coordinate_expansion_from_uniform_term_discs {α : Type*} (S : Set α)
    (ψ : α → ℂ → ℂ) (term : α → ℂ → ℕ → ℂ) (r Mψ c M CT : ℝ)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : ∀ u ∈ S, DiffContOnCl ℂ (ψ u) (ball 0 r))
    (hψbound : ∀ u ∈ S, ∀ z ∈ sphere (0 : ℂ) r, ‖ψ u z‖ ≤ Mψ)
    (hdisc : ∀ u ∈ S, ∀ k, DiffContOnCl ℂ (fun z => term u z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ u ∈ S, ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term u z k‖ ≤ M / ((k : ℝ) + 1) ^ 4)
    (hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ k,
      ‖term u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4) :
    (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖coordinateSeries (fun s : ℝ => ψ u (s : ℂ)) (fun s : ℝ => term u (s : ℂ)) s -
        coordinateSeries (fun s : ℝ => ψ u (s : ℂ)) (fun s : ℝ => term u (s : ℂ)) 0 -
        s • firstOrderCoefficient (deriv (ψ u) 0) (fun k => deriv (fun z => term u z k) 0)‖ ≤
          errorConstant r Mψ c M CT * s ^ (6 / 5 : ℝ)) ∧
    ∀ u ∈ S, HasDerivWithinAt
      (coordinateSeries (fun s : ℝ => ψ u (s : ℂ)) (fun s : ℝ => term u (s : ℂ)))
      (firstOrderCoefficient (deriv (ψ u) 0) (fun k => deriv (fun z => term u z k) 0)) (Ici 0) 0 := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).filter_mono nhdsWithin_le_nhds
  have hadmissible := cutoff_admissible (β := 2 / 5) (by norm_num) (by norm_num) hc
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖coordinateSeries (fun s : ℝ => ψ u (s : ℂ)) (fun s : ℝ => term u (s : ℂ)) s -
        coordinateSeries (fun s : ℝ => ψ u (s : ℂ)) (fun s : ℝ => term u (s : ℂ)) 0 -
        s • firstOrderCoefficient (deriv (ψ u) 0) (fun k => deriv (fun z => term u z k) 0)‖ ≤
          errorConstant r Mψ c M CT * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos, hle, hsmall, hadmissible, hterms] with s hs hs1 hsr ha ht
    intro u hu
    exact coordinate_error_bound_at (ψ u) (term u) r Mψ c M CT hr hMψ hc hM hCT
      (hψ u hu) (hψbound u hu) (hdisc u hu) (hbound u hu) s hs hs1 hsr ha (ht u hu)
  refine ⟨he, ?_⟩
  intro u hu
  exact hasDerivWithinAt_of_power_error _ _ _ (6 / 5) (by norm_num)
    (he.mono fun _ hs => hs u hu)

end Kneser.UniformFirstOrderCutoff

end
