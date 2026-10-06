import Kneser.HigherOrderCutoff

/-! Pointwise cutoff bounds with explicit common constants, hence uniform
higher-order expansions for any family with common genuine discs and tails. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.UniformHigherOrderCutoff

open Filter Set Metric Kneser.TruncationBounds Kneser.PowerSeriesTail
open Kneser.FirstOrderCutoff Kneser.CauchyHigherTaylor Kneser.AsymptoticBalance
open Kneser.HigherOrderCutoff
open scoped Topology BigOperators

def expansionConstant (m N : ℕ) (r Mψ c M CT : ℝ) : ℝ :=
  2 * Mψ / r ^ (m + 1) +
    2 * M * powerConstant (2 * N) / c ^ (m + 1) * (2 : ℝ) ^ (2 * (m + 1)) +
      CT * powerConstant (2 * N) +
        ∑ j ∈ Finset.range (m + 1), (M / c ^ j) * powerConstant (2 * N - 2 * j)

theorem expansionConstant_nonneg (m N : ℕ) (r Mψ c M CT : ℝ)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT) :
    0 ≤ expansionConstant m N r Mψ c M CT := by
  have hp := powerConstant_nonneg (2 * N)
  have hsum : 0 ≤ ∑ j ∈ Finset.range (m + 1),
      (M / c ^ j) * powerConstant (2 * N - 2 * j) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (by positivity) (powerConstant_nonneg _))
  dsimp [expansionConstant]
  positivity

theorem balanced_head_remainder_at (term : ℂ → ℕ → ℂ) (c M : ℝ) (m N : ℕ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N) (hc : 0 < c) (hM : 0 ≤ M)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N))
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : s ≤ c / (2 * (cutoff s (beta m N) : ℝ) ^ 2)) :
    ‖finiteHead term (cutoff s (beta m N)) s -
      polynomial (finiteHead term (cutoff s (beta m N))) (m + 1) s‖ ≤
    (2 * M * powerConstant (2 * N) / c ^ (m + 1) * (2 : ℝ) ^ (2 * (m + 1))) *
      s ^ ((m : ℝ) + gamma m N) := by
  have hb := (beta_pos m N).le
  let J := cutoff s (beta m N)
  have hJ : 0 < J := cutoff_pos hs
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hR : 0 < c / (J : ℝ) ^ 2 := by positivity
  have hsR : ‖(s : ℂ)‖ ≤ (c / (J : ℝ) ^ 2) / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_div, mul_comm] using ha
  have hh := norm_remainder_le (finiteHead term J) (c / (J : ℝ) ^ 2)
    (M * powerConstant (2 * N)) (m + 1) (s : ℂ) hR
    (mul_nonneg hM (powerConstant_nonneg _)) (diffContOnCl_head term c hc hdisc J)
    (fun z hz => norm_head_le term c M N hc hM (by nlinarith) hbound J z
      (by exact (show ‖z‖ = c / (J : ℝ) ^ 2 by simpa only [mem_sphere, dist_zero_right] using hz).le)) hsR
  have hpow := cutoff_head_bound (β := beta m N) (a := ((2 * (m + 1) : ℕ) : ℝ))
    (b := ((m + 1 : ℕ) : ℝ)) hs hs1 hb (by positivity)
  have hexp : ((m + 1 : ℕ) : ℝ) - beta m N * ((2 * (m + 1) : ℕ) : ℝ) =
      (m : ℝ) + gamma m N := by
    rw [← headExponent_eq_order_add_gamma]
    dsimp [headExponent]
    push_cast
    ring
  rw [hexp] at hpow
  simp only [Real.rpow_natCast] at hpow
  have hpc := powerConstant_nonneg (2 * N)
  have hnum := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 2 * M * powerConstant (2 * N) / c ^ (m + 1))
  apply hh.trans
  calc
    2 * (M * powerConstant (2 * N)) * ‖(s : ℂ)‖ ^ (m + 1) / (c / (J : ℝ) ^ 2) ^ (m + 1) =
        (2 * M * powerConstant (2 * N) / c ^ (m + 1)) *
          (s ^ (m + 1) * (J : ℝ) ^ (2 * (m + 1))) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_pow, ← pow_mul]
      field_simp
    _ ≤ _ := by convert hnum using 1 <;> first | rfl | ring

theorem norm_expansion_at_admissible_cutoff
    (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (m N : ℕ) (r Mψ c M CT : ℝ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N))
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hsr : s ≤ r / 2)
    (ha : s ≤ c / (2 * (cutoff s (beta m N) : ℝ) ^ 2))
    (hreal : ∀ k, ‖term (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * N)) :
    (∀ j ≤ m, Summable (fun k => ‖termCoefficient term j k‖)) ∧
    ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
      coordinatePolynomial ψ term m s‖ ≤
        expansionConstant m N r Mψ c M CT * s ^ ((m : ℝ) + gamma m N) := by
  have hNj : ∀ j ≤ m, j + 1 ≤ N := by intro j hj; nlinarith
  have hdBound : ∀ j ≤ m, ∀ k,
      ‖termCoefficient term j k‖ ≤ (M / c ^ j) / ((k : ℝ) + 1) ^ (2 * N - 2 * j) := by
    intro j hj
    exact norm_termCoefficient_le term c M N j (by have h := hNj j hj; omega) hc hdisc hbound
  have hsumδ : ∀ j ≤ m, Summable (fun k => ‖termCoefficient term j k‖) := by
    intro j hj
    exact summable_norm_of_parabolic_bound _ (M / c ^ j)
      (by have h := hNj j hj; omega) (hdBound j hj)
  let Cψ : ℝ := 2 * Mψ / r ^ (m + 1)
  let CH : ℝ := 2 * M * powerConstant (2 * N) / c ^ (m + 1) * (2 : ℝ) ^ (2 * (m + 1))
  let CD : ℝ := ∑ j ∈ Finset.range (m + 1), (M / c ^ j) * powerConstant (2 * N - 2 * j)
  let C : ℝ := Cψ + CH + CT * powerConstant (2 * N) + CD
  have hC : 0 ≤ C := by
    have hpc := powerConstant_nonneg (2 * N)
    have hCD : 0 ≤ CD := Finset.sum_nonneg (fun j hj =>
      mul_nonneg (by positivity) (powerConstant_nonneg _))
    dsimp [C, Cψ, CH]
    positivity
  have hα : (m : ℝ) + gamma m N ≤ ((m + 1 : ℕ) : ℝ) := by
    rw [← headExponent_eq_order_add_gamma]
    dsimp [headExponent]
    push_cast
    have hβ := beta_pos m N
    nlinarith
  have hmodel : ‖ψ s - polynomial ψ (m + 1) s‖ ≤ Cψ * s ^ ((m : ℝ) + gamma m N) := by
    have ht := norm_remainder_le ψ r Mψ (m + 1) s hr hMψ hψ hψbound
      (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr)
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 hα
    simp only [Real.rpow_natCast] at hp
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at ht
    apply ht.trans
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Cψ)
    convert hh using 1 <;> first | rfl | (dsimp [Cψ]; ring)
  have hhead := balanced_head_remainder_at term c M m N hm hN hc hM hdisc hbound s hs hs1 ha
  refine ⟨hsumδ, ?_⟩
  let J := cutoff s (beta m N)
  have hsumT : Summable (term (s : ℂ)) :=
    summable_of_parabolic_bound _ CT (by nlinarith) hreal
  have hsplitT := hsumT.sum_add_tsum_nat_add J
  have htailT : ‖∑' k : ℕ, term (s : ℂ) (k + J)‖ ≤
      CT * powerConstant (2 * N) * s ^ ((m : ℝ) + gamma m N) := by
    have ht := norm_scaled_tail_cutoff (j := 0) (β := beta m N) (α := (m : ℝ) + gamma m N)
      hCT hs hs1 (by nlinarith : 2 ≤ 2 * N) hreal (by
        rw [← tailExponent_eq_order_add_gamma]
        dsimp [tailExponent]
        rw [Nat.cast_sub (by nlinarith : 1 ≤ 2 * N)]
        push_cast
        ring_nf
        exact le_rfl)
    simpa only [pow_zero, one_mul] using ht
  have htailδ : ‖∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
      (∑' k : ℕ, termCoefficient term j (k + J))‖ ≤ CD * s ^ ((m : ℝ) + gamma m N) := by
    apply (norm_sum_le _ _).trans
    have hbounds : ∀ j ∈ Finset.range (m + 1),
        ‖(s : ℂ) ^ j * (∑' k : ℕ, termCoefficient term j (k + J))‖ ≤
          ((M / c ^ j) * powerConstant (2 * N - 2 * j)) * s ^ ((m : ℝ) + gamma m N) := by
      intro j hj
      have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact norm_scaled_tail_cutoff (β := beta m N) (by positivity) hs hs1
        (by have h := hNj j hjm; omega) (hdBound j hjm)
        (by simpa only [Nat.sub_sub] using balanced_coefficient_tail_exponent m N j hm hN hjm)
    apply (Finset.sum_le_sum hbounds).trans_eq
    rw [← Finset.sum_mul]
  have hpoly : coordinatePolynomial ψ term m s = polynomial ψ (m + 1) s +
      polynomial (finiteHead term J) (m + 1) s +
        ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * (∑' k : ℕ, termCoefficient term j (k + J)) := by
    have hsplitδ : ∀ j ∈ Finset.range (m + 1),
        (∑' k : ℕ, termCoefficient term j k) =
          (∑ k ∈ Finset.range J, termCoefficient term j k) +
            (∑' k : ℕ, termCoefficient term j (k + J)) := by
      intro j hj
      exact ((hsumδ j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).of_norm.sum_add_tsum_nat_add J).symm
    calc
      coordinatePolynomial ψ term m s =
          ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
            (coefficient ψ j + (∑ k ∈ Finset.range J, termCoefficient term j k) +
              (∑' k : ℕ, termCoefficient term j (k + J))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coordinateCoefficient, hsplitδ j hj, add_assoc]
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, polynomial]
        simp_rw [head_coefficient_eq term c hc hdisc]
  have heq : coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
      coordinatePolynomial ψ term m s =
        (ψ s - polynomial ψ (m + 1) s) +
          (finiteHead term J s - polynomial (finiteHead term J) (m + 1) s) +
          (∑' k : ℕ, term (s : ℂ) (k + J)) -
          (∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * (∑' k : ℕ, termCoefficient term j (k + J))) := by
    rw [coordinateSeries, ← hsplitT, hpoly]
    dsimp [finiteHead]
    ring
  rw [heq]
  calc
    _ ≤ ‖ψ s - polynomial ψ (m + 1) s‖ +
        ‖finiteHead term J s - polynomial (finiteHead term J) (m + 1) s‖ +
        ‖∑' k : ℕ, term (s : ℂ) (k + J)‖ +
        ‖∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * (∑' k : ℕ, termCoefficient term j (k + J))‖ := by
      apply (norm_sub_le _ _).trans
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Cψ * s ^ ((m : ℝ) + gamma m N) + CH * s ^ ((m : ℝ) + gamma m N) +
        CT * powerConstant (2 * N) * s ^ ((m : ℝ) + gamma m N) + CD * s ^ ((m : ℝ) + gamma m N) :=
      add_le_add (add_le_add (add_le_add hmodel hhead) htailT) htailδ
    _ = _ := by dsimp [C, expansionConstant, Cψ, CH, CD]; ring


/-- The same cutoff event works for every spatial initial point. -/
theorem coordinate_expansion_uniform_from_bounds
    (S : Set ℂ) (ψ : ℂ → ℂ → ℂ) (term : ℂ → ℂ → ℕ → ℂ)
    (m N : ℕ) (r Mψ c M CT : ℝ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : ∀ u ∈ S, DiffContOnCl ℂ (ψ u) (ball 0 r))
    (hψbound : ∀ u ∈ S, ∀ z ∈ sphere (0 : ℂ) r, ‖ψ u z‖ ≤ Mψ)
    (hdisc : ∀ u ∈ S, ∀ k, DiffContOnCl ℂ (fun s => term u s k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ u ∈ S, ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term u s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N))
    (hreal : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ k,
      ‖term u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * N)) :
    (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient (term u) j k‖)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖coordinateSeries (fun s : ℝ => ψ u (s : ℂ))
          (fun s : ℝ => term u (s : ℂ)) s -
        coordinatePolynomial (ψ u) (term u) m s‖ ≤ C * s ^ ((m : ℝ) + gamma m N) := by
  have hNj : ∀ j ≤ m, j + 1 ≤ N := by intro j hj; nlinarith
  have hsum : ∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient (term u) j k‖) := by
    intro u hu j hj
    apply summable_norm_of_parabolic_bound _ (M / c ^ j)
      (q := 2 * N - 2 * j) (by have h := hNj j hj; omega)
    exact norm_termCoefficient_le (term u) c M N j
      (by have h := hNj j hj; omega) hc (hdisc u hu) (hbound u hu)
  refine ⟨hsum, expansionConstant m N r Mψ c M CT,
    expansionConstant_nonneg m N r Mψ c M CT hr hMψ hc hM hCT, ?_⟩
  have hadm := cutoff_admissible (beta_pos m N).le (beta_lt_half m N hm hN) hc
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ r / 2 :=
    ((eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hadm, hpos, hle, hsmall, hreal] with s ha hs hs1 hsr hT u hu
  exact (norm_expansion_at_admissible_cutoff (ψ u) (term u) m N r Mψ c M CT
    hm hN hr hMψ hc hM hCT (hψ u hu) (hψbound u hu) (hdisc u hu) (hbound u hu)
    s hs hs1 hsr ha (hT u hu)).2

end Kneser.UniformHigherOrderCutoff

end
