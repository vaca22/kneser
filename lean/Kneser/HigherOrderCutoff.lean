import Kneser.CauchyHigherTaylor
import Kneser.HigherPreparedDerivative
import Kneser.FirstOrderCutoff

/-! Higher-degree rounded orbit cutoffs.  All Taylor estimates and power
tails are derived from shrinking analytic discs and individual real terms. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.HigherOrderCutoff

open Filter Set Metric Kneser.TruncationBounds Kneser.PowerSeriesTail
open Kneser.FirstOrderCutoff Kneser.CauchyHigherTaylor Kneser.AsymptoticBalance
open scoped Topology BigOperators

def termCoefficient (term : ℂ → ℕ → ℂ) (j k : ℕ) : ℂ :=
  coefficient (fun s => term s k) j

def coordinateCoefficient (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (j : ℕ) : ℂ :=
  coefficient ψ j + ∑' k : ℕ, termCoefficient term j k

def coordinatePolynomial (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), s ^ j * coordinateCoefficient ψ term j

theorem smaller_head_radius (c : ℝ) (hc : 0 < c) (J k : ℕ) (hk : k < J) :
    c / (J : ℝ) ^ 2 ≤ c / ((k : ℝ) + 1) ^ 2 := by
  have hkj : (k : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  exact div_le_div_of_nonneg_left hc.le (by positivity)
    (pow_le_pow_left₀ (by positivity) hkj 2)

theorem diffContOnCl_head (term : ℂ → ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (J : ℕ) : DiffContOnCl ℂ (finiteHead term J) (ball 0 (c / (J : ℝ) ^ 2)) := by
  have hsmall : ∀ k ∈ Finset.range J,
      DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / (J : ℝ) ^ 2)) := by
    intro k hk
    exact (hdisc k).mono (ball_subset_ball (smaller_head_radius c hc J k (Finset.mem_range.mp hk)))
  exact ⟨DifferentiableOn.fun_sum (fun k hk => (hsmall k hk).differentiableOn),
    continuousOn_finset_sum _ (fun k hk => (hsmall k hk).continuousOn)⟩

theorem norm_head_le (term : ℂ → ℕ → ℂ) (c M : ℝ) (N : ℕ)
    (hc : 0 < c) (hM : 0 ≤ M) (hN : 1 ≤ N)
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N))
    (J : ℕ) (s : ℂ) (hs : ‖s‖ ≤ c / (J : ℝ) ^ 2) :
    ‖finiteHead term J s‖ ≤ M * powerConstant (2 * N) := by
  have hsum := summable_parabolic_majorant M (show 2 ≤ 2 * N by omega)
  calc
    ‖finiteHead term J s‖ ≤ ∑ k ∈ Finset.range J, ‖term s k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range J, M / ((k : ℝ) + 1) ^ (2 * N) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound k s (hs.trans (smaller_head_radius c hc J k (Finset.mem_range.mp hk)))
    _ ≤ ∑' k : ℕ, M / ((k : ℝ) + 1) ^ (2 * N) := hsum.sum_le_tsum _ (fun _ _ => by positivity)
    _ = M * powerConstant (2 * N) := by
      rw [show (fun k : ℕ => M / ((k : ℝ) + 1) ^ (2 * N)) =
        fun k : ℕ => M * (1 / ((k : ℝ) + 1) ^ (2 * N)) by funext k; ring, tsum_mul_left]
      rfl

theorem head_coefficient_eq (term : ℂ → ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (J j : ℕ) : coefficient (finiteHead term J) j =
      ∑ k ∈ Finset.range J, termCoefficient term j k := by
  have hcda : ∀ k, ContDiffAt ℂ j (fun s => term s k) 0 := by
    intro k
    apply ((hdisc k).differentiableOn.analyticAt (ball_mem_nhds 0 (by positivity))).contDiffAt
  unfold coefficient finiteHead termCoefficient
  rw [iteratedDeriv_fun_sum (fun k _ => hcda k), Finset.sum_div]
  rfl

theorem norm_termCoefficient_le (term : ℂ → ℕ → ℂ) (c M : ℝ) (N j : ℕ)
    (hj : j ≤ N) (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) (k : ℕ) :
    ‖termCoefficient term j k‖ ≤ (M / c ^ j) / ((k : ℝ) + 1) ^ (2 * N - 2 * j) := by
  have h := HigherPreparedDerivative.norm_iteratedDeriv_term_le term c M N j hj hc hdisc hbound k
  have hfact : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [termCoefficient, coefficient, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right h hfact.le).trans_eq
  field_simp

/-- The integer rounding, including every coefficient-tail power, is
controlled at the common exponent, rather than passed in as an estimate. -/
theorem norm_scaled_tail_cutoff {a : ℕ → ℂ} {C s α β : ℝ} {p j : ℕ}
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1) (hp : 2 ≤ p)
    (ha : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ p)
    (hα : α ≤ (j : ℝ) + β * ((p - 1 : ℕ) : ℝ)) :
    ‖(s : ℂ) ^ j * (∑' k : ℕ, a (k + cutoff s β))‖ ≤
      (C * powerConstant p) * s ^ α := by
  have ht := norm_tsum_tail_le a C hC hp ha (cutoff s β) (cutoff_pos hs)
  have hnum := cutoff_scaled_tail_bound (β := β) (b := (j : ℝ))
    (d := ((p - 1 : ℕ) : ℝ)) hs (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast] at hnum
  have hcompare := Real.rpow_le_rpow_of_exponent_ge hs hs1 hα
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc
    s ^ j * ‖∑' k : ℕ, a (k + cutoff s β)‖ ≤
        s ^ j * (C * powerConstant p / (cutoff s β : ℝ) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (C * powerConstant p) *
        (s ^ j * ((cutoff s β : ℝ) ^ (p - 1))⁻¹) := by ring
    _ ≤ (C * powerConstant p) * s ^ ((j : ℝ) + β * ((p - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg hC (powerConstant_nonneg p))
    _ ≤ _ := mul_le_mul_of_nonneg_left hcompare (mul_nonneg hC (powerConstant_nonneg p))

theorem balanced_coefficient_tail_exponent (m N j : ℕ) (hm : 1 ≤ m)
    (hN : m * m + m + 1 ≤ N) (hj : j ≤ m) :
    (m : ℝ) + gamma m N ≤ (j : ℝ) + beta m N * ((2 * N - 2 * j - 1 : ℕ) : ℝ) := by
  have hjN : j + 1 ≤ N := by nlinarith
  have hsub : ((2 * N - 2 * j - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 * (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * N - 2 * j),
      Nat.cast_sub (by omega : 2 * j ≤ 2 * N)]
    push_cast
    ring
  rw [← tailExponent_eq_order_add_gamma, hsub]
  dsimp [tailExponent]
  have hβ := beta_lt_half m N hm hN
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

theorem balanced_head_remainder (term : ℂ → ℕ → ℂ) (c M : ℝ) (m N : ℕ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N) (hc : 0 < c) (hM : 0 ≤ M)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖finiteHead term (cutoff s (beta m N)) s -
        polynomial (finiteHead term (cutoff s (beta m N))) (m + 1) s‖ ≤
      (2 * M * powerConstant (2 * N) / c ^ (m + 1) * (2 : ℝ) ^ (2 * (m + 1))) *
        s ^ ((m : ℝ) + gamma m N) := by
  have hb := (beta_pos m N).le
  have hadm := cutoff_admissible hb (beta_lt_half m N hm hN) hc
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
  filter_upwards [hadm, hpos, hle] with s ha hs hs1
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

/-- The actual orbit sum has an order-m polynomial expansion with the
paper's strictly positive gain γ.  All coefficients are absolutely
convergent series of genuine finite-orbit Taylor coefficients. -/
theorem coordinate_expansion_from_disc_and_term_bounds
    (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (m N : ℕ) (r Mψ c M CT : ℝ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N))
    (hreal : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖term (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * N)) :
    (∀ j ≤ m, Summable (fun k => ‖termCoefficient term j k‖)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
        coordinatePolynomial ψ term m s‖ ≤ C * s ^ ((m : ℝ) + gamma m N) := by
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
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).filter_mono nhdsWithin_le_nhds
  have hα : (m : ℝ) + gamma m N ≤ ((m + 1 : ℕ) : ℝ) := by
    rw [← headExponent_eq_order_add_gamma]
    dsimp [headExponent]
    push_cast
    have hβ := beta_pos m N
    nlinarith
  have hmodel : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖ψ s - polynomial ψ (m + 1) s‖ ≤ Cψ * s ^ ((m : ℝ) + gamma m N) := by
    filter_upwards [hpos, hle, hsmall] with s hs hs1 hsr
    have ht := norm_remainder_le ψ r Mψ (m + 1) s hr hMψ hψ hψbound
      (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr.le)
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 hα
    simp only [Real.rpow_natCast] at hp
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at ht
    apply ht.trans
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Cψ)
    convert hh using 1 <;> first | rfl | (dsimp [Cψ]; ring)
  have hhead := balanced_head_remainder term c M m N hm hN hc hM hdisc hbound
  refine ⟨hsumδ, C, hC, ?_⟩
  filter_upwards [hpos, hle, hmodel, hhead, hreal] with s hs hs1 hmod hH hT
  let J := cutoff s (beta m N)
  have hsumT : Summable (term (s : ℂ)) :=
    summable_of_parabolic_bound _ CT (by nlinarith) hT
  have hsplitT := hsumT.sum_add_tsum_nat_add J
  have htailT : ‖∑' k : ℕ, term (s : ℂ) (k + J)‖ ≤
      CT * powerConstant (2 * N) * s ^ ((m : ℝ) + gamma m N) := by
    have ht := norm_scaled_tail_cutoff (j := 0) (β := beta m N) (α := (m : ℝ) + gamma m N)
      hCT hs hs1 (by nlinarith : 2 ≤ 2 * N) hT (by
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
      add_le_add (add_le_add (add_le_add hmod hH) htailT) htailδ
    _ = _ := by dsimp [C]; ring

end Kneser.HigherOrderCutoff

end
