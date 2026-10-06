import Kneser.FourierSewingLambdaComparison

/-!
The quantitative W2 Fourier sewing construction.  Q, P and the same
normalizing translation are constructed, and their actual translated
coefficients obey the exponentially small comparison.  The assumptions
are mode decay, strip geometry and explicit numerical smallness.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def bandWidth (h Y : ℝ) : ℝ := h / 2 - Y - 1
def sewingWidth (h Y D ρ : ℝ) : ℝ := bandWidth h Y - D - ρ
def gapFactor (Y D ρ : ℝ) : ℝ := Real.exp (2 * Real.pi * (2 * Y + 2 + D + 2 * ρ))
def pointFactor (Y D ρ : ℝ) : ℝ := Real.exp (2 * Real.pi * (Y + D + ρ + 2))
def normalizationConstant (Y D ρ M : ℝ) : ℝ :=
  2 * M * gapFactor Y D ρ + 2 * ρ * pointFactor Y D ρ
def hornSizeConstant (Y M : ℝ) (n : ℕ) : ℝ :=
  M * Real.exp (2 * Real.pi * (n : ℝ) * (Y + 1))
def hornErrorConstant (Y D ρ M : ℝ) (n : ℕ) : ℝ :=
  2 * M * Real.exp (2 * Real.pi * (n : ℝ) * (Y + 1 + ρ)) * gapFactor Y D ρ
def comparisonConstant (Y D ρ M : ℝ) (n : ℕ) : ℝ :=
  (hornSizeConstant Y M n * ‖Kneser.fourierFrequency n‖ *
      normalizationConstant Y D ρ M + hornErrorConstant Y D ρ M n) *
    Real.exp ‖Kneser.fourierFrequency n‖

theorem gap_rate_identity (h Y D ρ : ℝ) :
    Real.exp (-2 * Real.pi * (bandWidth h Y + sewingWidth h Y D ρ - ρ)) =
      lambda h * gapFactor Y D ρ := by
  rw [lambda, gapFactor, ← Real.exp_add]
  congr 1
  simp only [sewingWidth, bandWidth]
  ring

theorem centre_im (h : ℝ) (t₀ : ℂ) (ht₀ : t₀.im = h / 2) :
    (normalizingCentre h t₀).im = h / 2 := by
  simp [normalizingCentre, ht₀]
  ring

theorem point_rate_identity (h Y D ρ : ℝ) (t₀ : ℂ) (ht₀ : t₀.im = h / 2) :
    normalizationRate (sewingWidth h Y D ρ) (normalizingCentre h t₀) =
      lambda h * pointFactor Y D ρ := by
  rw [normalizationRate, centre_im h t₀ ht₀, lambda, pointFactor, ← Real.exp_add]
  congr 1
  unfold sewingWidth bandWidth
  ring

theorem div_one_sub_le_two (q C : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) (hC : 0 ≤ C) :
    C * q / (1 - q) ≤ 2 * C * q := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith [mul_nonneg hC hq, mul_le_mul_of_nonneg_left hqhalf (mul_nonneg hC hq)]

theorem norm_raw_horn_le (h Y M : ℝ) (t₀ : ℂ) (ht₀ : t₀.im = h / 2)
    (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * bandWidth h Y))
    (n : ℕ) (hn : 1 ≤ n) :
    ‖t n * hornPhase t₀ n‖ ≤ hornSizeConstant Y M n := by
  have hnne : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (by omega : 0 < n))
  rw [norm_mul, norm_hornPhase h t₀ ht₀]
  calc
    _ ≤ (M * Real.exp (-2 * Real.pi * |((n : ℤ) : ℝ)| * bandWidth h Y)) *
        Real.exp (Real.pi * ((n : ℤ) : ℝ) * h) :=
      mul_le_mul_of_nonneg_right (ht n hnne) (Real.exp_pos _).le
    _ = hornSizeConstant Y M n := by
      simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ _)]
      rw [mul_assoc, ← Real.exp_add]
      unfold hornSizeConstant bandWidth
      congr 2
      ring

theorem norm_positive_horn_error_le (h Y D ρ M : ℝ) (hM : 0 ≤ M)
    (hH : 0 ≤ sewingWidth h Y D ρ) (hgap : 0 < bandWidth h Y + sewingWidth h Y D ρ - ρ)
    (hq : lambda h * gapFactor Y D ρ ≤ 1 / 2)
    (t₀ : ℂ) (ht₀ : t₀.im = h / 2) (t : ℤ → ℂ)
    (hv : Summable (valueBudget (sewingWidth h Y D ρ) ρ t))
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * bandWidth h Y))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (hneg : Q ∈ Negative) (n : ℕ) :
    ‖(coefficient (sewingWidth h Y D ρ)
        (positiveProjection (composition (sewingWidth h Y D ρ) hH t Q)) n - t n) * hornPhase t₀ n‖ ≤
      hornErrorConstant Y D ρ M n * lambda h := by
  have he := norm_positive_coefficient_sub_le_decay (sewingWidth h Y D ρ) hH ρ
    (bandWidth h Y) M hM hgap t hv ht Q hQ hneg n (by exact_mod_cast Nat.zero_le n)
  have hgpos : 0 ≤ lambda h * gapFactor Y D ρ := by unfold lambda gapFactor; positivity
  rw [gap_rate_identity] at he
  have hdiv := div_one_sub_le_two (lambda h * gapFactor Y D ρ)
    (M * Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * (bandWidth h Y - ρ))) hgpos hq (by positivity)
  rw [norm_mul, norm_hornPhase h t₀ ht₀]
  calc
    _ ≤ (2 * (M * Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * (bandWidth h Y - ρ))) *
        (lambda h * gapFactor Y D ρ)) * Real.exp (Real.pi * ((n : ℤ) : ℝ) * h) :=
      mul_le_mul_of_nonneg_right (he.trans hdiv) (Real.exp_pos _).le
    _ = hornErrorConstant Y D ρ M n * lambda h := by
      have hexp : Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * (bandWidth h Y - ρ)) *
          Real.exp (Real.pi * ((n : ℤ) : ℝ) * h) =
          Real.exp (2 * Real.pi * (n : ℝ) * (Y + 1 + ρ)) := by
        rw [← Real.exp_add]
        congr 1
        simp only [Int.cast_natCast]
        unfold bandWidth
        ring
      unfold hornErrorConstant
      calc
        _ = (2 * M * (Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * (bandWidth h Y - ρ)) *
            Real.exp (Real.pi * ((n : ℤ) : ℝ) * h))) * gapFactor Y D ρ * lambda h := by ring
        _ = _ := by rw [hexp]

/-- A complete quantitative Fourier sewing kernel, using the same
constructed Q, P and normalizing ζ for every positive mode.  No sewing
fixed point, normalization root or coefficient comparison is assumed. -/
theorem exists_quantitative_sewing (h Y D ρ M : ℝ)
    (hD : 0 < D) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hH : 0 ≤ sewingWidth h Y D ρ)
    (t₀ : ℂ) (ht₀ : t₀.im = h / 2) (t : ℤ → ℂ) (htzero : t 0 = 0)
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * bandWidth h Y))
    (hvalueD : 2 * M * Real.exp (-2 * Real.pi * D) / (1 - Real.exp (-2 * Real.pi * D)) ≤ ρ)
    (hderivativeD : 4 * Real.pi * M * Real.exp (-2 * Real.pi * D) /
      (1 - Real.exp (-2 * Real.pi * D)) ^ 2 ≤ 1 / 2)
    (hqgap : lambda h * gapFactor Y D ρ ≤ 1 / 2)
    (hqpoint : lambda h * pointFactor Y D ρ ≤ 1 / 2)
    (hnormalization : normalizationConstant Y D ρ M * lambda h ≤ 1)
    (hnormalizationLip : normalizationLipschitzBound (sewingWidth h Y D ρ)
      (normalizingCentre h t₀) ρ ≤ 1 / 2) :
    ∃ Q P : Space, ∃ ζ : ℂ,
      Q ∈ Negative ∧ ‖Q‖ ≤ ρ ∧
      (∀ n : ℤ, n < 0 → P n = 0) ∧ ‖P‖ ≤ ρ ∧
      P = positiveProjection (composition (sewingWidth h Y D ρ) hH t Q) ∧
      Q = -negativeProjection (composition (sewingWidth h Y D ρ) hH t Q) ∧
      ‖ζ‖ ≤ normalizationConstant Y D ρ M * lambda h ∧ ‖ζ‖ ≤ 1 ∧
      (normalizingCentre h t₀ + ζ) +
        evaluate (sewingWidth h Y D ρ) P (normalizingCentre h t₀ + ζ) =
          normalizingCentre h t₀ ∧
      (∀ z : ℂ, |z.im| ≤ sewingWidth h Y D ρ →
        (z + evaluate (sewingWidth h Y D ρ) Q z) + t₀ +
          periodicFunction t (z + evaluate (sewingWidth h Y D ρ) Q z) =
            z + t₀ + evaluate (sewingWidth h Y D ρ) P z) ∧
      (∀ n : ℕ, 1 ≤ n →
        ‖translatedCoefficient (sewingWidth h Y D ρ) h P t₀ ζ n / (lambda h : ℂ) ^ n -
            t n * hornPhase t₀ n‖ ≤ comparisonConstant Y D ρ M n * lambda h) := by
  have hwidth : sewingWidth h Y D ρ + ρ + D = bandWidth h Y := by
    unfold sewingWidth
    ring
  have hdecay : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤
      M * Real.exp (-2 * Real.pi * |(m : ℝ)| * (sewingWidth h Y D ρ + ρ + D)) := by
    simpa only [hwidth] using ht
  obtain ⟨hv, hd, hvsum, hdsum⟩ := budgets_of_mode_decay (sewingWidth h Y D ρ) ρ D M hD hM t htzero hdecay
  obtain ⟨Q, P, hneg, hQ, hpos, hP, hproj, hfixed, hsew⟩ :=
    exists_nonlinear_sewing (sewingWidth h Y D ρ) hH ρ hρ t hv hd
      (hvsum.trans hvalueD) (hdsum.trans hderivativeD)
  have hgap : 0 < bandWidth h Y + sewingWidth h Y D ρ - ρ := by
    have he : Real.exp (-2 * Real.pi * (bandWidth h Y + sewingWidth h Y D ρ - ρ)) < 1 := by
      rw [gap_rate_identity]
      exact hqgap.trans_lt (by norm_num)
    rw [Real.exp_lt_one_iff] at he
    nlinarith [Real.pi_pos]
  have hpointgap : 0 < sewingWidth h Y D ρ + (normalizingCentre h t₀).im - 1 := by
    have he : normalizationRate (sewingWidth h Y D ρ) (normalizingCentre h t₀) < 1 := by
      rw [point_rate_identity h Y D ρ t₀ ht₀]
      exact hqpoint.trans_lt (by norm_num)
    unfold normalizationRate at he
    rw [Real.exp_lt_one_iff] at he
    nlinarith [Real.pi_pos]
  let B := M * (lambda h * gapFactor Y D ρ) / (1 - lambda h * gapFactor Y D ρ)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply div_nonneg (by unfold lambda gapFactor; positivity)
    linarith
  have hconstant : ‖coefficient (sewingWidth h Y D ρ) P 0‖ ≤ B := by
    rw [hproj]
    have he := norm_positive_coefficient_sub_le_decay (sewingWidth h Y D ρ) hH ρ
      (bandWidth h Y) M hM hgap t hv ht Q hQ hneg 0 le_rfl
    rw [gap_rate_identity] at he
    simpa [htzero, B] using he
  have hnormalBound : normalizationValueBound (sewingWidth h Y D ρ)
      (normalizingCentre h t₀) ρ B ≤ normalizationConstant Y D ρ M * lambda h := by
    rw [normalizationValueBound, point_rate_identity h Y D ρ t₀ ht₀]
    have hg := div_one_sub_le_two (lambda h * gapFactor Y D ρ) M
      (by unfold lambda gapFactor; positivity) hqgap hM
    have hp := div_one_sub_le_two (lambda h * pointFactor Y D ρ) ρ
      (by unfold lambda pointFactor; positivity) hqpoint hρ
    dsimp [B]
    exact (add_le_add hg hp).trans_eq (by unfold normalizationConstant; ring)
  obtain ⟨ζ, hζbound, hζone, hroot⟩ := exists_normalizing_shift (sewingWidth h Y D ρ) P hpos
    (normalizingCentre h t₀) ρ B hpointgap hρ hB hP hconstant
    (hnormalBound.trans hnormalization) hnormalizationLip
  have hζ : ‖ζ‖ ≤ normalizationConstant Y D ρ M * lambda h := hζbound.trans hnormalBound
  refine ⟨Q, P, ζ, hneg, hQ, hpos, hP, hproj, hfixed, hζ, hζone, hroot,
    (fun z hz => hsew z hz t₀), ?_⟩
  intro n hn
  apply norm_translated_coefficient_sub_le (sewingWidth h Y D ρ) h P t₀ ζ (t n) n
    (hornSizeConstant Y M n) (hornErrorConstant Y D ρ M n) (normalizationConstant Y D ρ M)
    (by unfold hornSizeConstant; positivity)
    (by unfold hornErrorConstant gapFactor; positivity)
    (by unfold normalizationConstant gapFactor pointFactor; positivity)
    (norm_raw_horn_le h Y M t₀ ht₀ t ht n hn) _ hζ hζone
  rw [hproj]
  exact norm_positive_horn_error_le h Y D ρ M hM hH hgap hqgap t₀ ht₀ t hv ht Q hQ hneg n

end Kneser.FourierSewing

end
