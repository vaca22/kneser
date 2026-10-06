import Kneser.ExponentialLogDefect

/-!
# The actual quadratic prepared correction

Two analytic coefficients are constructed by interpolation, and repeated
moving-root division proves a square of the actual root polynomial in the
corrected logarithmic defect. This is the N=2 prepared model.
-/

noncomputable section

namespace Kneser.ExponentialPreparedQuadratic

open Kneser.ExponentialLogDefect Kneser.PreparedTwoRootDivision
open Kneser.ExponentialPreparedModel Kneser.ExponentialMatrixDividedDifference
open Kneser.ExponentialUnfolding Filter
open scoped Topology

def rootProduct (U : ℂ → ℂ) (x u : ℂ) : ℂ := (u - U x) * (u - U (-x))

theorem rootProduct_even (U : ℂ → ℂ) (x u : ℂ) :
    rootProduct U (-x) u = rootProduct U x u := by
  simp only [rootProduct, neg_neg, mul_comm]

theorem exists_prepared_quadratic {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) :
    ∃ e₁ e₂ : ℂ → ℂ, ∃ F Γ : Pair → ℂ,
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧
      AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p, F (reflectFirst p) = F p) ∧
      (∀ p, Γ (reflectFirst p) = Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
          rootProduct U p.1 p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) := by
  obtain ⟨F, φ, hFa, hφa, hFeven, hφeven, hFfactor, hFresidue⟩ :=
    exists_analytic_log_defect hU hU0 hUd hroots hdistinct
  have hK0 : symmetricCofactor U 0 0 = 1 / 2 :=
    symmetricCofactor_zero hU hU0 hroots hdistinct
  have hKroota : AnalyticAt ℂ (fun x => symmetricCofactor U x (U x)) 0 :=
    analyticAt_symmetricCofactor hU analyticAt_id rfl hU
  have hKroot0 : symmetricCofactor U 0 (U 0) ≠ 0 := by rw [hU0, hK0]; norm_num
  have hcpa : AnalyticAt ℂ (fun x => (x, U x)) 0 := analyticAt_id.prod hU
  have hcp0 : ((0 : ℂ), U 0) = (0 : Pair) := by simp [hU0]
  have hφroota : AnalyticAt ℂ (fun x => φ (x, U x)) 0 := hφa.comp_of_eq hcpa hcp0
  let v : ℂ → ℂ := fun x => -φ (x, U x) / symmetricCofactor U x (U x)
  have hva : AnalyticAt ℂ v 0 := hφroota.neg.div hKroota hKroot0
  obtain ⟨e₁, e₂, he₁a, he₂a, heval⟩ := exists_analytic_quadratic_interpolant hU hUd hva
  let T : Pair → ℂ := fun p => φ p + symmetricCofactor U p.1 p.2 *
    (e₁ (p.1 ^ 2) + e₂ (p.1 ^ 2) * (unfolding (p.1 ^ 2) p.2 + p.2))
  have hKa : AnalyticAt ℂ (fun p : Pair => symmetricCofactor U p.1 p.2) 0 :=
    analyticAt_symmetricCofactor hU analyticAt_fst rfl analyticAt_snd
  have he₁p : AnalyticAt ℂ (fun p : Pair => e₁ (p.1 ^ 2)) 0 :=
    he₁a.comp_of_eq (f := fun p : Pair => p.1 ^ 2) (analyticAt_fst.pow 2) (by simp)
  have he₂p : AnalyticAt ℂ (fun p : Pair => e₂ (p.1 ^ 2)) 0 :=
    he₂a.comp_of_eq (f := fun p : Pair => p.1 ^ 2) (analyticAt_fst.pow 2) (by simp)
  have hfpa : AnalyticAt ℂ (fun p : Pair => unfolding (p.1 ^ 2) p.2) 0 := by
    have hx : AnalyticAt ℂ (fun p : Pair => p.1 ^ 2) 0 := analyticAt_fst.pow 2
    exact ((hx.neg.add ((analyticAt_const.sub hx).mul analyticAt_snd)).cexp).sub analyticAt_const
  have hTa : AnalyticAt ℂ T 0 :=
    hφa.add (hKa.mul (he₁p.add (he₂p.mul (hfpa.add analyticAt_snd))))
  have hTeven : ∀ p, T (reflectFirst p) = T p := by
    intro p
    dsimp [T, reflectFirst]
    rw [show φ (-p.1, p.2) = φ p from hφeven p,
      symmetricCofactor_even, neg_sq]
  have hKnear : ∀ᶠ x in 𝓝 0, symmetricCofactor U x (U x) ≠ 0 :=
    hKroota.continuousAt.eventually_ne hKroot0
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hTzero : ∀ᶠ x in 𝓝 0, T (x, U x) = 0 ∧ T (x, U (-x)) = 0 := by
    filter_upwards [hroots, heval, hKnear, hneg.eventually hKnear] with x hr he hk hnk
    have hφv : φ (x, U x) + symmetricCofactor U x (U x) * v x = 0 := by
      dsimp [v]
      field_simp [hk]
      ring
    have hφvn : φ (x, U (-x)) + symmetricCofactor U x (U (-x)) * v (-x) = 0 := by
      have h := (show φ (-x, U (-x)) + symmetricCofactor U (-x) (U (-x)) * v (-x) = 0 by
        dsimp [v]; field_simp [hnk]; ring)
      rw [show φ (-x, U (-x)) = φ (x, U (-x)) from hφeven (x, U (-x)),
        symmetricCofactor_even] at h
      exact h
    constructor
    · dsimp [T]
      rw [hr.1]
      linear_combination hφv + symmetricCofactor U x (U x) * he.1
    · dsimp [T]
      rw [hr.2]
      linear_combination hφvn + symmetricCofactor U x (U (-x)) * he.2
  obtain ⟨D, hDa, hD⟩ := exists_two_root_factor hTa hU hU0 hdistinct hTzero
  let Γ := symmetrizeFirst D
  have hΓfactor : ∀ᶠ p in 𝓝 (0 : Pair), T p = rootProduct U p.1 p.2 * Γ p := by
    filter_upwards [hD, reflectFirst_tendsto.eventually hD] with p hp hnp
    rw [hTeven] at hnp
    simp only [reflectFirst, neg_neg] at hnp
    dsimp [rootProduct, Γ, symmetrizeFirst, reflectFirst]
    linear_combination (hp + hnp) / 2
  refine ⟨e₁, e₂, F, Γ, he₁a, he₂a, hFa, analyticAt_symmetrizeFirst hDa,
    hFeven, symmetrizeFirst_even D, ?_, hFresidue⟩
  have hfactor := eventually_symmetricCofactor_factor hU hroots hdistinct
  have hfst : Tendsto (fun p : Pair => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  filter_upwards [hFfactor, hΓfactor, hfst.eventually hfactor] with p hF hΓ hf
  have hP := polynomialCorrection_difference e₁ e₂ (p.1 ^ 2) p.2
    (rootProduct U p.1 p.2) (symmetricCofactor U p.1 p.2) (hf p.2)
  change F p = rootProduct U p.1 p.2 * φ p at hF
  dsimp [T] at hΓ
  linear_combination hF + hP + rootProduct U p.1 p.2 * hΓ

/-- All root, cofactor, and prepared-model witnesses are constructed together
for the actual exponential unfolding. There are no root-existence or
prepared-model hypotheses in this final existence theorem. -/
theorem exists_actual_prepared_quadratic :
    ∃ U a b e₁ e₂ : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : Pair → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ a 0 = 0 ∧ b 0 = 0 ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧
      AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : Pair => K p.1 p.2) 0 ∧
      (∀ p, F (reflectFirst p) = F p) ∧
      (∀ p, Γ (reflectFirst p) = Γ p) ∧
      (∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u =
        Kneser.ExponentialRootPolynomial.rootPolynomial a b s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
          Kneser.ExponentialRootPolynomial.rootPolynomial a b (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) ∧
      (∀ x u, Kneser.ExponentialRootPolynomial.rootPolynomial a b (x ^ 2) u =
        (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) := by
  obtain ⟨U, a, b, hU, hU0, hUd, ha, hb, ha0, hb0, hasum, hbprod, hq,
    hroots, hdistinct⟩ := Kneser.ExponentialRootPolynomial.exists_analytic_rootPolynomial
  obtain ⟨e₁, e₂, F, Γ, he₁, he₂, hF, hΓ, hFeven, hΓeven, hprepared, hresidue⟩ :=
    exists_prepared_quadratic hU hU0 hUd hroots hdistinct
  refine ⟨U, a, b, e₁, e₂, descendedCofactor U, F, Γ,
    hU, hU0, hUd, ha, hb, ha0, hb0, he₁, he₂, hF, hΓ, ?_, ?_,
    hFeven, hΓeven, ?_, ?_, hresidue, hq, hroots⟩
  · simpa only [descendedCofactor, Complex.sqrt_zero] using
      symmetricCofactor_zero hU hU0 hroots hdistinct
  · exact continuousAt_descendedCofactor hU 0
  · have hsqrt : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.sqrt_zero] using
        (Complex.continuousAt_sqrt (Or.inl (by simp : (0 : ℝ) ≤ (0 : ℂ).re))).tendsto
    have hf := hsqrt.eventually (eventually_symmetricCofactor_factor hU hroots hdistinct)
    filter_upwards [hf] with s hs u
    have h := hs u
    rw [← hq (Complex.sqrt s) u, Kneser.AnalyticEvenDescent.square_sqrt] at h
    exact h
  · filter_upwards [hprepared] with p hp
    rw [hq]
    exact hp

end Kneser.ExponentialPreparedQuadratic

end
