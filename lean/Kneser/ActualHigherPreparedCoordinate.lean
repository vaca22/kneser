import Kneser.HigherOrderCutoff
import Kneser.HigherPreparedModelTime
import Kneser.PreparedActualFirstOrder

/-! Arbitrary-degree expansions for genuinely constructed exponential
prepared orbit series.  All shrinking discs and infinite real tails are
derived from the actual dynamics.  The preparation order is part of the
coordinate; compatibility after a common spatial normalization is separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ActualHigherPreparedCoordinate

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ParabolicExponentialOrbit
open Kneser.EvenPreparedOrbitDiscs Kneser.FirstOrderCutoff
open Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.HigherPreparedModelTime Kneser.ExponentialPreparedHigher
open scoped Topology BigOperators

/-- The actual shrinking-disc and positive-real estimates imply every
finite-order orbit coefficient is absolutely summable. -/
theorem prepared_higher_expansion
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (m N : ℕ) (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 →
        (∀ j ≤ m, Summable (fun k => ‖termCoefficient (descendedTerm A B Γ N u) j k‖)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ))
              (fun s : ℝ => descendedTerm A B Γ N u (s : ℂ)) s -
            coordinatePolynomial ψ (descendedTerm A B Γ N u) m s‖ ≤
              C * s ^ ((m : ℝ) + gamma m N) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_prepared_orbit_disc_bounds A B Γ N
    hAa hBa hA0 hB0 hΓa hEven
  have hΓcont := continuousAt_descendedFactor Γ hΓa.continuousAt
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) N hK hK0 hfactor hΓcont
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro u hu ψ hψ
  let Z : ℝ := ‖inverseCoordinate u‖
  have hZ : 0 ≤ Z := norm_nonneg _
  have hu' : R₀ ≤ (inverseCoordinate u).re := by linarith
  obtain ⟨c, M, hc, hM, hdisc, hbound⟩ :=
    hdiscs R₀ (le_max_left _ _) Z hZ u hu' (le_refl _)
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖descendedTerm A B Γ N u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * N) := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss k
    simpa only [descendedTerm_eq] using hterms s hs hss u hu (le_refl _) k
  obtain ⟨r, Mψ, hr, hMψ, hψdisc, hψbound⟩ :=
    PreparedActualFirstOrder.exists_analytic_disc_bounds ψ hψ
  exact coordinate_expansion_from_disc_and_term_bounds ψ (descendedTerm A B Γ N u)
    m N r Mψ c M CT hm hN hr hMψ hc hM hCT hψdisc hψbound hdisc hbound hterms'

theorem analyticAt_modelTime_parameter {U H : ℂ → ℂ} (n : ℕ)
    (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0) (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (fun s => modelTime U H n e s u) 0 := by
  have hsplit := analyticAt_splitModelTime n e hU hU0 hH hHne he u hu
  have hcurve : AnalyticAt ℂ (fun x => splitModelTime U H n e (x, u)) 0 :=
    hsplit.comp_of_eq (analyticAt_id.prod analyticAt_const) (by simp)
  have hdesc := AnalyticEvenDescent.analyticAt_even_sqrt
    (fun x => splitModelTime_even U H n e x u) hcurve
  simpa only [splitModelTime_sqrt] using hdesc

def actualCoordinate (U H : ℂ → ℂ) (N : ℕ)
    (e : Fin (2 * (N - 1)) → ℂ → ℂ) (A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) : ℂ :=
  coordinateSeries (fun s : ℝ => modelTime U H (N - 1) e s u)
    (fun s : ℝ => descendedTerm A B Γ N u s) s

def actualCoefficient (U H : ℂ → ℂ) (N : ℕ)
    (e : Fin (2 * (N - 1)) → ℂ → ℂ) (A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (u : ℂ) (j : ℕ) : ℂ :=
  coordinateCoefficient (fun s => modelTime U H (N - 1) e s u)
    (descendedTerm A B Γ N u) j

/-- For every requested order and admissible preparation order, actual
roots, finite polynomial, logarithmic residues, and residual are constructed.
The resulting actual orbit sum has the paper's positive remainder gain. -/
theorem exists_actual_higher_expansion (m N : ℕ)
    (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N) :
    ∃ U H A B : ℂ → ℂ, ∃ e : Fin (2 * (N - 1)) → ℂ → ℂ,
    ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (ExponentialPreparedModel.rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      (∀ i, AnalyticAt ℂ (e i) 0) ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
        unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        F p + correction (N - 1) e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          correction (N - 1) e (p.1 ^ 2) p.2 =
            rootPolynomial A B (p.1 ^ 2) p.2 ^ N * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
        (∀ j ≤ m, Summable (fun k =>
          ‖termCoefficient (descendedTerm A B Γ N u) j k‖)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖actualCoordinate U H N e A B Γ u s -
            ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
              actualCoefficient U H N e A B Γ u j‖ ≤
              C * s ^ ((m : ℝ) + gamma m N) := by
  have hN1 : 1 ≤ N := by omega
  have horder : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  obtain ⟨U, A, B, e, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he, hF, hΓ, hK0, hK, _hFeven, hΓeven, hq, hroots, hfactor, hprepared, hresidue⟩ :=
    exists_actual_prepared_order (N - 1)
  rw [horder] at hprepared
  obtain ⟨H, hH, hH0, hHlog⟩ :=
    ExponentialPreparedModel.exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  obtain ⟨R₀, hR₀, hhigher⟩ := prepared_higher_expansion A B K Γ
    hA hB hA0 hB0 hΓ hEven hK (by rw [hK0]; norm_num) hfactor m N hm hN
  refine ⟨U, H, A, B, e, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R₀, hR₀, ?_⟩
  intro u hu
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have huRe : u.re < 0 := by
    have h := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hpos
    simpa only [Complex.neg_re, neg_pos] using h
  exact hhigher u hu (fun s => modelTime U H (N - 1) e s u)
    (analyticAt_modelTime_parameter (N - 1) e hU hU0 hH hHne he u huRe)

end Kneser.ActualHigherPreparedCoordinate

end
