import Kneser.EvenPreparedOrbitDiscs
import Kneser.ActualRootPolynomialOrbit
import Kneser.N2FirstOrderCutoff
import Kneser.ExponentialPreparedQuadratic
import Kneser.ExponentialModelTime
import Kneser.ParabolicFatouCoordinate

/-!
First-order expansion of the actual prepared orbit series.  The roots,
analytic factors, complex finite-orbit estimates, and positive-real infinite
tail estimates are constructed, rather than postulated as decay conditions.
-/

noncomputable section

namespace Kneser.PreparedActualFirstOrder

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ParabolicExponentialOrbit
open Kneser.EvenPreparedOrbitDiscs Kneser.N2FirstOrderCutoff
open scoped Topology

theorem exists_analytic_disc_bounds (ψ : ℂ → ℂ) (hψ : AnalyticAt ℂ ψ 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ DiffContOnCl ℂ ψ (ball 0 r) ∧
      ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ M := by
  let M : ℝ := ‖ψ 0‖ + 1
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖ψ z‖ < M :=
    hψ.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp
    (hψ.eventually_analyticAt.and hbound)
  refine ⟨η / 2, M, by positivity, by dsimp [M]; positivity, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ ψ (closedBall 0 (η / 2)) := by
      intro z hz
      have hz' : dist z 0 < η := by
        have hn : dist z 0 ≤ η / 2 := hz
        linarith
      exact (hηball hz').1.differentiableAt.differentiableWithinAt
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
  · intro z hz
    have hn : dist z 0 = η / 2 := hz
    exact (hηball (by rw [hn]; linarith)).2.le

/-- For the true exponential orbit, the explicit derivative series is
absolutely convergent and gives a `6/5` (hence `10/9`) one-sided expansion.
Every dynamical or Cauchy estimate in this statement is a conclusion. -/
theorem prepared_quadratic_first_order
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 →
        let term := descendedTerm A B Γ 2 u
        let δ := fun k => deriv (fun z => term z k) 0
        let X := coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ))
        let d := firstOrderCoefficient (deriv ψ 0) δ
        Summable (fun k => ‖δ k‖) ∧ ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ‖X s - X 0 - s • d‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ‖X s - X 0 - s • d‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          HasDerivWithinAt X d (Ici 0) 0 := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_prepared_orbit_disc_bounds A B Γ 2
    hAa hBa hA0 hB0 hΓa hEven
  have hΓcont := continuousAt_descendedFactor Γ hΓa.continuousAt
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) 2 hK hK0 hfactor hΓcont
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro u hu ψ hψ
  dsimp only
  let Z : ℝ := ‖inverseCoordinate u‖
  have hZ : 0 ≤ Z := norm_nonneg _
  have hu' : R₀ ≤ (inverseCoordinate u).re := by linarith
  obtain ⟨c, M, hc, hM, hdisc, hbound⟩ :=
    hdiscs R₀ (le_max_left _ _) Z hZ u hu' (le_refl _)
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖descendedTerm A B Γ 2 u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4 := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss k
    simpa only [descendedTerm_eq] using hterms s hs hss u hu (le_refl _) k
  obtain ⟨r, Mψ, hr, hMψ, hψdisc, hψbound⟩ := exists_analytic_disc_bounds ψ hψ
  have he := coordinate_expansion_from_term_discs ψ (descendedTerm A B Γ 2 u)
    r Mψ c M CT hr hMψ hc hM hCT hψdisc hψbound hdisc hbound hterms'
  have hδ : ∀ k, ‖deriv (fun z => descendedTerm A B Γ 2 u z k) 0‖ ≤
      (M / c) / ((k : ℝ) + 1) ^ 2 :=
    norm_deriv_term_le (descendedTerm A B Γ 2 u) c M hc hdisc hbound
  refine ⟨summable_norm_of_parabolic_bound _ (M / c) (q := 2) (by norm_num) hδ, ?_⟩
  let C := 2 * Mψ / r ^ 2 + 4 * M / c ^ 2 +
    2 * (M + CT) * PowerSeriesTail.powerConstant 4 +
      (M / c) * PowerSeriesTail.powerConstant 2
  have hC : 0 ≤ C := by
    have hp4 := PowerSeriesTail.powerConstant_nonneg 4
    have hp2 := PowerSeriesTail.powerConstant_nonneg 2
    dsimp [C]
    positivity
  refine ⟨C, hC, he.1, ?_, he.2⟩
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ hs => hs.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [he.1, self_mem_nhdsWithin, hsmall] with s hs hpos hs1
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (show 0 < s from hpos) hs1 (by norm_num)) hC)

def actualPreparedCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s : ℝ) : ℂ :=
  coordinateSeries (fun s : ℝ => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u)
    (fun s : ℝ => descendedTerm A B Γ 2 u s) s

def actualPreparedCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) : ℂ :=
  firstOrderCoefficient
    (deriv (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) 0)
    (fun k => deriv (fun s => descendedTerm A B Γ 2 u s k) 0)

/-- An unconditional existence theorem for the actual exponential family's
prepared attracting series and its absolutely convergent first coefficient.
The model and preparation witnesses are constructed in the proof. -/
theorem exists_actual_attracting_first_order :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (ExponentialPreparedModel.rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
        unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        F p + ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2)
            (unfolding (p.1 ^ 2) p.2) -
          ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
            rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
        Summable (fun k => ‖deriv (fun s => descendedTerm A B Γ 2 u s k) 0‖) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • actualPreparedCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • actualPreparedCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          HasDerivWithinAt (actualPreparedCoordinate U H e₁ e₂ A B Γ u)
            (actualPreparedCoefficient U H e₁ e₂ A B Γ u) (Ici 0) 0 := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he₁, he₂, hF, hΓ, hK0, hK, hFeven, hΓeven, hfactor, hprepared, hresidue, hq, hroots⟩ :=
    ExponentialPreparedQuadratic.exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := ExponentialPreparedModel.exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  obtain ⟨R₀, hR₀, hfirst⟩ := prepared_quadratic_first_order A B K Γ
    hA hB hA0 hB0 hΓ hEven hK (by rw [hK0]; norm_num) hfactor
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R₀, hR₀, ?_⟩
  intro u hu
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have huRe : u.re < 0 := by
    have h := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hpos
    simpa only [Complex.neg_re, neg_pos] using h
  exact hfirst u hu (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u)
    (ExponentialModelTime.analyticAt_preparedModelTime_parameter hU hU0 hH hHne he₁ he₂ u huRe)

end Kneser.PreparedActualFirstOrder

end
