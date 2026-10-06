import Kneser.ReflectedEvenOrbitDiscs
import Kneser.ReflectedPreparedRealMajorant
import Kneser.N2FirstOrderCutoff
import Kneser.ExponentialPreparedQuadratic
import Kneser.ExponentialModelTime
import Kneser.ParabolicFatouCoordinate
import Kneser.UniformFirstOrderCutoff

/-!
First-order expansion of the actual prepared orbit series.  The roots,
analytic factors, complex finite-orbit estimates, and positive-real infinite
tail estimates are constructed, rather than postulated as decay conditions.
-/

noncomputable section

namespace Kneser.ReflectedPreparedFirstOrder

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ParabolicExponentialOrbit
open Kneser.ReflectedEvenOrbitDiscs Kneser.N2FirstOrderCutoff
open scoped Topology

def shiftedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (v s : ℂ) (k : ℕ) : ℂ :=
  descendedTerm A B Γ N v s (k + 1)

theorem disc_radius_shift_bound (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    (c / 4) / ((k : ℝ) + 1) ^ 2 ≤ c / ((k : ℝ) + 2) ^ 2 := by
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsq : ((k : ℝ) + 2) ^ 2 ≤ 4 * ((k : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_le_mul_of_nonneg_left hsq hc

theorem shifted_disc_bounds (term : ℂ → ℕ → ℂ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ 4) :
    (∀ k, DiffContOnCl ℂ (fun z => term z (k + 1))
      (ball 0 ((c / 4) / ((k : ℝ) + 1) ^ 2))) ∧
    (∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ (c / 4) / ((k : ℝ) + 1) ^ 2 →
      ‖term z (k + 1)‖ ≤ M / ((k : ℝ) + 1) ^ 4) := by
  constructor
  · intro k
    apply (hdisc (k + 1)).mono
    apply Metric.ball_subset_ball
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using disc_radius_shift_bound c hc.le k
  · intro k z hz
    have ht := hbound (k + 1) z (hz.trans (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using disc_radius_shift_bound c hc.le k))
    apply ht.trans
    apply div_le_div_of_nonneg_left hM (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) 4

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
theorem prepared_inverse_quadratic_first_order
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 →
        let term := shiftedTerm A B Γ 2 u
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
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
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
  obtain ⟨hdiscShift, hboundShift⟩ := shifted_disc_bounds (descendedTerm A B Γ 2 u) c M hc hM hdisc hbound
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖shiftedTerm A B Γ 2 u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4 := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss k
    have ht := hterms s hs hss u hu (le_refl _) (k + 1)
    change ‖descendedTerm A B Γ 2 u (s : ℂ) (k + 1)‖ ≤ _
    rw [descendedTerm_eq]
    apply ht.trans
    apply div_le_div_of_nonneg_left hCT (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) 4
  obtain ⟨r, Mψ, hr, hMψ, hψdisc, hψbound⟩ := exists_analytic_disc_bounds ψ hψ
  have he := coordinate_expansion_from_term_discs ψ (shiftedTerm A B Γ 2 u)
    r Mψ (c / 4) M CT hr hMψ (by positivity) hM hCT hψdisc hψbound hdiscShift hboundShift hterms'
  have hδ : ∀ k, ‖deriv (fun z => shiftedTerm A B Γ 2 u z k) 0‖ ≤
      (M / (c / 4)) / ((k : ℝ) + 1) ^ 2 :=
    norm_deriv_term_le (shiftedTerm A B Γ 2 u) (c / 4) M (by positivity) hdiscShift hboundShift
  refine ⟨summable_norm_of_parabolic_bound _ (M / (c / 4)) (q := 2) (by norm_num) hδ, ?_⟩
  let C := 2 * Mψ / r ^ 2 + 4 * M / (c / 4) ^ 2 +
    2 * (M + CT) * PowerSeriesTail.powerConstant 4 +
      (M / (c / 4)) * PowerSeriesTail.powerConstant 2
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

/-- Common model discs give a common first-order estimate on every bounded
set in the actual reflected inverse petal. All orbit and residual estimates
are derived from the actual preparation and actual inverse dynamics. -/
theorem prepared_inverse_quadratic_first_order_uniform
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∀ S : Set ℂ, (∀ v ∈ S, R + 1 ≤ (inverseCoordinate v).re ∧ ‖inverseCoordinate v‖ ≤ Z) →
      ∀ ψ : ℂ → ℂ → ℂ, ∀ r Mψ : ℝ, 0 < r → 0 ≤ Mψ →
        (∀ v ∈ S, DiffContOnCl ℂ (ψ v) (ball 0 r)) →
        (∀ v ∈ S, ∀ z ∈ sphere (0 : ℂ) r, ‖ψ v z‖ ≤ Mψ) →
        let δ := fun v k => deriv (fun z => shiftedTerm A B Γ 2 v z k) 0
        let X := fun v => coordinateSeries (fun s : ℝ => ψ v (s : ℂ))
          (fun s : ℝ => shiftedTerm A B Γ 2 v (s : ℂ))
        let d := fun v => firstOrderCoefficient (deriv (ψ v) 0) (δ v)
        ∃ C CD : ℝ, 0 ≤ C ∧ 0 ≤ CD ∧
          (∀ v ∈ S, ∀ k, ‖δ v k‖ ≤ CD / ((k : ℝ) + 1) ^ 2) ∧
          (∀ v ∈ S, Summable (fun k => ‖δ v k‖)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S, ‖X v s - X v 0 - s • d v‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S, ‖X v s - X v 0 - s • d v‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          (∀ v ∈ S, HasDerivWithinAt (X v) (d v) (Ici 0) 0) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_uniform_prepared_orbit_disc_bounds A B Γ 2
    hAa hBa hA0 hB0 hΓa hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) 2 hK hK0 hfactor
      (continuousAt_descendedFactor Γ hΓa.continuousAt)
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ S hS ψ r Mψ hr hMψ hψ hψbound
  dsimp only
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRR₂ : R₂ ≤ R := (le_max_right _ _).trans hR
  obtain ⟨c, M, hc, hM, hdiscData⟩ := hdiscs R hRR₁ Z hZ
  have hdiscShift : ∀ v ∈ S, ∀ k, DiffContOnCl ℂ (fun z => shiftedTerm A B Γ 2 v z k)
      (ball 0 ((c / 4) / ((k : ℝ) + 1) ^ 2)) := by
    intro v hv
    obtain ⟨hd, hb⟩ := hdiscData v (by linarith [(hS v hv).1]) (hS v hv).2
    exact (shifted_disc_bounds (descendedTerm A B Γ 2 v) c M hc hM hd hb).1
  have hboundShift : ∀ v ∈ S, ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ (c / 4) / ((k : ℝ) + 1) ^ 2 →
      ‖shiftedTerm A B Γ 2 v z k‖ ≤ M / ((k : ℝ) + 1) ^ 4 := by
    intro v hv
    obtain ⟨hd, hb⟩ := hdiscData v (by linarith [(hS v hv).1]) (hS v hv).2
    exact (shifted_disc_bounds (descendedTerm A B Γ 2 v) c M hc hM hd hb).2
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R hRR₂ Z hZ
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S, ∀ k,
      ‖shiftedTerm A B Γ 2 v (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4 := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss
    intro v hv k
    have ht := hterms s hs hss v (hS v hv).1 (hS v hv).2 (k + 1)
    change ‖descendedTerm A B Γ 2 v (s : ℂ) (k + 1)‖ ≤ _
    rw [descendedTerm_eq]
    apply ht.trans
    apply div_le_div_of_nonneg_left hCT (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) 4
  have hδbound : ∀ v ∈ S, ∀ k,
      ‖deriv (fun z => shiftedTerm A B Γ 2 v z k) 0‖ ≤ (M / (c / 4)) / ((k : ℝ) + 1) ^ 2 := by
    intro v hv
    exact norm_deriv_term_le (shiftedTerm A B Γ 2 v) (c / 4) M (by positivity)
      (hdiscShift v hv) (hboundShift v hv)
  obtain ⟨he, hd⟩ := UniformFirstOrderCutoff.coordinate_expansion_from_uniform_term_discs S ψ
    (fun v => shiftedTerm A B Γ 2 v) r Mψ (c / 4) M CT hr hMψ (by positivity) hM hCT
    hψ hψbound hdiscShift hboundShift hterms'
  let C := UniformFirstOrderCutoff.errorConstant r Mψ (c / 4) M CT
  have hC : 0 ≤ C := UniformFirstOrderCutoff.errorConstant_nonneg _ _ _ _ _
    hr (by positivity) hMψ hM hCT
  refine ⟨C, M / (c / 4), hC, by positivity, hδbound, ?_, he, ?_, hd⟩
  · intro v hv
    exact summable_norm_of_parabolic_bound _ (M / (c / 4)) (q := 2) (by norm_num) (hδbound v hv)
  · have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ hs => hs.le).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [he, self_mem_nhdsWithin, hsmall] with s hs hpos hs1
    intro v hv
    exact (hs v hv).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (show 0 < s from hpos) hs1 (by norm_num)) hC)

/-- The reflected logarithmic model uses the reflected roots and inverse
multiplier logarithms, together with the reflected polynomial correction. -/
def actualInversePreparedCoordinate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (v : ℂ) : ℝ → ℂ :=
  coordinateSeries
    (fun s : ℝ => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v)
    (fun s : ℝ => shiftedTerm A B Γ 2 v s)

def actualInversePreparedCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (v : ℂ) : ℂ :=
  firstOrderCoefficient
    (deriv (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0)
    (fun k => deriv (fun s => shiftedTerm A B Γ 2 v s k) 0)

set_option maxHeartbeats 1000000 in
/-- The actual exponential preparation gives a reflected inverse series
whose first parameter coefficient is an absolutely convergent orbit series.
No preparation-existence, dynamical, convergence, or Cauchy bound is assumed. -/
theorem exists_actual_repelling_first_order :
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
        Complex.log (1 + (p.2 - U (-p.1)) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ v : ℂ, R₀ + 1 ≤ (inverseCoordinate v).re →
        Summable (fun k => ‖deriv (fun s => shiftedTerm A B Γ 2 v s k) 0‖) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0,
            ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
              actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
              s • actualInversePreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0,
            ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
              actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
              s • actualInversePreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          HasDerivWithinAt (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v)
            (actualInversePreparedCoefficient U H e₁ e₂ A B Γ v) (Ici 0) 0 := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he₁, he₂, hF, hΓ, hK0, hK, _hFeven, hΓeven, hfactor, hprepared, hresidue, hq, hroots⟩ :=
    ExponentialPreparedQuadratic.exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := ExponentialPreparedModel.exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hΓeven' : ∀ x v, Γ (-x, v) = Γ (x, v) := by
    intro x v
    exact hΓeven (x, v)
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨R, hR, hresult⟩ := prepared_inverse_quadratic_first_order A B K Γ
    hA hB hA0 hB0 hΓ hΓeven' hK hKne hfactor
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, ?_, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R, hR, ?_⟩
  · intro p
    exact hΓeven p
  · intro v hv
    have hpos : 0 < (inverseCoordinate v).re := by linarith
    have hneg : v.re < 0 := by
      have h := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hpos
      simpa only [Complex.neg_re, neg_pos] using h
    have hψ : AnalyticAt ℂ
        (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0 := by
      apply ExponentialModelTime.analyticAt_preparedModelTime_curve hU.neg
        (by simp only [Pi.neg_apply, hU0, neg_zero]) hH.neg
        (by simpa only [Pi.neg_apply, neg_ne_zero] using hHne) he₁ he₂.neg
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => v) 0)
      exact hneg
    let ψ : ℂ → ℂ := fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v
    have hXe : actualInversePreparedCoordinate U H e₁ e₂ A B Γ v =
        coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => shiftedTerm A B Γ 2 v s) := rfl
    have hde : actualInversePreparedCoefficient U H e₁ e₂ A B Γ v =
        firstOrderCoefficient (deriv ψ 0) (fun k => deriv (fun s => shiftedTerm A B Γ 2 v s k) 0) := rfl
    rw [hXe, hde]
    exact hresult v hv ψ hψ

end Kneser.ReflectedPreparedFirstOrder

end
