import Kneser.PreparedActualFirstOrder
import Kneser.PreparedSpatialHolomorphy

/-!
# Actual local Abel equation for the prepared attracting series

The logarithmic branch inequalities follow from continuity, rather than
being supplied as hypotheses. The orbit correction then satisfies the Abel
equation by the shift of an absolutely convergent actual exponential orbit.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.PreparedLocalAbel

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialModelTime
open Kneser.EvenPreparedOrbitDiscs Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder
open scoped Topology BigOperators

/-- The actual finite orbit starting at the first image is the shifted orbit. -/
theorem orbit_shift (u s : ℂ) (k : ℕ) :
    orbit (unfolding s u) s k = orbit u s (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [orbit_succ, ih]

/-- The prepared residual series at the image is exactly the shifted series. -/
theorem descendedTerm_shift (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u s : ℂ) (k : ℕ) :
    descendedTerm A B Γ N (unfolding s u) s k = descendedTerm A B Γ N u s (k + 1) := by
  simp only [descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt, orbit_shift]

/-- Absolute convergence at one point supplies convergence at its image,
without a further dynamical assumption at that image. -/
theorem summable_descendedTerm_shift (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u s : ℂ) (hs : Summable (fun k => ‖descendedTerm A B Γ N u s k‖)) :
    Summable (fun k => ‖descendedTerm A B Γ N (unfolding s u) s k‖) := by
  exact ((summable_nat_add_iff 1).mpr hs).congr
    (fun k => (congrArg norm (descendedTerm_shift A B Γ N u s k)).symm)

/-- The exact actual-series Abel equation only needs the genuine model
defect at the initial point and convergence of its residual series. -/
theorem actualPreparedCoordinate_abel (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s : ℝ)
    (hdefect : preparedModelTime U H e₁ e₂ s (unfolding s u) -
      preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0)
    (hs : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖)) :
    actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s u) s =
      actualPreparedCoordinate U H e₁ e₂ A B Γ u s + 1 := by
  have heq := hs.of_norm.tsum_eq_zero_add
  have hshift : (∑' k : ℕ, descendedTerm A B Γ 2 (unfolding s u) s k) =
      (∑' k : ℕ, descendedTerm A B Γ 2 u s k) - descendedTerm A B Γ 2 u s 0 := by
    rw [tsum_congr (descendedTerm_shift A B Γ 2 u s)]
    linear_combination -heq
  dsimp only [actualPreparedCoordinate, Kneser.coordinateSeries]
  rw [hshift]
  linear_combination hdefect

/-- Positive-real logarithmic factors hold in a neighborhood of the merger.
This condition is derived from the actual analytic cofactor. -/
theorem eventually_log_ratio_re_pos (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 0,
      0 < (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2).re ∧
      0 < (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2).re := by
  have hK : ContinuousAt (fun p : ℂ × ℂ => symmetricCofactor U p.1 p.2) 0 :=
    (analyticAt_symmetricCofactor hU analyticAt_fst rfl analyticAt_snd).continuousAt
  have hUn : ContinuousAt (fun p : ℂ × ℂ => U (-p.1)) 0 :=
    hU.continuousAt.comp_of_eq continuous_fst.continuousAt.neg (by simp)
  have hUp : ContinuousAt (fun p : ℂ × ℂ => U p.1) 0 :=
    hU.continuousAt.comp_of_eq continuous_fst.continuousAt rfl
  have h₁c : ContinuousAt
      (fun p : ℂ × ℂ => 1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) 0 :=
    continuousAt_const.add ((continuous_snd.continuousAt.sub hUn).mul hK)
  have h₂c : ContinuousAt
      (fun p : ℂ × ℂ => 1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) 0 :=
    continuousAt_const.add ((continuous_snd.continuousAt.sub hUp).mul hK)
  have h₁ := Complex.continuous_re.continuousAt.comp h₁c
  have h₂ := Complex.continuous_re.continuousAt.comp h₂c
  have hb₁ : (0 : ℝ) < (1 + ((0 : ℂ) - U (-(0 : ℂ))) * symmetricCofactor U 0 0).re := by
    simp [hU0]
  have hb₂ : (0 : ℝ) < (1 + ((0 : ℂ) - U 0) * symmetricCofactor U 0 0).re := by
    simp [hU0]
  exact (h₁.eventually (lt_mem_nhds hb₁)).and (h₂.eventually (lt_mem_nhds hb₂))

/-- The actual prepared one-step identity holds locally at each sufficiently
small attracting point. No logarithmic branch inequalities are inputs. -/
theorem exists_local_model_defect (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hprepared : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
        rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p)
    (hresidue : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
      Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U p.1) +
      Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U (-p.1)) - 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ u₀ : ℂ, ‖u₀‖ < η → u₀.re < 0 →
      ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ u ∈ ball u₀ ρ,
          preparedModelTime U H e₁ e₂ s (unfolding s u) -
            preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0 := by
  have hHnear := hH.continuousAt.eventually_ne hHne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 0) (𝓝 (0 : ℂ)) :=
    continuous_fst.tendsto 0
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    (hprepared.and (hresidue.and ((eventually_log_ratio_re_pos U hU hU0).and
      ((hfst.eventually hHnear).and ((hfst.eventually (hneg.eventually hHnear)).and
        (hfst.eventually hcofactor))))))
  refine ⟨δ / 2, by positivity, ?_⟩
  intro u₀ hu₀ hneg₀
  have hUp : ContinuousAt (fun p : ℂ × ℂ => U p.1 - p.2) (0, u₀) :=
    (hU.continuousAt.comp_of_eq continuous_fst.continuousAt rfl).sub continuous_snd.continuousAt
  have hUn : ContinuousAt (fun p : ℂ × ℂ => U (-p.1) - p.2) (0, u₀) :=
    (hU.continuousAt.comp_of_eq continuous_fst.continuousAt.neg (by simp)).sub
      continuous_snd.continuousAt
  have hpos : 0 < (U 0 - u₀).re := by simpa [hU0] using neg_pos.mpr hneg₀
  have hposn : 0 < (U (-(0 : ℂ)) - u₀).re := by simpa using hpos
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp
    (((Complex.continuous_re.continuousAt.comp hUp).eventually (lt_mem_nhds hpos)).and
      ((Complex.continuous_re.continuousAt.comp hUn).eventually (lt_mem_nhds hposn)))
  let r : ℝ := min (δ / 2) (ε / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨r, r ^ 2, hr, by positivity, ?_⟩
  intro s hs hss u hu
  have hxsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hxr : ‖Complex.sqrt (s : ℂ)‖ < r := by nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hur : ‖u - u₀‖ < r := by simpa only [mem_ball, dist_eq_norm] using hu
  have hpδ : dist (Complex.sqrt (s : ℂ), u) (0 : ℂ × ℂ) < δ := by
    rw [dist_zero_right, Prod.norm_def]
    refine max_lt ?_ ?_
    · have h := hxr.trans_le (min_le_left (δ / 2) (ε / 2))
      linarith
    · have hnorm : ‖u‖ ≤ ‖u - u₀‖ + ‖u₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (u - u₀) u₀
      have hurδ := hur.trans_le (min_le_left (δ / 2) (ε / 2))
      linarith
  have hpε : dist (Complex.sqrt (s : ℂ), u) (0, u₀) < ε := by
    simp only [dist_eq_norm, Prod.fst_sub, Prod.snd_sub, Prod.norm_def, sub_zero]
    exact max_lt (by have h := hxr.trans_le (min_le_right (δ / 2) (ε / 2)); linarith)
      (by have h := hur.trans_le (min_le_right (δ / 2) (ε / 2)); linarith)
  obtain ⟨hprep, hres, hratios, hHx, hHnx, hcf⟩ := hδball hpδ
  obtain ⟨ha, hb⟩ := hεball hpε
  have hx : Complex.sqrt (s : ℂ) ≠ 0 := by
    intro heq
    rw [heq] at hxsq
    simp at hxsq
    linarith
  have hstep := preparedModelTime_one_step U H e₁ e₂ hHlog
    (Complex.sqrt (s : ℂ)) u (F (Complex.sqrt (s : ℂ), u)) hx hHx hHnx
    (hcf u) (hres hx) ha hb hratios.1 hratios.2
  rw [AnalyticEvenDescent.square_sqrt] at hstep hprep
  rw [hprep] at hstep
  simpa only [descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt, orbit_zero] using hstep

/-- On a neighborhood of every point sufficiently deep in the attracting
petal, the actual series is absolutely convergent and satisfies Abel's
equation for all sufficiently small positive parameters. The preparation,
cofactor, and residue hypotheses are the constructed germ identities. -/
theorem exists_local_prepared_abel (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (hΓ : ContinuousAt Γ 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hprepared : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
        rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p)
    (hresidue : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
      Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U p.1) +
      Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U (-p.1)) - 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u₀ : ℂ, R₀ + 2 ≤ (inverseCoordinate u₀).re →
      ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ u ∈ ball u₀ ρ,
          Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) ∧
          Summable (fun k => ‖descendedTerm A B Γ 2 (unfolding s u) s k‖) ∧
          (preparedModelTime U H e₁ e₂ s (unfolding s u) -
            preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0) ∧
          actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s u) s =
            actualPreparedCoordinate U H e₁ e₂ A B Γ u s + 1 := by
  obtain ⟨η, hη, hlocal⟩ := exists_local_model_defect U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog hcofactor hprepared hresidue
  obtain ⟨R₁, C, hR₁, _hC, hmajorant⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) 2 hK hK0 hfactor (continuousAt_descendedFactor Γ hΓ)
  let R₀ : ℝ := max R₁ (4 / η)
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro u₀ hu₀
  have hre : 0 < (inverseCoordinate u₀).re := by linarith
  have hu₀small : ‖u₀‖ < η := by
    apply (norm_le_two_div_re u₀ hre).trans_lt
    apply (div_lt_iff₀ hre).mpr
    have hRη : 4 ≤ R₀ * η := (div_le_iff₀ hη).mp (le_max_right R₁ (4 / η))
    nlinarith
  have hu₀neg : u₀.re < 0 := by
    have h := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hre
    simpa only [Complex.neg_re, neg_pos] using h
  obtain ⟨ρ₁, s₁, hρ₁, hs₁, hmodel⟩ := hlocal u₀ hu₀small hu₀neg
  have hu₀ne : u₀ ≠ 0 := by
    intro heq
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hre
    linarith
  have hi : ContinuousAt inverseCoordinate u₀ := continuousAt_const.div continuousAt_id hu₀ne
  let Z : ℝ := ‖inverseCoordinate u₀‖ + 1
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hpetal : ∀ᶠ u : ℂ in 𝓝 u₀,
      R₀ + 1 < (inverseCoordinate u).re ∧ ‖inverseCoordinate u‖ < Z :=
    ((Complex.continuous_re.continuousAt.comp hi).eventually
      (lt_mem_nhds (by linarith : R₀ + 1 < (inverseCoordinate u₀).re))).and
      (hi.norm.eventually (gt_mem_nhds (by dsimp [Z]; linarith)))
  obtain ⟨ρ₂, hρ₂, hρ₂ball⟩ := Metric.eventually_nhds_iff.mp hpetal
  obtain ⟨s₂, hs₂, hbounds⟩ := hmajorant R₀ (le_max_left _ _) Z hZ
  refine ⟨min ρ₁ ρ₂, min s₁ s₂, lt_min hρ₁ hρ₂, lt_min hs₁ hs₂, ?_⟩
  intro s hs hss u hu
  have hu₁ : u ∈ ball u₀ ρ₁ := ball_subset_ball (min_le_left _ _) hu
  have hu₂ : dist u u₀ < ρ₂ := (hu.trans_le (min_le_right _ _) : dist u u₀ < ρ₂)
  obtain ⟨huRe, huZ⟩ := hρ₂ball hu₂
  have hsum : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) :=
    Kneser.summable_norm_of_parabolic_bound _ C (q := 4) (by norm_num) (by
      intro k
      simpa only [descendedTerm_eq] using
        hbounds s hs (hss.trans_le (min_le_right _ _)) u huRe.le huZ.le k)
  have hd := hmodel s hs (hss.trans_le (min_le_left _ _)) u hu₁
  exact ⟨hsum, summable_descendedTerm_shift A B Γ 2 u s hsum, hd,
    actualPreparedCoordinate_abel U H e₁ e₂ A B Γ u s hd hsum⟩

/-- A nonzero constructed root derivative supplies the distinct-root germ
needed for the symmetric cofactor identity. -/
theorem eventually_distinct_roots (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0)
    (hUd : deriv U 0 ≠ 0) :
    ∀ᶠ x in 𝓝 (0 : ℂ), U x = U (-x) ↔ x = 0 := by
  obtain ⟨G, hGa, hG0, hG⟩ := exists_odd_difference_factor hU
  have hGne : G 0 ≠ 0 := by rw [hG0]; exact mul_ne_zero (by norm_num) hUd
  filter_upwards [hGa.continuousAt.eventually_ne hGne] with x hx
  constructor
  · intro hEq
    have hzero : x * G x = 0 := by rw [← hG x, hEq, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right hx
  · rintro rfl
    simp

/-- All germs and all branch and convergence data in the local Abel theorem
are constructed for the actual exponential family. -/
theorem exists_actual_local_prepared_abel :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧
      AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
        unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u₀ : ℂ, R₀ + 2 ≤ (inverseCoordinate u₀).re →
        ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
          ∀ u ∈ ball u₀ ρ,
            Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) ∧
            Summable (fun k => ‖descendedTerm A B Γ 2 (unfolding s u) s k‖) ∧
            (preparedModelTime U H e₁ e₂ s (unfolding s u) -
              preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0) ∧
            actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s u) s =
              actualPreparedCoordinate U H e₁ e₂ A B Γ u s + 1 := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
      he₁, he₂, hF, hΓ, hK0, hK, _hFeven, hΓeven, hfactor, hprepared, hresidue,
      hq, hroots⟩ := exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u :=
    eventually_symmetricCofactor_factor hU hroots (eventually_distinct_roots U hU hUd)
  have hlocal := exists_local_prepared_abel U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog
    hΓ.continuousAt hK (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, hlocal⟩

end Kneser.PreparedLocalAbel

end
