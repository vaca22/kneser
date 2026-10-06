import Kneser.PreparedLocalAbel
import Kneser.ReflectedPreparedModel

/-!
# Local Abel equation for the actual reflected inverse coordinate

The logarithmic branch conditions are derived at the actual inverse image.
The shifted prepared series then satisfies Abel by an exact inverse-orbit
shift, with absolute convergence at the image supplied by the same series.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ReflectedLocalAbel

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialModelTime
open Kneser.ReflectedEvenOrbitDiscs Kneser.ReflectedPreparedFirstOrder
open Kneser.RepellingExponentialOrbit
open Kneser.ParabolicExponentialOrbit (inverseCoordinate)
open scoped Topology BigOperators

/-- A reflected inverse starting at its first image is the shifted true orbit. -/
theorem inverseOrbit_shift (v s : ℂ) (k : ℕ) :
    inverseOrbit (reflectedInverse s v) s k = inverseOrbit v s (k + 1) := by
  simp only [inverseOrbit, Function.iterate_succ_apply]

theorem shiftedTerm_shift (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (v s : ℂ) (k : ℕ) :
    shiftedTerm A B Γ N (reflectedInverse s v) s k = shiftedTerm A B Γ N v s (k + 1) := by
  simp only [shiftedTerm, descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt,
    inverseOrbit_shift]

theorem summable_shiftedTerm_shift (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (v s : ℂ) (hs : Summable (fun k => ‖shiftedTerm A B Γ N v s k‖)) :
    Summable (fun k => ‖shiftedTerm A B Γ N (reflectedInverse s v) s k‖) := by
  exact ((summable_nat_add_iff 1).mpr hs).congr
    (fun k => (congrArg norm (shiftedTerm_shift A B Γ N v s k)).symm)

/-- Abel's equation for the actual reflected model plus its convergent
shifted correction, with the original residual at the inverse image. -/
theorem actualInversePreparedCoordinate_abel (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (v : ℂ) (s : ℝ)
    (hdefect : preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
      preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1 = shiftedTerm A B Γ 2 v s 0)
    (hs : Summable (fun k => ‖shiftedTerm A B Γ 2 v s k‖)) :
    actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s v) s =
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s + 1 := by
  have heq := hs.of_norm.tsum_eq_zero_add
  have hshift : (∑' k : ℕ, shiftedTerm A B Γ 2 (reflectedInverse s v) s k) =
      (∑' k : ℕ, shiftedTerm A B Γ 2 v s k) - shiftedTerm A B Γ 2 v s 0 := by
    rw [tsum_congr (shiftedTerm_shift A B Γ 2 v s)]
    linear_combination -heq
  dsimp only [actualInversePreparedCoordinate, Kneser.coordinateSeries]
  rw [hshift]
  linear_combination hdefect

/-- The true parabolic reflected inverse preserves the negative real half-plane. -/
theorem parabolicInverse_re_neg (v : ℂ) (hv : v.re < 0) : (parabolicInverse v).re < 0 := by
  have hre : (1 : ℝ) < ((1 : ℂ) - v).re := by simp; linarith
  have hn : (1 : ℝ) < ‖(1 : ℂ) - v‖ := hre.trans_le (Complex.re_le_norm _)
  simp only [parabolicInverse, Complex.neg_re, Complex.log_re, neg_lt_zero]
  exact Real.log_pos hn

/-- Joint analyticity of the explicit inverse at each reflected attracting point. -/
theorem analyticAt_inverse_pair (v : ℂ) (hv : v.re < 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => reflectedInverse (p.1 ^ 2) p.2) (0, v) := by
  have hslit : (1 : ℂ) - v ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hsq : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ 2) (0, v) := analyticAt_fst.pow 2
  exact (((analyticAt_const.sub analyticAt_snd).clog hslit).add hsq).neg.div
    (analyticAt_const.sub hsq) (by simp)

/-- The joint inverse germ at the merger is actual analytic, including its
principal logarithm, rather than an abstract inverse function. -/
theorem analyticAt_inverse_pair_zero :
    AnalyticAt ℂ (fun p : ℂ × ℂ => reflectedInverse (p.1 ^ 2) p.2) 0 := by
  have hsq : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ 2) 0 := analyticAt_fst.pow 2
  exact (((analyticAt_const.sub analyticAt_snd).clog (by simp)).add hsq).neg.div
    (analyticAt_const.sub hsq) (by simp)

/-- The reflected model's one-step residual is the original prepared
residual at the inverse image. Branch inequalities are conclusions. -/
theorem exists_local_inverse_model_defect (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
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
    ∃ η : ℝ, 0 < η ∧ ∀ v₀ : ℂ, ‖v₀‖ < η → v₀.re < 0 →
      ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ v ∈ ball v₀ ρ,
          preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
            preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1 = shiftedTerm A B Γ 2 v s 0 := by
  let Q : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, -reflectedInverse (p.1 ^ 2) p.2)
  have hQt : Tendsto Q (𝓝 0) (𝓝 0) := by
    have h := continuous_fst.continuousAt.prodMk analyticAt_inverse_pair_zero.continuousAt.neg
    have hQ0 : Q 0 = 0 := by ext <;> simp [Q, reflectedInverse]
    simpa only [hQ0] using (show Tendsto Q (𝓝 0) (𝓝 (Q 0)) from h.tendsto)
  have hHnear := hH.continuousAt.eventually_ne hHne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  have hvnear : ∀ᶠ p : ℂ × ℂ in 𝓝 0, ‖p.2‖ < 1 :=
    continuous_snd.continuousAt.norm.eventually (gt_mem_nhds (by simp))
  have hsnear : ∀ᶠ p : ℂ × ℂ in 𝓝 0, p.1 ^ 2 ≠ (1 : ℂ) :=
    (continuous_fst.continuousAt.pow 2).eventually_ne (by simp)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    ((hQt.eventually hprepared).and ((hQt.eventually hresidue).and
      ((hQt.eventually (Kneser.PreparedLocalAbel.eventually_log_ratio_re_pos U hU hU0)).and
        ((hfst.eventually hHnear).and ((hfst.eventually (hneg.eventually hHnear)).and
          ((hfst.eventually hcofactor).and (hvnear.and hsnear)))))))
  refine ⟨δ / 2, by positivity, ?_⟩
  intro v₀ hv₀ hv₀neg
  have hGa := (analyticAt_inverse_pair v₀ hv₀neg).continuousAt
  have hUp : ContinuousAt (fun p : ℂ × ℂ => -U p.1 - reflectedInverse (p.1 ^ 2) p.2) (0, v₀) :=
    (hU.continuousAt.comp_of_eq continuous_fst.continuousAt rfl).neg.sub hGa
  have hUn : ContinuousAt (fun p : ℂ × ℂ => -U (-p.1) - reflectedInverse (p.1 ^ 2) p.2) (0, v₀) :=
    (hU.continuousAt.comp_of_eq continuous_fst.continuousAt.neg (by simp)).neg.sub hGa
  have hpos : 0 < (-U 0 - reflectedInverse ((0 : ℂ) ^ 2) v₀).re := by
    simpa [hU0] using neg_pos.mpr (parabolicInverse_re_neg v₀ hv₀neg)
  have hposn : 0 < (-U (-(0 : ℂ)) - reflectedInverse ((0 : ℂ) ^ 2) v₀).re := by simpa using hpos
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp
    (((Complex.continuous_re.continuousAt.comp hUp).eventually (lt_mem_nhds hpos)).and
      ((Complex.continuous_re.continuousAt.comp hUn).eventually (lt_mem_nhds hposn)))
  let r : ℝ := min (δ / 2) (ε / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨r, r ^ 2, hr, by positivity, ?_⟩
  intro s hs hss v hv
  have hxsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hxr : ‖Complex.sqrt (s : ℂ)‖ < r := by nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hvr : ‖v - v₀‖ < r := by simpa only [mem_ball, dist_eq_norm] using hv
  have hpδ : dist (Complex.sqrt (s : ℂ), v) (0 : ℂ × ℂ) < δ := by
    rw [dist_zero_right, Prod.norm_def]
    refine max_lt ?_ ?_
    · have h := hxr.trans_le (min_le_left (δ / 2) (ε / 2)); linarith
    · have hnorm : ‖v‖ ≤ ‖v - v₀‖ + ‖v₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (v - v₀) v₀
      have hvrδ := hvr.trans_le (min_le_left (δ / 2) (ε / 2))
      linarith
  have hpε : dist (Complex.sqrt (s : ℂ), v) (0, v₀) < ε := by
    simp only [dist_eq_norm, Prod.fst_sub, Prod.snd_sub, Prod.norm_def, sub_zero]
    exact max_lt (by have h := hxr.trans_le (min_le_right (δ / 2) (ε / 2)); linarith)
      (by have h := hvr.trans_le (min_le_right (δ / 2) (ε / 2)); linarith)
  obtain ⟨hprep, hres, hratios, hHx, hHnx, hcf, hvnorm, hsne⟩ := hδball hpδ
  dsimp only [Q] at hprep hres hratios
  obtain ⟨ha, hb⟩ := hεball hpε
  have hx : Complex.sqrt (s : ℂ) ≠ 0 := by
    intro heq
    rw [heq] at hxsq
    simp at hxsq
    linarith
  have hstep := Kneser.ReflectedPreparedModel.reflected_preparedModelTime_one_step
    U H e₁ e₂ hHlog (Complex.sqrt (s : ℂ)) v
    (F (Complex.sqrt (s : ℂ), -reflectedInverse ((Complex.sqrt (s : ℂ)) ^ 2) v))
    hx hHx hHnx hsne hvnorm (by simpa only [sub_neg_eq_add] using hcf (-reflectedInverse ((Complex.sqrt (s : ℂ)) ^ 2) v))
    (hres hx) ha hb hratios.1 hratios.2
  rw [AnalyticEvenDescent.square_sqrt] at hstep hprep hsne
  have hinv := unfolding_reflectedInverse (s : ℂ) v hsne hvnorm
  rw [hinv] at hprep
  rw [hprep] at hstep
  simpa only [shiftedTerm, descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt,
    inverseOrbit_succ, inverseOrbit_zero, zero_add] using hstep

/-- The actual reflected inverse series is locally absolutely convergent and
satisfies Abel's equation without branch or orbit-bound assumptions. -/
theorem exists_local_inverse_prepared_abel (U H e₁ e₂ A B : ℂ → ℂ)
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
          Summable (fun k => ‖shiftedTerm A B Γ 2 u s k‖) ∧
          Summable (fun k => ‖shiftedTerm A B Γ 2 (reflectedInverse s u) s k‖) ∧
          (preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s u) -
            preparedModelTime (-U) (-H) e₁ (-e₂) s u - 1 = shiftedTerm A B Γ 2 u s 0) ∧
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s u) s =
            actualInversePreparedCoordinate U H e₁ e₂ A B Γ u s + 1 := by
  obtain ⟨η, hη, hlocal⟩ := exists_local_inverse_model_defect U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog hcofactor hprepared hresidue
  obtain ⟨R₁, C, hR₁, _hC, hmajorant⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
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
  have hsum : Summable (fun k => ‖shiftedTerm A B Γ 2 u s k‖) := by
    have hraw : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) :=
      Kneser.summable_norm_of_parabolic_bound _ C (q := 4) (by norm_num) (by
        intro k
        simpa only [descendedTerm_eq] using
          hbounds s hs (hss.trans_le (min_le_right _ _)) u huRe.le huZ.le k)
    exact (summable_nat_add_iff 1).mpr hraw
  have hd := hmodel s hs (hss.trans_le (min_le_left _ _)) u hu₁
  exact ⟨hsum, summable_shiftedTerm_shift A B Γ 2 u s hsum, hd,
    actualInversePreparedCoordinate_abel U H e₁ e₂ A B Γ u s hd hsum⟩

/-- Actual constructed preparation witnesses, including the nonzero root
velocity, supply the reflected inverse local Abel equation. -/
theorem exists_actual_local_inverse_prepared_abel :
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
            Summable (fun k => ‖shiftedTerm A B Γ 2 u s k‖) ∧
            Summable (fun k => ‖shiftedTerm A B Γ 2 (reflectedInverse s u) s k‖) ∧
            (preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s u) -
              preparedModelTime (-U) (-H) e₁ (-e₂) s u - 1 = shiftedTerm A B Γ 2 u s 0) ∧
            actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s u) s =
              actualInversePreparedCoordinate U H e₁ e₂ A B Γ u s + 1 := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
      he₁, he₂, hF, hΓ, hK0, hK, _hFeven, hΓeven, hfactor, hprepared, hresidue,
      hq, hroots⟩ := exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u :=
    eventually_symmetricCofactor_factor hU hroots (Kneser.PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  have hlocal := exists_local_inverse_prepared_abel U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog
    hΓ.continuousAt hK (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, hlocal⟩

end Kneser.ReflectedLocalAbel

end
