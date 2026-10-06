import Kneser.PositiveKoenigsAbel
import Kneser.ActualPreparedRootMatching
import Kneser.ActualRootPolynomialOrbit

/-!
The actual preparation supplies the residue pair and true one-step model
identity on a common positive-parameter neighborhood. These identities are
then used to identify its orbit series with the actual Koenigs time.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Kneser.ActualKoenigsIdentification

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedModel Kneser.ExponentialModelTime
open Kneser.ExponentialMatrixDividedDifference Kneser.PreparedLocalAbel
open Kneser.EvenPreparedOrbitDiscs Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsAbel
open Kneser.ActualPreparedRootMatching Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder
open scoped Topology BigOperators

theorem rootMultiplier_of_real_value (U : ℂ → ℂ) (s a : ℝ) (x : ℂ)
    (hx : x ^ 2 = (s : ℂ)) (hUx : U x = (a : ℂ)) :
    rootMultiplier U x = (multiplier s a : ℂ) := by
  simp only [rootMultiplier, hx, hUx, multiplier]
  push_cast
  rfl

theorem preparedModelTime_pair_of_matching (U H e₁ e₂ : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (s a b : ℝ) (x : ℂ) (hs1 : s < 1) (ha : -1 < a) (hb : 0 < b)
    (hx : x ^ 2 = (s : ℂ)) (hxne : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hmatch : (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
      (U x = (b : ℂ) ∧ U (-x) = (a : ℂ))) (v : ℂ) :
    preparedModelTime U H e₁ e₂ s v = pairedModel s a b (e₁ s) (e₂ s) v := by
  have hμa : 0 < multiplier s a := by
    dsimp [multiplier]
    exact mul_pos (by linarith) (by linarith)
  have hμb : 0 < multiplier s b := by
    dsimp [multiplier]
    exact mul_pos (by linarith) (by linarith)
  have hp := preparedModelTime_residue_pair U H e₁ e₂ hHlog x v hxne hHx hHnx
  rw [hx] at hp
  rcases hmatch with hmatch | hmatch
  · rw [rootMultiplier_of_real_value U s a x hx hmatch.1,
      rootMultiplier_of_real_value U s b (-x) (by simpa only [neg_sq] using hx) hmatch.2,
      ← Complex.ofReal_log hμa.le, ← Complex.ofReal_log hμb.le, hmatch.1, hmatch.2] at hp
    exact hp.trans (by dsimp [pairedModel, polynomialCorrection]; ring)
  · rw [rootMultiplier_of_real_value U s b x hx hmatch.1,
      rootMultiplier_of_real_value U s a (-x) (by simpa only [neg_sq] using hx) hmatch.2,
      ← Complex.ofReal_log hμb.le, ← Complex.ofReal_log hμa.le, hmatch.1, hmatch.2] at hp
    exact hp.trans (by dsimp [pairedModel, polynomialCorrection]; ring)

/-- All local model identities are derived from the actual preparation.
The only spatial condition is the left side of the actual attracting root. -/
theorem exists_actual_model_neighborhood
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0 < η ∧ 0 < s₀ ∧ η ≤ 1 / 4 ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        (∀ v : ℂ, preparedModelTime U H e₁ e₂ s v = pairedModel s a b (e₁ s) (e₂ s) v) ∧
        ∀ v : ℂ, ‖v‖ < η → v.re < a →
          preparedModelTime U H e₁ e₂ s (unfolding s v) - preparedModelTime U H e₁ e₂ s v - 1 =
            descendedTerm A B Γ 2 v s 0 := by
  obtain ⟨ηm, sm, hηm, hsm, hmatch⟩ := exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, _hA, _hB, _hA0, _hB0, _he₁, _he₂,
    _hF, _hΓ, _hEven, _hK0, _hK, _hq, hroots, _hfactor, hprepared, hresidue⟩
  have hcofactor := eventually_symmetricCofactor_factor hU hroots (eventually_distinct_roots U hU hUd)
  have hHnear := hH.continuousAt.eventually_ne hHne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    (hprepared.and (hresidue.and ((eventually_log_ratio_re_pos U hU hU0).and
      ((hfst.eventually hHnear).and ((hfst.eventually (hneg.eventually hHnear)).and
        (hfst.eventually hcofactor))))))
  let η := min ηm (min (δ / 4) (1 / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηm' : η ≤ ηm := min_le_left _ _
  have hηδ : η ≤ δ / 4 := (min_le_left _ _).trans' (min_le_right _ _)
  have hηq : η ≤ 1 / 4 := (min_le_right _ _).trans' (min_le_right _ _)
  refine ⟨η, min sm (min (η ^ 2) (1 / 2)), hη, by positivity, hηq, ?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb
  have hsm' : s < sm := hss.trans_le (min_le_left _ _)
  have hsη : s < η ^ 2 := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hshalf : s < 1 / 2 := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let x := Complex.sqrt (s : ℂ)
  have hx : x ^ 2 = (s : ℂ) := Kneser.AnalyticEvenDescent.square_sqrt _
  have hxne : x ≠ 0 := by
    intro he
    have hz := hx
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hz
    exact (by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0) hz.symm
  have hxsq : ‖x‖ ^ 2 = s := by
    rw [← norm_pow, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hxn : ‖x‖ < η := by nlinarith [norm_nonneg x]
  have hp (v : ℂ) (hv : ‖v‖ < η) : dist (x, v) (0 : ℂ × ℂ) < δ := by
    rw [dist_zero_right, Prod.norm_def]
    exact max_lt (by linarith) (by linarith)
  have hzero := hδball (hp 0 (by simpa only [norm_zero] using hη))
  have hm := hmatch s a b hs hsm' (ha.trans_le hηm') (hb.trans_le hηm')
    (by linarith) hfa hfb x hx
  have hHa : H x ≠ 0 := hzero.2.2.2.1
  have hHb : H (-x) ≠ 0 := hzero.2.2.2.2.1
  have haa : -1 < a := by have hh := (abs_lt.mp ha).1; linarith
  refine ⟨preparedModelTime_pair_of_matching U H e₁ e₂ hHlog s a b x (by linarith) haa hb0 hx hxne hHa hHb hm, ?_⟩
  intro v hv hva
  have hd := hδball (hp v hv)
  have hapos : 0 < (U x - v).re := by
    rcases hm with hm | hm <;> rw [hm.1] <;> simp only [Complex.sub_re, Complex.ofReal_re] <;> linarith
  have hbpos : 0 < (U (-x) - v).re := by
    rcases hm with hm | hm <;> rw [hm.2] <;> simp only [Complex.sub_re, Complex.ofReal_re] <;> linarith
  have hstep := preparedModelTime_one_step U H e₁ e₂ hHlog x v (F (x, v))
    hxne hd.2.2.2.1 hd.2.2.2.2.1 (hd.2.2.2.2.2 v) (hd.2.1 hxne)
      hapos hbpos hd.2.2.1.1 hd.2.2.1.2
  have hprep := hd.1
  dsimp only at hprep
  rw [hx] at hprep
  rw [hx, hprep] at hstep
  simpa only [descendedTerm, splitTerm, orbit_zero, x, Kneser.AnalyticEvenDescent.square_sqrt] using hstep

/-- The actual preparation is the Koenigs Abel time, with an explicit
additive constant, throughout the genuine positive-parameter attracting
Apollonius petal. Every orbit limit and every summability assertion in this
statement is derived from the actual exponential map. -/
theorem exists_actual_prepared_koenigs_identification (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ (Q : Kneser.RealExponentialPetal.QuotientControl) (R₀ s₀ : ℝ),
      0 < R₀ ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b : ℝ,
        -1 < a ∧ a < 0 ∧ 0 < b ∧
        unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
        0 < multiplier s a ∧ multiplier s a < 1 ∧
        ∀ R : ℝ, R₀ ≤ R → ∀ u : ℂ, u.re < a →
          ‖Kneser.ApolloniusGeometry.crossRatio a b u‖ ≤
            Real.exp (-(Kneser.RealExponentialPetal.timeScale Q ((1 - s) * (b - a)) * R)) →
          Summable (fun n => ‖increment s a u n‖) ∧
          Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)) ∧
          Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) ∧
          koenigsValue s a u ≠ 0 ∧
          Summable (fun n => ‖descendedTerm A B Γ 2 u s n‖) ∧
          koenigsTime s a (unfolding s u) = koenigsTime s a u + 1 ∧
          actualPreparedCoordinate U H e₁ e₂ A B Γ u s =
            koenigsTime s a u + modelConstant s a b (e₁ s) (e₂ s) := by
  obtain ⟨Q⟩ := Kneser.RealExponentialPetal.exists_quotientControl
  obtain ⟨ηm, sm, hηm, hsm, hηmq, hmodel⟩ :=
    exists_actual_model_neighborhood U H e₁ e₂ A B K F Γ hdata
  obtain ⟨ηr, sr, hηr, hsr, hmatch⟩ :=
    exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  have hd := hdata
  rcases hd with ⟨_hU, _hU0, _hUd, _hH, _hHne, _hHlog, _hA, _hB, _hA0, _hB0,
    _he₁, _he₂, _hF, hΓ, _hEven, _hK0, _hK, hqpoly, _hroots, _hfactor, _hprep, _hres⟩
  obtain ⟨δ, hδ, hΓbound⟩ := Metric.eventually_nhds_iff.mp
    (hΓ.continuousAt.norm.eventually (gt_mem_nhds (show ‖Γ 0‖ < ‖Γ 0‖ + 1 by linarith)))
  let η := min ηm (min ηr (δ / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηm' : η ≤ ηm := min_le_left _ _
  have hηr' : η ≤ ηr := (min_le_left _ _).trans' (min_le_right _ _)
  have hηδ : η ≤ δ / 4 := (min_le_right _ _).trans' (min_le_right _ _)
  have hηq : η ≤ 1 / 4 := hηm'.trans hηmq
  let δroot := min (η / 4) (Q.radius / 32)
  have hδroot : 0 < δroot := by dsimp [δroot]; exact lt_min (by positivity) (by linarith [Q.radius_pos])
  obtain ⟨st, hst, hsthalf, hroots⟩ :=
    Kneser.RealExponentialRoots.exists_ordered_small_real_roots δroot hδroot
  let R₀ := max (80 / Q.radius) (max 5 (20 / η))
  let s₀ := min st (min sm (min sr ((η / 4) ^ 2)))
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  refine ⟨Q, R₀, s₀, (by dsimp [R₀]; positivity), hs₀,
    (min_le_left _ _).trans hsthalf, ?_⟩
  intro s hs hss
  have hst' : s < st := hss.trans_le (min_le_left _ _)
  have hsm' : s < sm := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsr' : s < sr := hss.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsη : s < (η / 4) ^ 2 := hss.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hshalf : s < 1 / 2 := hst'.trans_le hsthalf
  obtain ⟨a, b, har, ha, hb, hbr, hfa, hfb⟩ := hroots s hs hst'
  have haη : |a| < η / 4 := by
    rw [abs_of_neg ha]
    have hh := min_le_left (η / 4) (Q.radius / 32)
    change δroot ≤ η / 4 at hh
    linarith
  have hbη : |b| < η / 4 := by
    rw [abs_of_pos hb]
    exact hbr.trans_le (min_le_left _ _)
  have haa : -1 < a := by have hh := (abs_lt.mp (haη.trans (by linarith : η / 4 < 1))).1; linarith
  have hab : a < b := by linarith
  have hgap : b - a < Q.radius / 8 := by
    have hh := min_le_right (η / 4) (Q.radius / 32)
    change δroot ≤ Q.radius / 32 at hh
    linarith [Q.radius_pos]
  have hμ : 0 < multiplier s a := by dsimp [multiplier]; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by
    dsimp [multiplier]
    nlinarith
  have hpair := hmodel s a b hs hsm' (haη.trans_le (by linarith))
    (hbη.trans_le (by linarith)) ha hb hfa hfb
  let x := Complex.sqrt (s : ℂ)
  have hx : x ^ 2 = (s : ℂ) := Kneser.AnalyticEvenDescent.square_sqrt _
  have hxsq : ‖x‖ ^ 2 = s := by
    rw [← norm_pow, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hxn : ‖x‖ < η / 4 := by nlinarith [norm_nonneg x]
  have hm := hmatch s a b hs hsr' (haη.trans_le (by linarith))
    (hbη.trans_le (by linarith)) hab hfa hfb x hx
  have hpoly (v : ℂ) : rootPolynomial A B s v = (v - (a : ℂ)) * (v - (b : ℂ)) := by
    rw [← hx, hqpoly]
    rcases hm with hm | hm
    · rw [hm.1, hm.2]
    · rw [hm.1, hm.2, mul_comm]
  refine ⟨a, b, haa, ha, hb, hfa, hfb, hμ, hμ1, ?_⟩
  intro R hR u hua hcross
  have hRQ : 80 / Q.radius ≤ R := (le_max_left _ _).trans hR
  have hR5 : 5 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRη : 20 / η ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRpos : 0 < R := by linarith
  have hub : u ≠ (b : ℂ) := by intro he; simp only [he, Complex.ofReal_re] at hua; linarith
  obtain ⟨D, r, _hD, _hD1, _hr, _hr1, _hrμ, _horbit, hlim, hsum, happrox⟩ :=
    actual_koenigs_limit Q s a b R u hs hshalf haa ha hb hfa hfb hgap hRQ hR5 hub hcross
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hh := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) (sub_pos.mpr hab).le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := Kneser.RealExponentialPetal.timeScale_pos_and_gap_bound
    Q s a b hs hshalf hab hκr
  have hleft := orbit_left_of_root s a u (by linarith) hfa hua
  have hnorm (n : ℕ) : ‖orbit u s n‖ < η / 2 := by
    obtain ⟨hne, hqn⟩ := Kneser.RealExponentialPetal.infinite_orbit_crossRatio_bound
      Q s a b R u hs hshalf hab hb hfa hfb hgap hRQ hub hcross n
    have hxR : 0 < R + (3 / 4) * (n : ℝ) := by positivity
    have hd := Kneser.ApolloniusGeometry.attracting_root_distance_bound (a : ℂ) b
      (orbit u s n) (Kneser.RealExponentialPetal.timeScale Q ((1 - s) * (b - a)) *
        (R + (3 / 4) * (n : ℝ))) (mul_pos hθ hxR) hne hqn
    rw [← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_pos.mpr hab).le] at hd
    have hd5 : ‖orbit u s n - (a : ℂ)‖ ≤ 5 / R := by
      apply hd.trans
      calc
        (b - a) / (_ * (R + (3 / 4) * (n : ℝ))) =
            ((b - a) / Kneser.RealExponentialPetal.timeScale Q ((1 - s) * (b - a))) /
              (R + (3 / 4) * (n : ℝ)) := by rw [div_mul_eq_div_div]
        _ ≤ 5 / (R + (3 / 4) * (n : ℝ)) := div_le_div_of_nonneg_right hratio hxR.le
        _ ≤ 5 / R := div_le_div_of_nonneg_left (by norm_num) hRpos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have h5 : 5 / R ≤ η / 4 := by
      apply (div_le_iff₀ hRpos).mpr
      have hh := (div_le_iff₀ hη).mp hRη
      nlinarith
    have ht := norm_add_le (orbit u s n - (a : ℂ)) (a : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at ht
    linarith
  have hterms (n : ℕ) : ‖descendedTerm A B Γ 2 u s n‖ ≤
      (‖Γ 0‖ + 1) * 400 ^ 2 / ((n : ℝ) + 1) ^ 4 := by
    have hΓn : ‖Γ (x, orbit u s n)‖ ≤ ‖Γ 0‖ + 1 := by
      apply (hΓbound ?_).le
      rw [dist_zero_right, Prod.norm_def]
      exact max_lt (by linarith) (by linarith [hnorm n])
    have hp := Kneser.RealExponentialPetal.infinite_orbit_root_product_bound
      Q s a b R u hs hshalf hab hb hfa hfb hgap hRQ hub hcross n
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hden : 0 < R + (3 / 4) * (n : ℝ) := by positivity
    have hlo : ((n : ℝ) + 1) / 2 ≤ R + (3 / 4) * (n : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hp4 : ‖rootPolynomial A B s (orbit u s n)‖ ≤ 400 / ((n : ℝ) + 1) ^ 2 := by
      rw [hpoly, norm_mul]
      apply hp.trans
      calc
        100 / (R + (3 / 4) * (n : ℝ)) ^ 2 ≤ 100 / (((n : ℝ) + 1) / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_left₀ (by positivity) hlo 2)
        _ = _ := by field_simp; ring
    simp only [descendedTerm, splitTerm, Kneser.AnalyticEvenDescent.square_sqrt]
    change ‖rootPolynomial A B s (orbit u s n) ^ 2 * Γ (x, orbit u s n)‖ ≤ _
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (400 / ((n : ℝ) + 1) ^ 2) ^ 2 * (‖Γ 0‖ + 1) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp4 2) hΓn
          (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hsump := Kneser.summable_norm_of_parabolic_bound (fun n => descendedTerm A B Γ 2 u s n)
    ((‖Γ 0‖ + 1) * 400 ^ 2) (q := 4) (by norm_num) hterms
  have hdefect (n : ℕ) :
      preparedModelTime U H e₁ e₂ s (orbit u s (n + 1)) -
        preparedModelTime U H e₁ e₂ s (orbit u s n) - 1 = descendedTerm A B Γ 2 u s n := by
    have hh := hpair.2 (orbit u s n) ((hnorm n).trans_le (by linarith)) (hleft n)
    simpa only [orbit_succ, descendedTerm, splitTerm, orbit_zero,
      Kneser.AnalyticEvenDescent.square_sqrt] using hh
  obtain ⟨hKne, hKslit⟩ := actual_koenigs_branch s a u hs.le (by linarith) haa ha.le
    hfa hμ hμ1 hsum hlim hua
  exact ⟨hsum, hlim, happrox, hKne, hsump, koenigsTime_abel s a u hμ hμ1 hsum hKne,
    prepared_eq_koenigs_of_residue_pair U H e₁ e₂ A B Γ s a b u hμ hμ1 hab
      hlim happrox hKslit hpair.1 hdefect hsump⟩

end Kneser.ActualKoenigsIdentification

end
