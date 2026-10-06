import Kneser.PositiveKoenigsOrbit
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
The actual exponential has a normalized analytic Koenigs map at each
positive-parameter attracting root.  The map is the limit of its genuine
normalized iterates, and its normalization is proved by a quadratic estimate.
-/

noncomputable section

namespace Kneser.PositiveLocalKoenigs

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.RealExponentialRoots
open scoped Topology BigOperators

theorem exists_contraction_rate (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ r δ : ℝ, 0 < r ∧ r < 1 ∧ μ < r ∧ r ^ 2 < μ ∧
      0 < δ ∧ δ ≤ 1 ∧ μ + δ ≤ r := by
  let r := μ * (5 - μ) / 4
  let δ := (r - μ) / 2
  have hmr : μ < r := by dsimp [r]; nlinarith
  have hr : 0 < r := hμ.trans hmr
  have hr1 : r < 1 := by dsimp [r]; nlinarith [sq_nonneg (1 - μ)]
  have hrμ : r ^ 2 < μ := by
    have hp : 0 < (1 - μ) * (μ ^ 2 - 9 * μ + 16) :=
      mul_pos (by linarith) (by nlinarith [sq_nonneg μ])
    dsimp [r]
    nlinarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  exact ⟨r, δ, hr, hr1, hmr, hrμ, hδ, by dsimp [δ]; linarith, by dsimp [δ]; linarith⟩

theorem local_orbit_geometric (s a r δ : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hμδ : multiplier s a + δ ≤ r) (u : ℂ) (hu : u ∈ ball (a : ℂ) δ) :
    ∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ ‖u - (a : ℂ)‖ * r ^ n := by
  have hun : ‖u - (a : ℂ)‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hu
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ‖orbit u s n - (a : ℂ)‖ ≤ δ :=
      ih.trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) (norm_nonneg _)).trans
        (by simpa using hun.le))
    have hb := actual_quadratic_remainder s a (orbit u s n) hs hs1 ha ha0 hroot (hn.trans hδ1)
    rw [← orbit_succ] at hb
    have ht := norm_add_le
      (orbit u s (n + 1) - (a : ℂ) - (multiplier s a : ℂ) * (orbit u s n - (a : ℂ)))
      ((multiplier s a : ℂ) * (orbit u s n - (a : ℂ)))
    rw [sub_add_cancel, norm_mul, Complex.norm_of_nonneg hμ.le] at ht
    have hquad : ‖orbit u s n - (a : ℂ)‖ ^ 2 ≤ δ * ‖orbit u s n - (a : ℂ)‖ := by
      nlinarith [norm_nonneg (orbit u s n - (a : ℂ))]
    have hstep : ‖orbit u s (n + 1) - (a : ℂ)‖ ≤ r * ‖orbit u s n - (a : ℂ)‖ := by
      have hm := mul_le_mul_of_nonneg_right hμδ (norm_nonneg (orbit u s n - (a : ℂ)))
      linarith
    exact hstep.trans ((mul_le_mul_of_nonneg_left ih hr).trans (by rw [pow_succ]; ring_nf; rfl))

theorem approximation_at_root (s a : ℝ) (hroot : unfolding s a = (a : ℂ)) :
    ∀ n : ℕ, approximation s a (a : ℂ) n = 0 := by
  have ho : ∀ n : ℕ, orbit (a : ℂ) s n = (a : ℂ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [orbit_succ, ih, hroot]
  intro n
  simp [approximation, ho n]

theorem koenigsValue_at_root (s a : ℝ) (hroot : unfolding s a = (a : ℂ)) :
    koenigsValue s a (a : ℂ) = 0 := by
  simp [koenigsValue, increment, approximation_at_root s a hroot]

theorem quadratic_koenigs_error (s a D r : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a)
    (hD : 0 ≤ D) (hD1 : D ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrμ : r ^ 2 < multiplier s a)
    (horbit : ∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ D * r ^ n) :
    ‖koenigsValue s a u - (u - (a : ℂ))‖ ≤
      (1 / multiplier s a * (1 - r ^ 2 / multiplier s a)⁻¹) * D ^ 2 := by
  have hp : 0 ≤ r ^ 2 / multiplier s a := by positivity
  have hp1 : r ^ 2 / multiplier s a < 1 := (div_lt_one hμ).mpr hrμ
  have hsum := summable_norm_increment s a D r u hs hs1 ha ha0 hroot hμ hD hD1 hr hr1 hrμ horbit
  have hmajor := (summable_geometric_of_lt_one hp hp1).mul_left (D ^ 2 / multiplier s a)
  have hbound := increment_norm_bound s a D r u hs hs1 ha ha0 hroot hμ hD hD1 hr hr1 horbit
  unfold koenigsValue
  rw [add_sub_cancel_left]
  calc
    _ ≤ ∑' n : ℕ, ‖increment s a u n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, D ^ 2 / multiplier s a * (r ^ 2 / multiplier s a) ^ n :=
      hsum.tsum_le_tsum hbound hmajor
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg hp]; exact hp1)]
      ring

/-- No orbit estimate is an input: the actual quadratic exponential bound
constructs the invariant ball, true orbit limit and analytic normalized map. -/
theorem exists_actual_local_koenigs (s a : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      AnalyticOnNhd ℂ (koenigsValue s a) (ball (a : ℂ) δ) ∧
      koenigsValue s a (a : ℂ) = 0 ∧ HasDerivAt (koenigsValue s a) 1 (a : ℂ) ∧
      ∀ u ∈ ball (a : ℂ) δ,
        Summable (fun n => ‖increment s a u n‖) ∧
        Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) ∧
        unfolding s u ∈ ball (a : ℂ) δ ∧
        koenigsValue s a (unfolding s u) = (multiplier s a : ℂ) * koenigsValue s a u := by
  obtain ⟨r, δ, hr, hr1, _hmr, hrμ, hδ, hδ1, hμδ⟩ := exists_contraction_rate _ hμ hμ1
  have ho := local_orbit_geometric s a r δ hs hs1 ha ha0 hroot hμ hr.le hr1.le hδ hδ1 hμδ
  have hsum : ∀ u ∈ ball (a : ℂ) δ, Summable (fun n => ‖increment s a u n‖) := by
    intro u hu
    have hun : ‖u - (a : ℂ)‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hu
    have hn : ‖u - (a : ℂ)‖ ≤ 1 := hun.le.trans hδ1
    exact summable_norm_increment s a _ r u hs hs1 ha ha0 hroot hμ (norm_nonneg _) hn
      hr.le hr1.le hrμ (ho u hu)
  let M := δ ^ 2 / multiplier s a
  let p := r ^ 2 / multiplier s a
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p < 1 := (div_lt_one hμ).mpr hrμ
  have hmajor := (summable_geometric_of_lt_one hp hp1).mul_left M
  have hbound : ∀ n : ℕ, ∀ u ∈ ball (a : ℂ) δ, ‖increment s a u n‖ ≤ M * p ^ n := by
    intro n u hu
    have hun : ‖u - (a : ℂ)‖ ≤ δ :=
      (by simpa only [mem_ball, dist_eq_norm] using hu : ‖u - (a : ℂ)‖ < δ).le
    have hn : ‖u - (a : ℂ)‖ ≤ 1 := hun.trans hδ1
    have hb := increment_norm_bound s a _ r u hs hs1 ha ha0 hroot hμ (norm_nonneg _) hn
      hr.le hr1.le (ho u hu) n
    have hsq : ‖u - (a : ℂ)‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hun 2
    exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq hμ.le) (by positivity))
  have hterms : ∀ n : ℕ, DifferentiableOn ℂ (fun u => increment s a u n) (ball (a : ℂ) δ) := by
    intro n
    have haN (k : ℕ) : Differentiable ℂ (fun u => approximation s a u k) :=
      (differentiable_const (((multiplier s a : ℂ) ^ k)⁻¹)).mul
        ((Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s k).sub_const (a : ℂ))
    exact ((haN (n + 1)).sub (haN n)).differentiableOn
  have hsumhol := Complex.differentiableOn_tsum_of_summable_norm hmajor hterms isOpen_ball hbound
  have hhol : DifferentiableOn ℂ (koenigsValue s a) (ball (a : ℂ) δ) :=
    (differentiableOn_id.sub_const (a : ℂ)).add hsumhol
  have hzero := koenigsValue_at_root s a hroot
  have hbig : (fun u : ℂ => koenigsValue s a u - (u - (a : ℂ))) =O[𝓝 (a : ℂ)]
      (fun u : ℂ => ‖u - (a : ℂ)‖ ^ 2) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1 / multiplier s a * (1 - p)⁻¹, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ : (a : ℂ) ∈ ball (a : ℂ) δ)] with u hu
    have hun : ‖u - (a : ℂ)‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hu
    have hn : ‖u - (a : ℂ)‖ ≤ 1 := hun.le.trans hδ1
    simpa only [p, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u - (a : ℂ)‖)] using
      quadratic_koenigs_error s a _ r u hs hs1 ha ha0 hroot hμ (norm_nonneg _) hn
        hr.le hr1.le hrμ (ho u hu)
  have hder : HasDerivAt (koenigsValue s a) 1 (a : ℂ) := by
    apply HasDerivAt.of_isLittleO
    simpa only [hzero, sub_zero, smul_eq_mul, mul_one] using
      hbig.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub (a : ℂ) (m := 2) (by norm_num))
  refine ⟨δ, hδ, (fun u hu => hhol.analyticAt (isOpen_ball.mem_nhds hu)), hzero, hder, ?_⟩
  intro u hu
  have hnorm := ho u hu 1
  have hun : ‖u - (a : ℂ)‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hu
  have hin : unfolding s u ∈ ball (a : ℂ) δ := by
    rw [mem_ball, dist_eq_norm]
    simp only [orbit_succ, orbit_zero, pow_one] at hnorm
    exact hnorm.trans_lt ((mul_le_mul_of_nonneg_left hr1.le (norm_nonneg _)).trans_lt (by simpa using hun))
  exact ⟨hsum u hu, tendsto_approximation s a u (hsum u hu), hin,
    koenigsValue_functional_eq s a u (ne_of_gt hμ) (hsum u hu)⟩

/-- The roots and normalized analytic Koenigs map are constructed for
every sufficiently small positive parameter of the actual exponential. -/
theorem exists_actual_positive_koenigs :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ a b δ : ℝ, -1 < a ∧ a < 0 ∧ 0 < b ∧
        unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
        0 < multiplier s a ∧ multiplier s a < 1 ∧ 0 < δ ∧
        AnalyticOnNhd ℂ (koenigsValue s a) (ball (a : ℂ) δ) ∧
        koenigsValue s a (a : ℂ) = 0 ∧ HasDerivAt (koenigsValue s a) 1 (a : ℂ) ∧
        ∀ u ∈ ball (a : ℂ) δ,
          Summable (fun n => ‖increment s a u n‖) ∧
          Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) ∧
          unfolding s u ∈ ball (a : ℂ) δ ∧
          koenigsValue s a (unfolding s u) = (multiplier s a : ℂ) * koenigsValue s a u := by
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := exists_ordered_small_real_roots (1 / 4) (by norm_num)
  refine ⟨s₀, hs₀, ?_⟩
  intro s hs hss
  obtain ⟨a, b, haδ, ha0, hb0, _hbδ, hfa, hfb⟩ := hroots s hs hss
  have ha : -1 < a := by linarith
  have hμ : 0 < multiplier s a := by dsimp [multiplier]; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by
    dsimp [multiplier]
    nlinarith
  obtain ⟨δ, hδ, hhol, hzero, hder, hrest⟩ := exists_actual_local_koenigs s a hs.le
    (by linarith) ha ha0.le hfa hμ hμ1
  exact ⟨a, b, δ, ha, ha0, hb0, hfa, hfb, hμ, hμ1, hδ, hhol, hzero, hder, hrest⟩

end Kneser.PositiveLocalKoenigs

end
