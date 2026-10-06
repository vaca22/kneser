import Kneser.ActualHigherPreparedCoordinate
import Kneser.PreparedCanonicalAtZero

/-! Actual positive-parameter attracting orbits have a common real-root
limit on each bounded buffered parabolic petal.  No orbit limit is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.PositiveOrbitRootLimit

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ParabolicExponentialOrbit Kneser.RealExponentialPetal
open Kneser.ParabolicInitialPetal Kneser.ApolloniusGeometry
open scoped Topology

theorem exists_uniform_actual_orbit_root_limit :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          ∀ u : ℂ, R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
            Tendsto (fun k : ℕ => orbit u s k) atTop (𝓝 (a : ℂ)) := by
  obtain ⟨Q⟩ := exists_quotientControl
  obtain ⟨R₁, hR₁, hpetals⟩ := exists_uniform_initial_parabolic_petals
  let R₀ : ℝ := max R₁ (max 1 (80 / Q.radius))
  refine ⟨R₀, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRQ : 80 / Q.radius ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  let W : ℝ := max Z (max 1 (4 / Q.radius))
  have hWZ : Z ≤ W := le_max_left _ _
  have hWone : 1 ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have hWQ : 4 / Q.radius ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  have hW : 0 ≤ W := hZ.trans hWZ
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := hpetals R hRR₁ W hW
  refine ⟨s₀, hs₀, ?_⟩
  intro s hs hss
  obtain ⟨a, b, θ, ha, hb, haW, hbW, hθ, hfa, hfb, hθeq, horbit⟩ := hroots s hs hss
  have hs' : s < 1 / 2 := hss.trans_le hs₀half
  have hab : a < b := by linarith
  have hgap : b - a < Q.radius / 8 := by
    have hsmall : 1 / (2 * (W + 1)) < Q.radius / 8 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (W + 1))).mpr
      have hmul := (div_le_iff₀ Q.radius_pos).mp hWQ
      nlinarith [Q.radius_pos]
    rw [abs_of_neg ha] at haW
    rw [abs_of_pos hb] at hbW
    have heq : 1 / (2 * (W + 1)) = 2 * (1 / (4 * (W + 1))) := by
      field_simp
      ring
    rw [heq] at hsmall
    linarith
  have ha1 : -1 < a := by
    have hh : 1 / (4 * (W + 1)) ≤ 1 / 8 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * (W + 1)) (by norm_num)).mpr
      linarith
    rw [abs_of_neg ha] at haW
    linarith
  have hθQ : timeScale Q ((1 - s) * (b - a)) = θ :=
    (timeScale_eq_neg_log_multiplier Q s a b (by linarith) ha1 hab hfa hfb).trans hθeq.symm
  refine ⟨a, b, ha, hb, hfa, hfb, ?_⟩
  intro u hu hZu
  have hub : u ≠ (b : ℂ) := by
    have hneg := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate u).re by linarith)
    intro heq
    simp [heq] at hneg
    linarith
  have hq := (horbit u hu (hZu.trans hWZ)).1
  rw [← hθQ] at hq
  let C : ℝ := 4 * (b - a) / (3 * θ)
  have hbound : ∀ k : ℕ, ‖orbit u s k - (a : ℂ)‖ ≤ C / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨hne, hn⟩ := infinite_orbit_crossRatio_bound Q s a b R u
      hs hs' hab hb hfa hfb hgap hRQ hub hq k
    rw [hθQ] at hn
    have hx : 0 < R + (3 / 4) * (k : ℝ) := by positivity
    have hdist := attracting_root_distance_bound (a : ℂ) b (orbit u s k)
      (θ * (R + (3 / 4) * (k : ℝ))) (mul_pos hθ hx) hne hn
    have hg : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
      rw [← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_pos.mpr hab).le]
    rw [hg] at hdist
    apply hdist.trans
    dsimp [C]
    apply (div_le_div_iff₀ (mul_pos hθ hx) (by positivity : 0 < (k : ℝ) + 1)).mpr
    have hden : 3 * θ ≠ 0 := by positivity
    field_simp [hden]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hmajorant : Tendsto (fun k : ℕ => C / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := C)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> simp [div_eq_mul_inv]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hmajorant)

end Kneser.PositiveOrbitRootLimit

end
