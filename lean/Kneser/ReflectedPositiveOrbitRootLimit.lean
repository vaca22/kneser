import Kneser.ReflectedHigherPreparedCoordinate
import Kneser.RepellingRealPetal

/-! Genuine positive-parameter inverse orbits converge to the reflected
repelling root, uniformly in the choice of initial point on bounded
buffered petals.  The root limit is derived from the actual cross ratio. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ReflectedPositiveOrbitRootLimit

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.RepellingExponentialOrbit
open Kneser.ParabolicExponentialOrbit Kneser.RealExponentialPetal
open Kneser.RepellingRealPetal Kneser.ApolloniusGeometry
open scoped Topology

theorem exists_uniform_actual_inverseOrbit_root_limit :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          ∀ v : ℂ, R + 1 ≤ (inverseCoordinate v).re → ‖inverseCoordinate v‖ ≤ Z →
            Tendsto (fun k : ℕ => inverseOrbit v s k) atTop (𝓝 (-(b : ℂ))) := by
  obtain ⟨Q⟩ := exists_quotientControl
  obtain ⟨R₁, hR₁, hpetals⟩ := exists_uniform_initial_repelling_petals
  let R₀ : ℝ := max R₁ (max 80 (80 / Q.radius))
  refine ⟨R₀, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR80 : 80 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
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
    have heq : 1 / (2 * (W + 1)) = 2 * (1 / (4 * (W + 1))) := by field_simp; ring
    rw [heq] at hsmall
    linarith
  have hsmall : 1 / (4 * (W + 1)) ≤ 1 / 8 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * (W + 1)) (by norm_num)).mpr
    linarith
  have hasmall : -1 / 4 < a := by rw [abs_of_neg ha] at haW; linarith
  have hbsmall : b < 1 / 4 := by rw [abs_of_pos hb] at hbW; linarith
  have hθQ : inverseTimeScale Q ((1 - s) * (b - a)) = θ :=
    (inverseTimeScale_eq_log_multiplier Q s a b (by linarith) (by linarith)
      hab hfa hfb).trans hθeq.symm
  refine ⟨a, b, ha, hb, hfa, hfb, ?_⟩
  intro v hv hZv
  have hva : v ≠ -(a : ℂ) := by
    have hneg := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate v).re by linarith)
    intro heq
    simp [heq] at hneg
    linarith
  have hq := (horbit v hv (hZv.trans hWZ)).1
  rw [← hθQ] at hq
  let C : ℝ := 4 * (b - a) / (3 * θ)
  have hbound : ∀ k : ℕ, ‖inverseOrbit v s k - (-(b : ℂ))‖ ≤ C / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨hne, hn⟩ := infinite_inverseOrbit_crossRatio_bound Q s a b R v
      hs hs' ha hasmall hb hbsmall hfa hfb hgap hRQ hR80 hva hq k
    rw [hθQ] at hn
    have hx : 0 < R + (3 / 4) * (k : ℝ) := by positivity
    have hdist := attracting_root_distance_bound (-(b : ℂ)) (-(a : ℂ)) (inverseOrbit v s k)
      (θ * (R + (3 / 4) * (k : ℝ))) (mul_pos hθ hx) hne hn
    have hg : ‖(-(a : ℂ)) - (-(b : ℂ))‖ = b - a := by
      have heq : -(a : ℂ) - -(b : ℂ) = ((b - a : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_of_nonneg (sub_pos.mpr hab).le]
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

end Kneser.ReflectedPositiveOrbitRootLimit

end
