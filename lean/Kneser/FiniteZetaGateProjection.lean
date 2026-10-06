import Kneser.ParabolicOverlapGate
import Kneser.FiniteGateJacobian
import Kneser.StableHolomorphicInverse

/-!
Quantitative control of the genuine finite inverse orbit in the ζ chart.
The sharper error tends to zero as the actual gate height tends to infinity;
this is the estimate needed for a whole image gate, rather than one point.
-/

noncomputable section
namespace Kneser.FiniteZetaGateProjection

open Set Metric Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ParabolicOverlapGate

/-- The finite-orbit estimate improves from k/4 to a bound decreasing with
height, using the actual one-step error and genuine orbit norms. -/
theorem finite_orbit_sharp_bound (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (H : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H)
    (hheight : H ≤ |(inverseCoordinate u).im|) :
    ∀ k : ℕ, k ≤ N →
      ‖inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ))‖ ≤
        16 * (k : ℝ) / (H - (N : ℝ) / 4) := by
  have hg := hH.trans hheight
  have hden : 0 < H - (N : ℝ) / 4 := by
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hnorm : ∀ k : ℕ, k ≤ N →
      ‖(f^[k]) u‖ ≤ 2 / (H - (N : ℝ) / 4) := by
    intro k hk
    have hb := finite_orbit_gate_bound f hstep u N hg k hk
    have him := (Complex.abs_im_le_norm
      (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hb
    simp only [Complex.sub_im, Complex.add_im, Complex.natCast_im, add_zero] at him
    have hi := norm_sub_norm_le (inverseCoordinate u).im (inverseCoordinate ((f^[k]) u)).im
    simp only [Real.norm_eq_abs] at hi
    rw [abs_sub_comm] at hi
    have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hlow : H - (N : ℝ) / 4 ≤ ‖inverseCoordinate ((f^[k]) u)‖ := by
      linarith [Complex.abs_im_le_norm (inverseCoordinate ((f^[k]) u))]
    rw [← inverseCoordinate_involutive ((f^[k]) u), ParabolicExponentialOrbit.inverseCoordinate_norm]
    exact div_le_div_of_nonneg_left (by norm_num) hden hlow
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk0 : k ≤ N := by omega
    have hb := ih hk0
    have hn := finite_orbit_gate_norm f hstep u N hg k hk0
    have hne : (f^[k]) u ≠ 0 := by
      intro hz
      have hl := hnorm k hk0
      have hb' := finite_orbit_gate_bound f hstep u N hg k hk0
      have hi := (Complex.abs_im_le_norm
        (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hb'
      simp only [hz, inverseCoordinate, div_zero, Complex.zero_im, Complex.zero_re,
        zero_sub, Complex.neg_im, abs_neg, Complex.add_im, Complex.natCast_im, add_zero] at hi
      change |(inverseCoordinate u).im| ≤ (k : ℝ) / 4 at hi
      have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk0
      linarith
    have hs := (hstep ((f^[k]) u) (by linarith) hne).trans
      (mul_le_mul_of_nonneg_left (hnorm k hk0) (by norm_num : (0 : ℝ) ≤ 8))
    have heq : inverseCoordinate ((f^[k + 1]) u) -
        (inverseCoordinate u + ((k + 1 : ℕ) : ℂ)) =
        (inverseCoordinate (f ((f^[k]) u)) - inverseCoordinate ((f^[k]) u) - 1) +
        (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ))) := by
      rw [Function.iterate_succ_apply']
      push_cast
      ring
    rw [heq]
    have ht := norm_add_le
      (inverseCoordinate (f ((f^[k]) u)) - inverseCoordinate ((f^[k]) u) - 1)
      (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))
    have ha : 8 * (2 / (H - (N : ℝ) / 4)) +
        16 * (k : ℝ) / (H - (N : ℝ) / 4) =
        16 * ((k + 1 : ℕ) : ℝ) / (H - (N : ℝ) / 4) := by push_cast; ring
    exact ht.trans ((add_le_add hs hb).trans_eq ha)

def inverseZetaProjection (N : ℕ) (z : ℂ) : ℂ :=
  inverseCoordinate (inverseOrbit (-inverseCoordinate z) 0 N)

theorem inverseZetaProjection_bound (N : ℕ) (z : ℂ) (H : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hz : H ≤ |z.im|) :
    ‖inverseZetaProjection N z - (-z + (N : ℂ))‖ ≤
      16 * (N : ℝ) / (H - (N : ℝ) / 4) := by
  have heq : inverseCoordinate (-inverseCoordinate z) = -z := by
    have hneg : inverseCoordinate (-inverseCoordinate z) = -inverseCoordinate (inverseCoordinate z) := by
      simp only [inverseCoordinate, div_neg]
    rw [hneg, inverseCoordinate_involutive]
  have h := finite_orbit_sharp_bound parabolicInverse
    RepellingExponentialOrbit.inverse_step_error_bound (-inverseCoordinate z) N H hH
    (by simpa [heq] using hz) N le_rfl
  simpa only [inverseZetaProjection, RepellingFatouCoordinate.inverseOrbit_zero_parameter, heq] using h


theorem inverseZetaProjection_ne_zero (N : ℕ) (z : ℂ)
    (hz : 64 * ((N : ℝ) + 1) ≤ |z.im|) : inverseZetaProjection N z ≠ 0 := by
  have heq : inverseCoordinate (-inverseCoordinate z) = -z := by
    have hneg : inverseCoordinate (-inverseCoordinate z) = -inverseCoordinate (inverseCoordinate z) := by
      simp only [inverseCoordinate, div_neg]
    rw [hneg, inverseCoordinate_involutive]
  have hb := finite_orbit_gate_bound parabolicInverse
    RepellingExponentialOrbit.inverse_step_error_bound (-inverseCoordinate z) N
    (by simpa [heq] using hz) N le_rfl
  have hi := (Complex.abs_im_le_norm
    (inverseCoordinate ((parabolicInverse^[N]) (-inverseCoordinate z)) -
      (inverseCoordinate (-inverseCoordinate z) + (N : ℂ)))).trans hb
  simp only [heq, ← RepellingFatouCoordinate.inverseOrbit_zero_parameter,
    Complex.sub_im, Complex.add_im, Complex.neg_im,
    Complex.natCast_im, add_zero] at hi
  change |(inverseZetaProjection N z).im - -z.im| ≤ (N : ℝ) / 4 at hi
  intro he
  rw [he, Complex.zero_im, zero_sub, neg_neg] at hi
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem analyticAt_inverseZetaProjection (N : ℕ) (z : ℂ)
    (hz : 64 * ((N : ℝ) + 1) ≤ |z.im|) :
    AnalyticAt ℂ (inverseZetaProjection N) z := by
  have hzne : z ≠ 0 := by
    intro he
    simp only [he, Complex.zero_im, abs_zero] at hz
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have heq : inverseCoordinate (-inverseCoordinate z) = -z := by
    have hneg : inverseCoordinate (-inverseCoordinate z) = -inverseCoordinate (inverseCoordinate z) := by
      simp only [inverseCoordinate, div_neg]
    rw [hneg, inverseCoordinate_involutive]
  have hi := FiniteGateJacobian.analyticAt_inverseOrbit_spatial_of_gate
    (-inverseCoordinate z) N (by simpa [heq] using hz) N le_rfl
  have hζ : AnalyticAt ℂ inverseCoordinate z := analyticAt_const.div analyticAt_id hzne
  have hinner := hi.comp (f := fun w : ℂ => -inverseCoordinate w) hζ.neg
  have hend : inverseOrbit (-inverseCoordinate z) 0 N ≠ 0 := by
    intro he
    have hn := inverseZetaProjection_ne_zero N z hz
    apply hn
    rw [inverseZetaProjection, he]
    simp only [inverseCoordinate, div_zero]
  exact (analyticAt_const.div analyticAt_id hend).comp
    (f := fun w : ℂ => inverseOrbit (-inverseCoordinate w) 0 N) hinner

theorem height_on_closedBall (Y ρ H : ℝ) (hY : H + ρ ≤ Y) (hH : 0 ≤ H)
    (z : ℂ) (hz : z ∈ closedBall (Complex.I * (Y : ℂ)) ρ) : H ≤ |z.im| := by
  have hn : ‖z - Complex.I * (Y : ℂ)‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z - Complex.I * (Y : ℂ))).trans hn
  have he : (z - Complex.I * (Y : ℂ)).im = z.im - Y := by simp
  rw [he] at hi
  have hl := (abs_le.mp hi).1
  exact (show H ≤ z.im by linarith).trans (le_abs_self _)

/-- Cauchy's estimate converts the true height-dependent finite-orbit
bound into a spatial derivative bound on a fixed ζ disc. -/
theorem inverseZetaProjection_deriv_bound (N : ℕ) (Y ρ H : ℝ)
    (hρ : 0 < ρ) (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 2 * ρ ≤ Y)
    (z : ℂ) (hz : z ∈ ball (Complex.I * (Y : ℂ)) ρ) :
    ‖deriv (inverseZetaProjection N) z + 1‖ ≤
      (16 * (N : ℝ) / (H - (N : ℝ) / 4)) / ρ := by
  let G : ℂ → ℂ := fun w => inverseZetaProjection N w + w - (N : ℂ)
  have hH0 : 0 ≤ H := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsub : closedBall z ρ ⊆ closedBall (Complex.I * (Y : ℂ)) (2 * ρ) := by
    intro w hw
    have hw' : dist w z ≤ ρ := hw
    have hz' : dist z (Complex.I * (Y : ℂ)) < ρ := hz
    exact (dist_triangle w z (Complex.I * (Y : ℂ))).trans (by linarith)
  have hwh : ∀ w ∈ closedBall z ρ, 64 * ((N : ℝ) + 1) ≤ |w.im| := by
    intro w hw
    exact hH.trans (height_on_closedBall Y (2 * ρ) H hY hH0 w (hsub hw))
  have hd : DifferentiableOn ℂ G (closedBall z ρ) := by
    intro w hw
    exact (((analyticAt_inverseZetaProjection N w (hwh w hw)).add analyticAt_id).sub
      analyticAt_const).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ sphere z ρ, ‖G w‖ ≤ 16 * (N : ℝ) / (H - (N : ℝ) / 4) := by
    intro w hw
    have hw' : w ∈ closedBall z ρ := mem_closedBall.mpr (mem_sphere.mp hw).le
    have h := inverseZetaProjection_bound N w H hH
      (height_on_closedBall Y (2 * ρ) H hY hH0 w (hsub hw'))
    convert h using 1
    dsimp [G]
    congr 1
    ring
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    ((hd.mono closure_ball_subset_closedBall).diffContOnCl) hb
  have hzH := hH.trans (height_on_closedBall Y (2 * ρ) H hY hH0 z
    (hsub (mem_closedBall_self hρ.le)))
  have hg := (((analyticAt_inverseZetaProjection N z hzH).hasStrictDerivAt.hasDerivAt.add
    (hasDerivAt_id z)).sub_const (N : ℂ)).deriv
  change deriv G z = deriv (inverseZetaProjection N) z + 1 at hg
  rwa [hg] at hc

end Kneser.FiniteZetaGateProjection
end
