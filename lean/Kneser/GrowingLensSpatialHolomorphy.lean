import Kneser.GrowingLensUniformMajorant
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Spatial holomorphy of the genuine growing-lens orbit sums. The local
uniform majorants are deduced from the true logarithmic-time drift. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.GrowingLensSpatialHolomorphy

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.GrowingBandGeometry Kneser.GrowingLensEntry Kneser.ActualLensGeometry
open Kneser.ActualLensModel Kneser.EvenPreparedOrbitDiscs Kneser.ActualLensDynamics
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.ActualReflectedLensModel Kneser.GrowingLensUniformMajorant
open scoped Topology

def forwardSeries (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (Z : ℂ) : ℂ :=
  ∑' k, descendedTerm A B Γ 2 (bandChart a b θ Z) s k

def inverseSeries (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (Z : ℂ) : ℂ :=
  ∑' k, descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0

def attractingCoordinate (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ : ℝ) (e₁ e₂ : ℂ) (Z : ℂ) : ℂ :=
  lensModel s a b θ e₁ e₂ (bandChart a b θ Z) + forwardSeries A B Γ s a b θ Z

def repellingCoordinate (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ : ℝ) (e₁ e₂ : ℂ) (Z : ℂ) : ℂ :=
  lensModel s a b θ e₁ e₂ (bandChart a b θ Z) - inverseSeries A B Γ s a b θ Z

theorem strip_isOpen (θ Y : ℝ) : IsOpen (strip θ Y) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem analyticAt_forwardOrbit_spatial (s u : ℂ) (k : ℕ) :
    AnalyticAt ℂ (fun v => orbit v s k) u := by
  induction k with
  | zero => exact analyticAt_id
  | succ k ih =>
    have hmap : Differentiable ℂ (unfolding s) := fun v => (hasDerivAt_unfolding_spatial s v).differentiableAt
    convert (hmap.analyticAt (orbit u s k)).comp (f := fun v => orbit v s k) ih using 1
    funext v
    exact orbit_succ v s k

theorem analyticAt_physical_inverseOrbit (s : ℝ) (u : ℂ) (k : ℕ)
    (hsmall : ∀ j, ‖inverseOrbit s u j‖ < 1) :
    AnalyticAt ℂ (fun v => inverseOrbit s v k) u := by
  induction k with
  | zero => exact analyticAt_id
  | succ k ih =>
    have hslit : 1 + inverseOrbit s u k ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.add_re, Complex.one_re]
      linarith [(abs_le.mp (Complex.abs_re_le_norm (inverseOrbit s u k))).1, hsmall k]
    have hh : AnalyticAt ℂ (fun v => Complex.log (1 + inverseOrbit s v k) + (s : ℂ)) u :=
      ((analyticAt_const.add ih).clog hslit).add analyticAt_const
    have hd := hh.div_const (c := ((1 - s : ℝ) : ℂ))
    convert hd using 1 <;> first | rfl | (funext v; rw [inverseOrbit_succ, inverseStep_formula])

theorem analyticAt_forwardTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y : ℝ) (Z : ℂ) (k : ℕ) (hab : a < b) (hθ : 0 < θ)
    (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y)
    (hΓ : AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), orbit (bandChart a b θ Z) s k)) :
    AnalyticAt ℂ (fun W => descendedTerm A B Γ 2 (bandChart a b θ W) s k) Z := by
  have ho := (analyticAt_forwardOrbit_spatial (s : ℂ) (bandChart a b θ Z) k).comp
    (analyticOnNhd_bandChart a b θ Y hab hθ hY hYθ Z hZ)
  have hpoly : AnalyticAt ℂ (fun W => (orbit (bandChart a b θ W) s k ^ 2 -
      A s * orbit (bandChart a b θ W) s k + B s) ^ 2) Z :=
    (((ho.pow 2).sub (analyticAt_const.mul ho)).add analyticAt_const).pow 2
  have hin : AnalyticAt ℂ (fun W => (Complex.sqrt (s : ℂ), orbit (bandChart a b θ W) s k)) Z :=
    analyticAt_const.prod ho
  have hh := hpoly.mul (hΓ.comp (f := fun W => (Complex.sqrt (s : ℂ), orbit (bandChart a b θ W) s k)) hin)
  convert hh using 1 <;> first | rfl | (funext W; simp only [descendedTerm, splitTerm, Kneser.AnalyticEvenDescent.square_sqrt, rootPolynomial]; rfl)

theorem analyticAt_inverseTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y : ℝ) (Z : ℂ) (k : ℕ) (hab : a < b) (hθ : 0 < θ)
    (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) (hZ : Z ∈ strip θ Y)
    (hsmall : ∀ j, ‖inverseOrbit s (bandChart a b θ Z) j‖ < 1)
    (hΓ : AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), inverseOrbit s (bandChart a b θ Z) (k + 1))) :
    AnalyticAt ℂ (fun W => descendedTerm A B Γ 2
      (inverseOrbit s (bandChart a b θ W) (k + 1)) s 0) Z := by
  have ho := (analyticAt_physical_inverseOrbit s (bandChart a b θ Z) (k + 1) hsmall).comp
    (analyticOnNhd_bandChart a b θ Y hab hθ hY hYθ Z hZ)
  have hpoly : AnalyticAt ℂ (fun W => (inverseOrbit s (bandChart a b θ W) (k + 1) ^ 2 -
      A s * inverseOrbit s (bandChart a b θ W) (k + 1) + B s) ^ 2) Z :=
    (((ho.pow 2).sub (analyticAt_const.mul ho)).add analyticAt_const).pow 2
  have hin : AnalyticAt ℂ (fun W => (Complex.sqrt (s : ℂ), inverseOrbit s (bandChart a b θ W) (k + 1))) Z :=
    analyticAt_const.prod ho
  have hh := hpoly.mul (hΓ.comp (f := fun W => (Complex.sqrt (s : ℂ), inverseOrbit s (bandChart a b θ W) (k + 1))) hin)
  convert hh using 1 <;> first | rfl | (funext W; simp only [descendedTerm, splitTerm, Kneser.AnalyticEvenDescent.square_sqrt, orbit_zero, rootPolynomial]; rfl)

/-- A local source disc has a common bound on its initial real time. -/
theorem source_re_bound (Z W : ℂ) (r : ℝ) (hr : r ≤ 1) (hW : W ∈ ball Z r) :
    |W.re| ≤ |Z.re| + 1 := by
  have hnorm : ‖W - Z‖ ≤ r := by simpa only [dist_eq_norm] using (mem_ball.mp hW).le
  have hh := (Complex.abs_re_le_norm (W - Z)).trans hnorm
  rw [Complex.sub_re] at hh
  have ht := abs_add_le (W.re - Z.re) Z.re
  rw [sub_add_cancel] at ht
  linarith

/-- The infinite forward sum is locally uniformly summable and holomorphic
on the growing strip; no termwise differentiation is assumed. -/
theorem analyticOnNhd_forwardSeries_of_true_control (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y M : ℝ) (hab : a < b) (hθ : 0 < θ) (hY : 2 ≤ Y)
    (hYθ : θ * Y ≤ Real.pi) (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hterm : ∀ k Z, Z ∈ strip θ Y → AnalyticAt ℂ
      (fun W => descendedTerm A B Γ 2 (bandChart a b θ W) s k) Z)
    (hroots : ∀ Z ∈ strip θ Y, ∀ k, orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
      orbit (bandChart a b θ Z) s k ≠ (b : ℂ))
    (hband : ∀ Z ∈ strip θ Y, ∀ k, bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2))
    (hres : ∀ Z ∈ strip θ Y, ∀ k, ‖descendedTerm A B Γ 2 (orbit (bandChart a b θ Z) s k) s 0‖ ≤
      M * (‖orbit (bandChart a b θ Z) s k - (a : ℂ)‖ * ‖orbit (bandChart a b θ Z) s k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ Z ∈ strip θ Y, ∀ k,
      (bandTime a b θ (orbit (bandChart a b θ Z) s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit (bandChart a b θ Z) s (k + 1))).re) :
    AnalyticOnNhd ℂ (forwardSeries A B Γ s a b θ) (strip θ Y) := by
  intro Z hZ
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (strip_isOpen θ Y) Z hZ
  let r := min δ 1
  have hr : 0 < r := lt_min hδ (by norm_num)
  have hsub : ball Z r ⊆ strip θ Y := (ball_subset_ball (min_le_left _ _)).trans hδsub
  let L := |Z.re| + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hhalf : θ * (Y / 2) ≤ Real.pi := by nlinarith
  have hb : ∀ k W, W ∈ ball Z r → ‖descendedTerm A B Γ 2 (bandChart a b θ W) s k‖ ≤ majorant M L θ k := by
    intro k W hW
    have hWs := hsub hW
    have ht := bandTime_bandChart a b θ Y W hab hθ (by linarith) hYθ hWs
    have hl := time_step_lower (fun j => (bandTime a b θ (orbit (bandChart a b θ W) s j)).re)
      (3 / 4) (hstep W hWs) k
    simp only [orbit_zero, ht] at hl
    have hx : -L + (3 / 4) * k ≤ (bandTime a b θ (orbit (bandChart a b θ W) s k)).re := by
      have hw := source_re_bound Z W r (min_le_right _ _) hW
      have hw' := (abs_le.mp hw).1
      dsimp [L]
      linarith
    rw [← descendedTerm_at_orbit A B Γ (bandChart a b θ W) (s : ℂ) k]
    exact residual_le_majorant A B Γ s a b θ (Y / 2) M L _ k hM hL hab hθ (by linarith)
      hhalf hratio (hroots W hWs k).1 (hroots W hWs k).2 (hband W hWs k) (hres W hWs k) hx
  have hd := Complex.differentiableOn_tsum_of_summable_norm (summable_majorant M L θ hθ)
    (fun k W hW => (hterm k W (hsub hW)).differentiableAt.differentiableWithinAt)
    isOpen_ball hb
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))

theorem analyticOnNhd_inverseSeries_of_true_control (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y M : ℝ) (hab : a < b) (hθ : 0 < θ) (hY : 2 ≤ Y)
    (hYθ : θ * Y ≤ Real.pi) (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hterm : ∀ k Z, Z ∈ strip θ Y → AnalyticAt ℂ
      (fun W => descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ W) (k + 1)) s 0) Z)
    (hroots : ∀ Z ∈ strip θ Y, ∀ k, inverseOrbit s (bandChart a b θ Z) k ≠ (a : ℂ) ∧
      inverseOrbit s (bandChart a b θ Z) k ≠ (b : ℂ))
    (hband : ∀ Z ∈ strip θ Y, ∀ k, bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k) ∈ strip θ (Y / 2))
    (hres : ∀ Z ∈ strip θ Y, ∀ k, ‖descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) k) s 0‖ ≤
      M * (‖inverseOrbit s (bandChart a b θ Z) k - (a : ℂ)‖ * ‖inverseOrbit s (bandChart a b θ Z) k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ Z ∈ strip θ Y, ∀ k,
      (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) (k + 1))).re + 3 / 4 ≤
      (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k)).re) :
    AnalyticOnNhd ℂ (inverseSeries A B Γ s a b θ) (strip θ Y) := by
  intro Z hZ
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (strip_isOpen θ Y) Z hZ
  let r := min δ 1
  have hr : 0 < r := lt_min hδ (by norm_num)
  have hsub : ball Z r ⊆ strip θ Y := (ball_subset_ball (min_le_left _ _)).trans hδsub
  let L := |Z.re| + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hhalf : θ * (Y / 2) ≤ Real.pi := by nlinarith
  have hb : ∀ k W, W ∈ ball Z r → ‖descendedTerm A B Γ 2
      (inverseOrbit s (bandChart a b θ W) (k + 1)) s 0‖ ≤ majorant M L θ k := by
    intro k W hW
    have hWs := hsub hW
    have ht := bandTime_bandChart a b θ Y W hab hθ (by linarith) hYθ hWs
    have hs : ∀ j, -(bandTime a b θ (inverseOrbit s (bandChart a b θ W) j)).re + 3 / 4 ≤
        -(bandTime a b θ (inverseOrbit s (bandChart a b θ W) (j + 1))).re := by
      intro j
      linarith only [hstep W hWs j]
    have hl := time_step_lower (fun j => -(bandTime a b θ (inverseOrbit s (bandChart a b θ W) j)).re)
      (3 / 4) hs (k + 1)
    simp only [inverseOrbit_zero, ht, Nat.cast_add, Nat.cast_one] at hl
    have hx : -L + (3 / 4) * k ≤ -(bandTime a b θ (inverseOrbit s (bandChart a b θ W) (k + 1))).re := by
      have hw := source_re_bound Z W r (min_le_right _ _) hW
      have hw' := (abs_le.mp hw).2
      change -(|Z.re| + 1) + (3 / 4) * k ≤ -(bandTime a b θ (inverseOrbit s (bandChart a b θ W) (k + 1))).re
      linarith only [hl, hw']
    exact residual_le_majorant_left A B Γ s a b θ (Y / 2) M L _ k hM hL hab hθ (by linarith)
      hhalf hratio (hroots W hWs (k + 1)).1 (hroots W hWs (k + 1)).2
      (hband W hWs (k + 1)) (hres W hWs (k + 1)) hx
  have hd := Complex.differentiableOn_tsum_of_summable_norm (summable_majorant M L θ hθ)
    (fun k W hW => (hterm k W (hsub hW)).differentiableAt.differentiableWithinAt)
    isOpen_ball hb
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))

end Kneser.GrowingLensSpatialHolomorphy
end
