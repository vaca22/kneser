import Kneser.ActualInverseLensDynamics

/-! Actual logarithmic-time drift gives entry into every attracting
cross-ratio petal and convergence to the genuine fixed root. -/

noncomputable section
namespace Kneser.GrowingLensEntry

open Filter Kneser.ActualLensGeometry Kneser.GrowingBandGeometry
open Kneser.ApolloniusGeometry Kneser.ExponentialUnfolding
open scoped Topology

theorem norm_crossRatio_eq_exp_time (a b θ : ℝ) (u : ℂ) (hθ : 0 < θ)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ)) :
    ‖crossRatio a b u‖ = Real.exp (-θ * (bandTime a b θ u).re) := by
  have hn : 0 < ‖crossRatio a b u‖ := norm_pos_iff.mpr
    (div_ne_zero (sub_ne_zero.mpr hua) (sub_ne_zero.mpr hub))
  have ht := bandTime_re a b θ u
  have hh := congrArg (fun r : ℝ => r * θ) ht
  rw [div_mul_cancel₀ _ (ne_of_gt hθ)] at hh
  rw [← Real.exp_log hn]
  congr 1
  nlinarith

theorem time_step_lower (t : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ k, t k + c ≤ t (k + 1)) : ∀ k, t 0 + c * k ≤ t k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [hstep k]

theorem eventually_any_time_depth (t : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hstep : ∀ k, t k + c ≤ t (k + 1)) (R : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, R ≤ t k := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((R - t 0) / c)
  refine ⟨N, ?_⟩
  intro k hk
  have hcast : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hh := (div_lt_iff₀ hc).mp hN
  have hl := time_step_lower t c hstep k
  nlinarith

theorem true_forward_eventually_any_petal (u : ℂ) (s a b θ : ℝ) (hθ : 0 < θ)
    (hroots : ∀ k, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ))
    (hstep : ∀ k, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit u s (k + 1))).re) (R : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ‖crossRatio a b (orbit u s k)‖ ≤ Real.exp (-θ * R) := by
  obtain ⟨N, hN⟩ := eventually_any_time_depth (fun k => (bandTime a b θ (orbit u s k)).re)
    (3 / 4) (by norm_num) hstep R
  refine ⟨N, ?_⟩
  intro k hk
  rw [norm_crossRatio_eq_exp_time a b θ _ hθ (hroots k).1 (hroots k).2]
  apply Real.exp_le_exp.mpr
  nlinarith [hN k hk]

theorem rootChart_continuousAt_zero (a b : ℝ) : ContinuousAt (rootChart a b) 0 := by
  unfold rootChart
  exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.sub continuousAt_id) (by simp)

theorem sequence_tendsto_root_of_geometric_crossRatio (u : ℕ → ℂ) (a b C r : ℝ)
    (hab : a ≠ b) (hr : 0 ≤ r) (hr1 : r < 1)
    (hub : ∀ k, u k ≠ (b : ℂ))
    (hbound : ∀ k, ‖crossRatio a b (u k)‖ ≤ C * r ^ k) :
    Tendsto u atTop (𝓝 (a : ℂ)) := by
  have hn : Tendsto (fun k => ‖crossRatio a b (u k)‖) atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C
    simp only [mul_zero] at ht
    exact squeeze_zero (fun k => norm_nonneg _) hbound ht
  have hq : Tendsto (fun k => crossRatio a b (u k)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hu := (rootChart_continuousAt_zero a b).tendsto.comp hq
  change Tendsto (fun k => rootChart a b (crossRatio a b (u k))) atTop (𝓝 (rootChart a b 0)) at hu
  have he : (fun k => rootChart a b (crossRatio a b (u k))) = u :=
    funext (fun k => rootChart_crossRatio a b (u k) hab (hub k))
  rw [he] at hu
  simpa [rootChart] using hu

theorem true_forward_orbit_tendsto_root (u : ℂ) (s a b θ : ℝ) (hab : a < b) (hθ : 0 < θ)
    (hroots : ∀ k, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ))
    (hstep : ∀ k, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit u s (k + 1))).re) :
    Tendsto (orbit u s) atTop (𝓝 (a : ℂ)) := by
  let r := Real.exp (-(3 / 4) * θ)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  apply sequence_tendsto_root_of_geometric_crossRatio (orbit u s) a b
    (Real.exp (-θ * (bandTime a b θ u).re)) r (ne_of_lt hab) hr hr1 (fun k => (hroots k).2)
  intro k
  rw [norm_crossRatio_eq_exp_time a b θ _ hθ (hroots k).1 (hroots k).2]
  have hk := time_step_lower (fun k => (bandTime a b θ (orbit u s k)).re) (3 / 4) hstep k
  have he : Real.exp (-θ * ((bandTime a b θ u).re + (3 / 4) * k)) =
      Real.exp (-θ * (bandTime a b θ u).re) * r ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← he]
  apply Real.exp_le_exp.mpr
  simpa only [orbit_zero] using mul_le_mul_of_nonpos_left hk (neg_nonpos.mpr hθ.le)

end Kneser.GrowingLensEntry
end
