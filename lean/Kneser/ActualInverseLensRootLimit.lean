import Kneser.ActualBilateralGrowingLens
import Kneser.GrowingLensEntry

/-! The true backward time drift gives convergence of the principal
inverse orbit to the actual repelling root. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.ActualInverseLensRootLimit
open Set Metric Filter
open Kneser.ApolloniusGeometry Kneser.ActualLensGeometry
open Kneser.GrowingBandGeometry Kneser.GrowingLensEntry
open Kneser.ActualInverseLensBootstrap Kneser.PositiveKoenigsOrbit
open Kneser.ReflectedOrbitChainCoefficient Kneser.ActualBilateralGrowingLens
open Kneser.ExponentialUnfolding
open scoped Topology

theorem crossRatio_swap (a b : ℝ) (u : ℂ) :
    crossRatio b a u=(crossRatio a b u)⁻¹ := by
  simp only [crossRatio,inv_div]

theorem swapped_crossRatio_eq_exp_time (a b θ : ℝ) (u : ℂ)
    (hθ : 0<θ) (hua : u≠(a:ℂ)) (hub : u≠(b:ℂ)) :
    ‖crossRatio b a u‖=Real.exp (θ*(bandTime a b θ u).re) := by
  rw [crossRatio_swap,norm_inv,norm_crossRatio_eq_exp_time a b θ u hθ hua hub]
  rw [←Real.exp_neg]
  congr 1
  ring

theorem inverse_time_step_upper (s a b θ : ℝ) (u : ℂ)
    (hstep : ∀ k, (bandTime a b θ (inverseOrbit s u (k+1))).re+3/4≤
      (bandTime a b θ (inverseOrbit s u k)).re) :
    ∀ k : ℕ, (bandTime a b θ (inverseOrbit s u k)).re≤
      (bandTime a b θ u).re-(3/4)*(k:ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one]
    linarith [hstep k]

theorem true_inverse_orbit_tendsto_root (s a b θ : ℝ) (u : ℂ)
    (hab : a<b) (hθ : 0<θ)
    (hroots : ∀ k, inverseOrbit s u k≠(a:ℂ) ∧ inverseOrbit s u k≠(b:ℂ))
    (hstep : ∀ k, (bandTime a b θ (inverseOrbit s u (k+1))).re+3/4≤
      (bandTime a b θ (inverseOrbit s u k)).re) :
    Tendsto (inverseOrbit s u) atTop (𝓝 (b:ℂ)) := by
  let r := Real.exp (-(3/4)*θ)
  have hr : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  apply sequence_tendsto_root_of_geometric_crossRatio (inverseOrbit s u) b a
    (Real.exp (θ*(bandTime a b θ u).re)) r (ne_of_gt hab) hr hr1 (fun k => (hroots k).1)
  intro k
  rw [swapped_crossRatio_eq_exp_time a b θ _ hθ (hroots k).1 (hroots k).2]
  have hk := inverse_time_step_upper s a b θ u hstep k
  have he : Real.exp (θ*((bandTime a b θ u).re-(3/4)*(k:ℝ)))=
      Real.exp (θ*(bandTime a b θ u).re)*r^k := by
    dsimp [r]
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  rw [←he]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hθ.le)

/-- Actual bilateral lens control supplies every drift and root-avoidance
premise of the preceding theorem. -/
theorem exists_actual_bilateral_lens_root_limits
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        a<0 ∧ 0<b ∧ 0<θ ∧ unfolding s a=(a:ℂ) ∧ unfolding s b=(b:ℂ) ∧
        θ=-Real.log (multiplier s a) ∧ θ*Y≤Real.pi/2 ∧
        ∀ Z : ℂ, Z∈strip θ Y →
          Tendsto (orbit (bandChart a b θ Z) s) atTop (𝓝 (a:ℂ)) ∧
          Tendsto (inverseOrbit s (bandChart a b θ Z)) atTop (𝓝 (b:ℂ)) := by
  obtain ⟨Y,s₀,hY,hs₀,hs₀h,hall⟩ := exists_actual_bilateral_growing_lens U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,ha,hb,hθ,hfa,hfb,hθeq,hθY,hstates⟩ := hall s hs hss
  refine ⟨a,b,θ,ha,hb,hθ,hfa,hfb,hθeq,hθY,?_⟩
  intro Z hZ
  have hd := (hstates Z hZ).2.2.2.2
  have hFroots : ∀ k, orbit (bandChart a b θ Z) s k≠(a:ℂ) ∧ orbit (bandChart a b θ Z) s k≠(b:ℂ) :=
    fun k => ⟨(hd k).1,(hd k).2.1⟩
  have hGroots : ∀ k, inverseOrbit s (bandChart a b θ Z) k≠(a:ℂ) ∧
      inverseOrbit s (bandChart a b θ Z) k≠(b:ℂ) := fun k => ⟨(hd k).2.2.1,(hd k).2.2.2.1⟩
  have hFstep := fun k => (hd k).2.2.2.2.2.2.1
  have hGstep := fun k => (hd k).2.2.2.2.2.2.2
  exact ⟨true_forward_orbit_tendsto_root _ s a b θ (by linarith) hθ hFroots hFstep,
    true_inverse_orbit_tendsto_root s a b θ _ (by linarith) hθ hGroots hGstep⟩

end Kneser.ActualInverseLensRootLimit
end
