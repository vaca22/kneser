import Kneser.ActualGrowingTransition
import Kneser.ActualGrowingAbel

/-! Genuine translation equivariance of the growing transition. The
inverse dynamics first returns to the proved chart; injectivity identifies
it with the actual strip inverse. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualGrowingPeriodicity

open Filter Set Metric Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualGrowingTransition
open Kneser.ActualGrowingAbel Kneser.GrowingLensKoenigs
open Kneser.ActualGrowingRealPhases Kneser.RealRepellingCoordinatePhase
open Kneser.ActualLensGeometry Kneser.ActualInverseLensBootstrap
open Kneser.ActualReflectedLensModel Kneser.EvenPreparedOrbitDiscs
open scoped Topology

theorem inverse_tail_norm_le_one
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s : ℝ) (u : ℂ)
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0‖))
    (hb : (∑' k, ‖descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0‖) ≤ 1) :
    ‖∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0‖ ≤ 1 := by
  simp_rw [inverseOrbit_shift]
  have htail := hsum.comp_injective (i := fun k : ℕ => k+1) (by intro i j hh; exact Nat.add_right_cancel hh)
  have ht := hsum.tsum_eq_zero_add
  exact (norm_tsum_le_tsum_norm htail).trans (by
    have hp := norm_nonneg (descendedTerm A B Γ 2 (inverseOrbit s u (0+1)) s 0)
    linarith only [ht,hb,hp])

theorem actual_transition_translation
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s < 1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (V : ℂ → ℂ)
    (hVs : ∀ w ∈ strip θ (3 * Y + boundaryMargin P),
      V w ∈ strip θ (3 * Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w) = w)
    (w : ℂ) (hw : w ∈ strip θ (3 * Y + boundaryMargin P)) :
    transition A B Γ s a b θ (e₁ s) (e₂ s) V (w+1) =
      transition A B Γ s a b θ (e₁ s) (e₂ s) V w + 1 := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hsub : strip θ (3 * Y) ⊆ strip θ Y := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hsub2 : strip θ (3 * Y) ⊆ strip θ (2 * Y) := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hw1 : w+1 ∈ strip θ (3 * Y + boundaryMargin P) := by
    change 3 * Y + boundaryMargin P < (w+1).im ∧ (w+1).im < height θ - (3 * Y + boundaryMargin P)
    simp only [Complex.add_im,Complex.one_im,add_zero]
    exact hw
  let Z := V (w+1)
  let u := bandChart a b θ Z
  have hZ : Z ∈ strip θ (3 * Y) := (hVs (w+1) hw1).1
  have hZu := hc.true_orbits Z (hsub hZ)
  have hu : u ∈ physicalLens a b θ Y := ⟨Z,hsub hZ,rfl⟩
  have hS : physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) u = w+1 := (hVs (w+1) hw1).2
  have hgstate := hZu.2.2.2.2.2 1
  have hgnorm : ‖inverseStep s u‖ ≤ η / 4 := hgstate.2.2.1
  have hroota : inverseStep s u ≠ (a : ℂ) := hgstate.1
  have hrootb : inverseStep s u ≠ (b : ℂ) := hgstate.2.1
  have hSg : physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (inverseStep s u) = w := by
    rw [physicalRepelling_inverse_abel_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc u hu,hS]
    ring
  have hm := Kneser.ActualLensBounds.lensModel_phase_bound s a b θ P (e₁ s) (e₂ s)
    (inverseStep s u) hc.residue_bound hP hc.first_model_bound hc.second_model_bound
    (hgnorm.trans (by linarith [hc.radius_small]))
  have hn := inverse_tail_norm_le_one A B Γ s u hZu.2.1 hZu.2.2.2.1
  have hi := (Complex.abs_im_le_norm (∑' k, descendedTerm A B Γ 2
    (inverseOrbit s (inverseStep s u) (k+1)) s 0)).trans hn
  have hphase : |(physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      bandTime a b θ (inverseStep s u)).im| ≤ boundaryMargin P := by
    have hh := abs_add_le (lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      bandTime a b θ (inverseStep s u)).im (-(∑' k, descendedTerm A B Γ 2
        (inverseOrbit s (inverseStep s u) (k+1)) s 0).im)
    rw [abs_neg,←sub_eq_add_neg] at hh
    change |((lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      ∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0) -
      bandTime a b θ (inverseStep s u)).im| ≤ boundaryMargin P
    simp only [Complex.sub_im] at hm hh ⊢
    change |(lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im -
      (bandTime a b θ (inverseStep s u)).im| ≤ Real.pi + 2 * P + 1
    have he : (lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im -
      (bandTime a b θ (inverseStep s u)).im =
      ((lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im - (bandTime a b θ (inverseStep s u)).im) -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im := by ring
    rw [he]
    exact hh.trans (add_le_add hm hi)
  rw [hSg,Complex.sub_im] at hphase
  have htime : bandTime a b θ (inverseStep s u) ∈ strip θ (3 * Y) :=
    ⟨by linarith only [(abs_le.mp hphase).2,hw.1],by linarith only [(abs_le.mp hphase).1,hw.2]⟩
  have hchart := bandChart_bandTime a b θ (inverseStep s u) (ne_of_lt hab) (ne_of_gt hc.theta_pos) hroota hrootb
  have hg : inverseStep s u ∈ physicalLens a b θ Y := ⟨_,hsub htime,hchart⟩
  have hSchart : repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)
      (bandTime a b θ (inverseStep s u)) = w := by
    change physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s)
      (bandChart a b θ (bandTime a b θ (inverseStep s u))) = w
    rw [hchart,hSg]
  have htimeEq := (actual_coordinates_injective_buffered e₁ e₂ A B Γ s a b θ Y η M P hc).2
    (hsub2 htime) (hsub2 (hVs w hw).1) (hSchart.trans (hVs w hw).2.symm)
  have hgEq : inverseStep s u = bandChart a b θ (V w) := by rw [←htimeEq,hchart]
  have hfu : Kneser.ExponentialUnfolding.unfolding s (inverseStep s u) = u :=
    unfolding_inverseStep s u hs1 (by
      have hh := (hZu.2.2.2.2.1 0).2.2.1
      simp only [Kneser.ExponentialUnfolding.orbit_zero] at hh
      linarith only [hh,hc.radius_small])
  have hA := physicalAttracting_abel_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc (inverseStep s u) hg
  rw [hfu,hgEq] at hA
  exact hA

end Kneser.ActualGrowingPeriodicity
end
