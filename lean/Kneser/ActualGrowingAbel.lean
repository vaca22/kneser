import Kneser.ActualGrowingRealPhases

/-! Genuine Abel identities for both actual growing-lens series. The real
midline identities follow by continuity from the true nonreal log branch. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualGrowingAbel
open Set Filter Metric Complex
open Kneser.ExponentialUnfolding Kneser.ActualLensModel Kneser.GrowingBandGeometry
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingLensKoenigs Kneser.ActualInverseLensBootstrap
open Kneser.ActualReflectedLensModel Kneser.EvenPreparedOrbitDiscs
open Kneser.RealRepellingCoordinatePhase Kneser.RealLensMidline
open Kneser.ActualKoenigsEntryRealPhase Kneser.GrowingLensSpatialHolomorphy
open scoped Topology BigOperators

theorem inverseOrbit_shift (s : ℝ) (u : ℂ) (k : ℕ) :
    inverseOrbit s (inverseStep s u) k=inverseOrbit s u (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [inverseOrbit_succ,ih]

theorem physical_model_steps_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (u : ℂ) (hu : u∈physicalLens a b θ Y) :
    lensModel s a b θ (e₁ s) (e₂ s) (unfolding s u)-lensModel s a b θ (e₁ s) (e₂ s) u-1=
      descendedTerm A B Γ 2 u s 0 ∧
    lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)-lensModel s a b θ (e₁ s) (e₂ s) u+1=
      -descendedTerm A B Γ 2 (inverseStep s u) s 0 := by
  obtain ⟨Z,hZ,rfl⟩ := hu
  have hd := hc.true_orbits Z hZ
  have huN : ‖bandChart a b θ Z‖≤η/4 := by simpa only [orbit_zero] using (hd.2.2.2.2.1 0).2.2.1
  by_cases hi : (bandChart a b θ Z).im=0
  · have he : bandChart a b θ Z=((bandChart a b θ Z).re:ℂ) := by apply Complex.ext <;> simp [hi]
    have htime := bandTime_bandChart a b θ Y Z (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
      (by linarith [hc.height_large]) (hc.width.trans (by linarith [Real.pi_pos])) hZ
    have hbetween := real_bandTime_between a b θ (bandChart a b θ Z).re
      (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
      (by intro hh; apply (hd.2.2.2.2.1 0).1; simpa only [orbit_zero] using he.trans (by rw [hh]))
      (by intro hh; apply (hd.2.2.2.2.1 0).2.1; simpa only [orbit_zero] using he.trans (by rw [hh]))
      (by rw [←he,htime]; exact lt_trans (by linarith [hc.height_large]) hZ.1)
    rw [he]
    exact lensControl_real_steps e₁ e₂ A B Γ s a b θ Y η M P _ hs1 hc hbetween.1 hbetween.2
  · exact ⟨hc.forward_nonreal_step _ (by linarith [hc.radius_pos]) hi,
      hc.inverse_nonreal_step _ huN hi⟩

theorem physicalAttracting_abel_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (u : ℂ) (hu : u∈physicalLens a b θ Y) :
    physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) (unfolding s u)=
      physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) u+1 := by
  obtain ⟨Z,hZ,huEq⟩ := hu
  have hsum : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) := by
    rw [←huEq]; exact (hc.true_orbits Z hZ).1
  have hshift : ∀ k, descendedTerm A B Γ 2 (unfolding s u) s k=descendedTerm A B Γ 2 u s (k+1) := by
    intro k
    have ho : orbit (unfolding s u) s k=orbit u s (k+1) := by
      simpa only [orbit_succ,orbit_zero] using actual_orbit_add u s 1 k
    simp only [descendedTerm,splitTerm,Kneser.AnalyticEvenDescent.square_sqrt,ho]
  have ht := hsum.of_norm.tsum_eq_zero_add
  have hh := (physical_model_steps_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc u ⟨Z,hZ,huEq⟩).1
  unfold physicalAttracting
  simp_rw [hshift]
  linear_combination hh-ht

theorem physicalRepelling_inverse_abel_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (u : ℂ) (hu : u∈physicalLens a b θ Y) :
    physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (inverseStep s u)=
      physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) u-1 := by
  obtain ⟨Z,hZ,huEq⟩ := hu
  have hsum : Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0‖) := by
    rw [←huEq]; exact (hc.true_orbits Z hZ).2.1
  have ht := hsum.of_norm.tsum_eq_zero_add
  have hh := (physical_model_steps_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc u ⟨Z,hZ,huEq⟩).2
  unfold physicalRepelling
  simp_rw [inverseOrbit_shift]
  change (∑' k,descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0)=
    descendedTerm A B Γ 2 (inverseStep s u) s 0+
    ∑' k,descendedTerm A B Γ 2 (inverseOrbit s u (k+1+1)) s 0 at ht
  linear_combination hh+ht

theorem inverseStep_unfolding (s : ℝ) (u : ℂ) (hs : 0≤s) (hs1 : s<1) (hu : ‖u‖≤1/4) :
    inverseStep s (unfolding s u)=u := by
  have hsne : (1-(s:ℂ))≠0 := by exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hs1))
  have hz : ‖-(s:ℂ)+(1-(s:ℂ))*u‖≤5/4 := by
    have hn := norm_add_le (-(s:ℂ)) ((1-(s:ℂ))*u)
    have h1 : ‖1-(s:ℂ)‖=1-s := by
      rw [show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs,norm_mul,h1] at hn
    nlinarith
  have hi := (Complex.abs_im_le_norm (-(s:ℂ)+(1-(s:ℂ))*u)).trans hz
  have hlog := Complex.log_exp
    (show -Real.pi<(-(s:ℂ)+(1-(s:ℂ))*u).im by linarith [ (abs_le.mp hi).1,Real.two_le_pi])
    (show (-(s:ℂ)+(1-(s:ℂ))*u).im≤Real.pi by linarith [(abs_le.mp hi).2,Real.two_le_pi])
  rw [inverseStep_formula]
  have he : 1+unfolding s u=Complex.exp (-(s:ℂ)+(1-(s:ℂ))*u) := by dsimp [unfolding]; ring
  rw [he,hlog]
  push_cast
  field_simp
  ring

theorem physicalRepelling_abel_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0≤s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (u : ℂ) (hu : u∈physicalLens a b θ Y) (hfu : unfolding s u∈physicalLens a b θ Y) :
    physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (unfolding s u)=
      physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) u+1 := by
  have huN : ‖u‖≤1/4 := by
    obtain ⟨Z,hZ,rfl⟩ := hu
    have hh := (hc.true_orbits Z hZ).2.2.2.2.1 0
    simp only [orbit_zero] at hh
    linarith [hh.2.2.1,hc.radius_small]
  have hh := physicalRepelling_inverse_abel_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc _ hfu
  rw [inverseStep_unfolding s u hs hs1 huN] at hh
  linear_combination -hh

end Kneser.ActualGrowingAbel
end
