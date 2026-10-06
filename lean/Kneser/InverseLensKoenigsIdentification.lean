import Kneser.InverseKoenigsRealGeometry
import Kneser.LensKoenigsIdentification

/-! The genuine inverse residual sum is the normalized repelling Koenigs
logarithm. Its additive constant is derived, including the actual branch
phase, rather than assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Kneser.InverseLensKoenigsIdentification
open Set Metric Filter Complex
open Kneser.ActualInverseLocalKoenigs Kneser.InverseKoenigsEntry
open Kneser.InverseKoenigsRealGeometry Kneser.QuadraticLocalKoenigs
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualLensModel Kneser.GrowingBandGeometry
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualKoenigsGlobalRealPhase Kneser.ActualReflectedLensMidline
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.ActualReflectedLensModel Kneser.EvenPreparedOrbitDiscs
open Kneser.RealRepellingCoordinatePhase Kneser.LensKoenigsIdentification
open scoped Topology BigOperators

def inverseModelConstant (s a b : ℝ) (e₁ e₂ : ℂ) : ℂ :=
  Complex.log ((b:ℂ)-(a:ℂ))/(Real.log (multiplier s a):ℂ)+e₁*b+e₂*(b:ℂ)^2

def intervalInverseKoenigsTime (s b : ℝ) (u : ℂ) : ℂ :=
  Complex.log (-inverseKoenigs s b u)/(Real.log (multiplier s b):ℂ)

theorem inverse_model_orbit_limit (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hs : 0<s) (hs1 : s<1/2) (hb : 0<b) (hθ : 0<θ)
    (hθeq : θ= -Real.log (multiplier s a)) (ha : -1<a) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (horbit : Tendsto (inverseOrbit s r) atTop (𝓝 (b:ℂ)))
    (hsum : Summable (fun n => ‖QuadraticLocalKoenigs.increment (inverseStep s) (b:ℂ) (inverseMultiplier s b) r n‖))
    (hslit : -inverseKoenigs s b r∈Complex.slitPlane) :
    Tendsto (fun n : ℕ => lensModel s a b θ e₁ e₂ (inverseOrbit s r n)+(n:ℂ)) atTop
      (𝓝 (intervalInverseKoenigsTime s b r+inverseModelConstant s a b e₁ e₂+(Real.pi:ℂ)*I/(θ:ℂ))) := by
  have hm : 0 < inverseMultiplier s b := inv_pos.mpr (lt_trans (by norm_num) (actual_right_multiplier s b hb hfb))
  have hl : 0<Real.log (multiplier s b) := Real.log_pos (actual_right_multiplier s b hb hfb)
  have hlc : (Real.log (multiplier s b):ℂ)≠0 := by exact_mod_cast (ne_of_gt hl)
  have hmclog : Real.log (inverseMultiplier s b)= -Real.log (multiplier s b) := Real.log_inv _
  have hmcn : (inverseMultiplier s b:ℂ)≠0 := by exact_mod_cast (ne_of_gt hm)
  have happ := QuadraticLocalKoenigs.tendsto_approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) r hsum
  have hbLog := happ.neg.clog hslit
  have haSlit : (b:ℂ)-(a:ℂ)∈Complex.slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have haLog := (horbit.sub_const (a:ℂ)).clog haSlit
  have ht := (((haLog.div_const (Real.log (multiplier s a):ℂ)).add
    (hbLog.div_const (Real.log (multiplier s b):ℂ))).add (horbit.const_mul e₁)).add
    ((horbit.pow 2).const_mul e₂) |>.add_const ((Real.pi:ℂ)*I/(θ:ℂ))
  have ht' : Tendsto (fun n : ℕ =>
      Complex.log (inverseOrbit s r n-(a:ℂ))/(Real.log (multiplier s a):ℂ)+
      Complex.log (-QuadraticLocalKoenigs.approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) r n)/(Real.log (multiplier s b):ℂ)+
      e₁*inverseOrbit s r n+e₂*(inverseOrbit s r n)^2+(Real.pi:ℂ)*I/(θ:ℂ)) atTop
      (𝓝 (intervalInverseKoenigsTime s b r+inverseModelConstant s a b e₁ e₂+(Real.pi:ℂ)*I/(θ:ℂ))) := by
    convert ht using 1
    dsimp [intervalInverseKoenigsTime,inverseModelConstant,inverseKoenigs]
    congr 1
    ring
  apply ht'.congr'
  filter_upwards [happ.neg.eventually_ne (slitPlane_ne_zero hslit)] with n hn
  have hp : (b:ℂ)-inverseOrbit s r n=(inverseMultiplier s b:ℂ)^n*
      (-QuadraticLocalKoenigs.approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) r n) := by
    rw [inverseOrbit_eq_iterate]
    unfold QuadraticLocalKoenigs.approximation
    field_simp
    ring
  have hpReal : (inverseMultiplier s b:ℂ)^n=((inverseMultiplier s b^n:ℝ):ℂ) := by simp
  have hlog : Complex.log ((b:ℂ)-inverseOrbit s r n)=
      -(n:ℂ)*(Real.log (multiplier s b):ℂ)+
      Complex.log (-QuadraticLocalKoenigs.approximation (inverseStep s) (b:ℂ) (inverseMultiplier s b) r n) := by
    rw [hp,hpReal,Complex.log_ofReal_mul (pow_pos hm n) hn,Real.log_pow,hmclog]
    push_cast
    ring
  have hreal : (inverseOrbit s r n).im=0 ∧ a<(inverseOrbit s r n).re ∧ (inverseOrbit s r n).re<b := by
    simpa only [inverseOrbit_eq_iterate] using real_between_inverse_orbit s a b r (by linarith) ha hfa hfb har hrb n
  have he : inverseOrbit s r n=((inverseOrbit s r n).re:ℂ) := by apply Complex.ext <;> simp [hreal.1]
  have hmodel := lensModel_real_formula s a b θ (inverseOrbit s r n).re e₁ e₂ hθ hθeq hreal.2.1 hreal.2.2
  rw [←he] at hmodel
  rw [hmodel,hlog]
  field_simp
  ring

theorem inverse_residual_telescope
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ, lensModel s a b θ e₁ e₂ (inverseOrbit s u (k+1))-
      lensModel s a b θ e₁ e₂ (inverseOrbit s u k)+1=
      -descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0) (n : ℕ) :
    lensModel s a b θ e₁ e₂ u-∑ k∈Finset.range n,descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0=
      lensModel s a b θ e₁ e₂ (inverseOrbit s u n)+(n:ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,sub_add_eq_sub_sub,ih]
    have h := hstep n
    push_cast
    linear_combination -h

theorem physicalRepelling_orbit_limit
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ, lensModel s a b θ e₁ e₂ (inverseOrbit s u (k+1))-
      lensModel s a b θ e₁ e₂ (inverseOrbit s u k)+1=
      -descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0)
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0‖)) :
    Tendsto (fun n : ℕ => lensModel s a b θ e₁ e₂ (inverseOrbit s u n)+(n:ℂ)) atTop
      (𝓝 (physicalRepelling A B Γ s a b θ e₁ e₂ u)) := by
  have ht := (tendsto_const_nhds (x:=lensModel s a b θ e₁ e₂ u)).sub hsum.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall (inverse_residual_telescope A B Γ s a b θ e₁ e₂ u hstep))

theorem physicalRepelling_eq_inverse_koenigs_real_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r=
      intervalInverseKoenigsTime s b r+inverseModelConstant s a b (e₁ s) (e₂ s)+(Real.pi:ℂ)*I/(θ:ℂ) := by
  obtain ⟨hZ,hchart⟩ := interval_source a b θ Y r hc.theta_pos hc.width har hrb
  have hd := hc.true_orbits (bandTime a b θ r) hZ
  rw [hchart] at hd
  have hlim' := lensControl_inverse_limit e₁ e₂ A B Γ s a b θ Y η M P hc (bandTime a b θ r) hZ
  rw [hchart] at hlim'
  have hlim : Tendsto (inverseOrbit s (r:ℂ)) atTop (𝓝 (b:ℂ)) := by
    convert hlim' using 1
    funext n
    exact inverseOrbit_eq_iterate s r n
  have haa := real_root_gt_neg_one s a hc.left_fixed
  have hsum := actual_inverse_sum_of_limit s b r hs hs1 hc.right_pos hc.right_fixed hlim'
  have hK := inverseKoenigs_negative_between_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb
  have hslit : -inverseKoenigs s b r∈Complex.slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp only [Complex.neg_re]; linarith [hK.2]))
  have hRG : ∀ k, (inverseOrbit s r k).im=0 ∧ a<(inverseOrbit s r k).re ∧ (inverseOrbit s r k).re<b := by
    intro k
    simpa only [inverseOrbit_eq_iterate] using real_between_inverse_orbit s a b r (by linarith) haa hc.left_fixed hc.right_fixed har hrb k
  have hstep : ∀ k, lensModel s a b θ (e₁ s) (e₂ s) (inverseOrbit s r (k+1))-
      lensModel s a b θ (e₁ s) (e₂ s) (inverseOrbit s r k)+1=
      -descendedTerm A B Γ 2 (inverseOrbit s r (k+1)) s 0 := by
    intro k
    have he : inverseOrbit s r k=((inverseOrbit s r k).re:ℂ) := by apply Complex.ext <;> simp [(hRG k).1]
    have hh := (lensControl_real_steps e₁ e₂ A B Γ s a b θ Y η M P _ (by linarith) hc (hRG k).2.1 (hRG k).2.2).2
    rw [←he] at hh
    simpa only [inverseOrbit_succ] using hh
  exact tendsto_nhds_unique (physicalRepelling_orbit_limit A B Γ s a b θ (e₁ s) (e₂ s) r hstep hd.2.1)
    (inverse_model_orbit_limit s a b θ r (e₁ s) (e₂ s) hs hs1 hc.right_pos hc.theta_pos hc.theta_actual haa har hrb
      hc.left_fixed hc.right_fixed hlim hsum hslit)

end Kneser.InverseLensKoenigsIdentification
end
