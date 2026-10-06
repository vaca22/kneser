import Kneser.ActualGrowingRealPhases

/-! The actual forward growing-lens series is the genuine normalized
Koenigs logarithm, with the explicitly derived residue constant. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.LensKoenigsIdentification
open Set Metric Filter Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsAbel
open Kneser.ActualLensModel Kneser.GrowingBandGeometry Kneser.ApolloniusGeometry
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualKoenigsRealPhase Kneser.ActualKoenigsUpperBranch
open Kneser.EvenPreparedOrbitDiscs Kneser.RealLensMidline Kneser.GrowingLensKoenigs
open scoped Topology BigOperators

def intervalKoenigsTime (s a : ℝ) (u : ℂ) : ℂ :=
  Complex.log (koenigsValue s a u)/(Real.log (multiplier s a):ℂ)

theorem log_positive_real_div (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Complex.log ((x:ℂ)/(y:ℂ))=Complex.log (x:ℂ)-Complex.log (y:ℂ) := by
  rw [←Complex.ofReal_div,←Complex.ofReal_log (div_pos hx hy).le,
    Real.log_div (ne_of_gt hx) (ne_of_gt hy),Complex.ofReal_sub,
    Complex.ofReal_log hx.le,Complex.ofReal_log hy.le]

theorem lensModel_real_formula (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hθ : 0<θ) (hθeq : θ= -Real.log (multiplier s a)) (har : a<r) (hrb : r<b) :
    lensModel s a b θ e₁ e₂ r=
      Complex.log ((r:ℂ)-(a:ℂ))/(Real.log (multiplier s a):ℂ)+
      Complex.log ((b:ℂ)-(r:ℂ))/(Real.log (multiplier s b):ℂ)+
      e₁*r+e₂*(r:ℂ)^2+(Real.pi:ℂ)*I/(θ:ℂ) := by
  have hq : -crossRatio a b (r:ℂ)=((r-a:ℝ):ℂ)/((b-r:ℝ):ℂ) := by
    unfold crossRatio
    push_cast
    rw [show (r:ℂ)-(b:ℂ)= -((b:ℂ)-(r:ℂ)) by ring,div_neg_eq_neg_div,neg_neg]
  have hl := log_positive_real_div (r-a) (b-r) (by linarith) (by linarith)
  have ht : (θ:ℂ)≠0 := by exact_mod_cast (ne_of_gt hθ)
  have hla : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast (by linarith : Real.log (multiplier s a)≠0)
  unfold lensModel bandTime residueSum
  rw [hq,hl,hθeq]
  push_cast
  field_simp
  ring

theorem interval_model_orbit_limit (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) (hθ : 0<θ)
    (hθeq : θ= -Real.log (multiplier s a)) (hs1 : s<1) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (horbit : Tendsto (orbit r s) atTop (𝓝 (a:ℂ)))
    (hsum : Summable (fun k => ‖increment s a r k‖))
    (hslit : koenigsValue s a r∈Complex.slitPlane) :
    Tendsto (fun n : ℕ => lensModel s a b θ e₁ e₂ (orbit r s n)-(n:ℂ)) atTop
      (𝓝 (intervalKoenigsTime s a r+modelConstant s a b e₁ e₂+(Real.pi:ℂ)*I/(θ:ℂ))) := by
  have hμc : (multiplier s a:ℂ)≠0 := by exact_mod_cast (ne_of_gt hμ)
  have hlc : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast (ne_of_lt (Real.log_neg hμ hμ1))
  have happrox := tendsto_approximation s a r hsum
  have haLog := happrox.clog hslit
  have hbslit : (b:ℂ)-(a:ℂ)∈Complex.slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hbLog := (tendsto_const_nhds (x:=(b:ℂ))).sub horbit |>.clog hbslit
  have ht := (((haLog.div_const (Real.log (multiplier s a):ℂ)).add
    (hbLog.div_const (Real.log (multiplier s b):ℂ))).add (horbit.const_mul e₁)).add
      ((horbit.pow 2).const_mul e₂) |>.add_const ((Real.pi:ℂ)*I/(θ:ℂ))
  have ht' : Tendsto (fun n : ℕ =>
    Complex.log (approximation s a r n)/(Real.log (multiplier s a):ℂ)+
      Complex.log ((b:ℂ)-orbit r s n)/(Real.log (multiplier s b):ℂ)+
      e₁*orbit r s n+e₂*(orbit r s n)^2+(Real.pi:ℂ)*I/(θ:ℂ)) atTop
      (𝓝 (intervalKoenigsTime s a r+modelConstant s a b e₁ e₂+(Real.pi:ℂ)*I/(θ:ℂ))) := by
    convert ht using 1
    dsimp [intervalKoenigsTime,modelConstant]
    congr 1
    ring
  apply ht'.congr'
  filter_upwards [happrox.eventually_ne (slitPlane_ne_zero hslit)] with n hn
  have hp : orbit r s n-(a:ℂ)=(multiplier s a:ℂ)^n*approximation s a r n := by
    unfold approximation
    field_simp
  have hpReal : (multiplier s a:ℂ)^n=((multiplier s a^n:ℝ):ℂ) := by simp
  have hlog : Complex.log (orbit r s n-(a:ℂ))=
      (n:ℂ)*(Real.log (multiplier s a):ℂ)+Complex.log (approximation s a r n) := by
    rw [hp,hpReal,Complex.log_ofReal_mul (pow_pos hμ n) hn,Real.log_pow]
    push_cast
    rfl
  have hreal := real_between_orbit s a b r hs1 hfa hfb har hrb n
  have he : orbit r s n=((orbit r s n).re:ℂ) := by apply Complex.ext <;> simp [hreal.1]
  have hm := lensModel_real_formula s a b θ (orbit r s n).re e₁ e₂ hθ hθeq hreal.2.1 hreal.2.2
  rw [←he] at hm
  rw [hm,hlog]
  field_simp
  ring

theorem forward_residual_telescope
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ, lensModel s a b θ e₁ e₂ (orbit u s (k+1))-
      lensModel s a b θ e₁ e₂ (orbit u s k)-1=descendedTerm A B Γ 2 u s k)
    (n : ℕ) :
    lensModel s a b θ e₁ e₂ u+∑ k∈Finset.range n,descendedTerm A B Γ 2 u s k=
      lensModel s a b θ e₁ e₂ (orbit u s n)-(n:ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,←add_assoc,ih]
    have h := hstep n
    push_cast
    linear_combination -h

theorem physicalAttracting_orbit_limit
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ, lensModel s a b θ e₁ e₂ (orbit u s (k+1))-
      lensModel s a b θ e₁ e₂ (orbit u s k)-1=descendedTerm A B Γ 2 u s k)
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖)) :
    Tendsto (fun n : ℕ => lensModel s a b θ e₁ e₂ (orbit u s n)-(n:ℂ)) atTop
      (𝓝 (physicalAttracting A B Γ s a b θ e₁ e₂ u)) := by
  have ht := (tendsto_const_nhds (x:=lensModel s a b θ e₁ e₂ u)).add hsum.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall (forward_residual_telescope A B Γ s a b θ e₁ e₂ u hstep))

/-- The real midline identity is derived from actual orbits and true
preparation. No equality to a Koenigs map is an input. -/
theorem physicalAttracting_eq_koenigs_real_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    physicalAttracting A B Γ s a b θ (e₁ s) (e₂ s) r=
      intervalKoenigsTime s a r+modelConstant s a b (e₁ s) (e₂ s)+(Real.pi:ℂ)*I/(θ:ℂ) := by
  obtain ⟨hZ,hchart⟩ := interval_source a b θ Y r hc.theta_pos hc.width har hrb
  have hd := hc.true_orbits (bandTime a b θ r) hZ
  rw [hchart] at hd
  have hlim := lensControl_forward_limit e₁ e₂ A B Γ s a b θ Y η M P hc r ⟨_,hZ,hchart⟩
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hsum := actual_koenigs_sum_of_orbit_limit s a r hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hlim
  have hK := koenigsValue_positive_between s a b r hs.le hs1 ha hc.left_neg.le hc.left_fixed hc.right_fixed hμ hμ1 hsum hlim har hrb
  have hslit : koenigsValue s a r∈Complex.slitPlane := mem_slitPlane_iff.mpr (Or.inl hK.2)
  have hRF := real_between_orbit s a b r hs1 hc.left_fixed hc.right_fixed har hrb
  have hstep : ∀ k, lensModel s a b θ (e₁ s) (e₂ s) (orbit r s (k+1))-
      lensModel s a b θ (e₁ s) (e₂ s) (orbit r s k)-1=descendedTerm A B Γ 2 r s k := by
    intro k
    have he : orbit r s k=((orbit r s k).re:ℂ) := by apply Complex.ext <;> simp [(hRF k).1]
    have hh := (lensControl_real_steps e₁ e₂ A B Γ s a b θ Y η M P _ hs1 hc (hRF k).2.1 (hRF k).2.2).1
    rw [←he] at hh
    simpa only [orbit_succ,Kneser.ActualLensDynamics.descendedTerm_at_orbit] using hh
  exact tendsto_nhds_unique (physicalAttracting_orbit_limit A B Γ s a b θ (e₁ s) (e₂ s) r hstep hd.1)
    (interval_model_orbit_limit s a b θ r (e₁ s) (e₂ s) hμ hμ1 hc.theta_pos hc.theta_actual hs1 har hrb hc.left_fixed hc.right_fixed hlim hsum hslit)

end Kneser.LensKoenigsIdentification
end
