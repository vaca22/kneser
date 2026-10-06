import Kneser.ActualKoenigsGlobalRealPhase

/-! A genuine holomorphic upper Koenigs logarithm. Its real interval
restriction has the exact half-period phase supplied by the actual orbit,
and its exponential is the normalized true Koenigs ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Kneser.ActualKoenigsUpperBranch
open Set Metric Complex Filter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.PositiveKoenigsPetal Kneser.RealExponentialPetal Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

def upperTime (s a r₀ : ℝ) (u : ℂ) : ℂ :=
  (Complex.log (koenigsValue s a u)-Complex.log (-koenigsValue s a (r₀:ℂ))-
    (Real.pi:ℂ)*I)/(Real.log (multiplier s a):ℂ)

theorem orbit_limit_of_koenigs_sum (s a : ℝ) (u : ℂ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hsum : Summable (fun k => ‖increment s a u k‖)) :
    Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ)) := by
  have ht : Tendsto (fun k : ℕ => multiplier s a^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hμ.le hμ1
  have htc : Tendsto (fun k : ℕ => (multiplier s a:ℂ)^k) atTop (𝓝 0) := by
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    change Tendsto (fun k : ℕ => ((multiplier s a^k:ℝ):ℂ)) atTop (𝓝 (0:ℂ)) at hc
    exact hc.congr' (Eventually.of_forall fun k => by norm_cast)
  have hl := htc.mul (tendsto_approximation s a u hsum)
  have hμc : (multiplier s a:ℂ)≠0 := by exact_mod_cast ne_of_gt hμ
  have he : ∀ k : ℕ, (multiplier s a:ℂ)^k*approximation s a u k=orbit u s k-(a:ℂ) := by
    intro k
    simp only [approximation,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hμc),one_mul]
  have hsub : Tendsto (fun k => orbit u s k-(a:ℂ)) atTop (𝓝 0) := by
    simpa only [he,zero_mul] using hl
  simpa using hsub.add_const (a:ℂ)

/-- Holomorphy of the true Koenigs sum follows from actual finite entry
into its local construction; no neighborhood summability input remains. -/
theorem analyticAt_koenigsValue_of_true_limit (s a : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ))) :
    AnalyticAt ℂ (koenigsValue s a) u := by
  obtain ⟨δ,hδ,_hhol,_hz,_hd,hlocal⟩ :=
    Kneser.PositiveLocalKoenigs.exists_actual_local_koenigs s a hs hs1 ha ha0 hfa hμ hμ1
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds (a:ℂ) hδ)).exists
  have hfinite : ContinuousAt (fun v : ℂ => orbit v s N) u :=
    (Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s N u).continuousAt
  have hentry : ∀ᶠ v : ℂ in 𝓝 u, orbit v s N∈ball (a:ℂ) δ :=
    hfinite.eventually (isOpen_ball.mem_nhds hN)
  have hsums : ∀ᶠ v : ℂ in 𝓝 u, Summable (fun k => ‖increment s a v k‖) := by
    filter_upwards [hentry] with v hv
    exact summable_increment_from_entry s a v N (ne_of_gt hμ) (hlocal _ hv).1
  exact analyticAt_koenigsValue_of_actual_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim hsums

theorem upperTime_analyticAt (s a r₀ : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ)))
    (hslit : koenigsValue s a u∈Complex.slitPlane) :
    AnalyticAt ℂ (upperTime s a r₀) u := by
  have hk := analyticAt_koenigsValue_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim
  exact ((hk.clog hslit).sub analyticAt_const |>.sub analyticAt_const).div_const

theorem upperTime_half_height (s a r r₀ : ℝ)
    (hr : (koenigsValue s a (r:ℂ)).im=0 ∧ 0<(koenigsValue s a (r:ℂ)).re)
    (hr₀ : (koenigsValue s a (r₀:ℂ)).im=0 ∧ (koenigsValue s a (r₀:ℂ)).re<0) :
    (upperTime s a r₀ r).im=Real.pi/(-Real.log (multiplier s a)) := by
  have he : koenigsValue s a (r:ℂ)=((koenigsValue s a (r:ℂ)).re:ℂ) := by apply Complex.ext <;> simp [hr.1]
  have he₀ : -koenigsValue s a (r₀:ℂ)=(-(koenigsValue s a (r₀:ℂ)).re:ℂ) := by apply Complex.ext <;> simp [hr₀.1]
  have har : Complex.arg (koenigsValue s a (r:ℂ))=0 := by
    rw [he]
    exact Complex.arg_ofReal_of_nonneg hr.2.le
  have har₀ : Complex.arg (-koenigsValue s a (r₀:ℂ))=0 := by
    rw [he₀]
    rw [←Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_nonneg (neg_nonneg.mpr hr₀.2.le)
  simp only [upperTime,Complex.div_ofReal_im,Complex.sub_im,Complex.log_im,har,har₀,
    Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,mul_one,zero_add,sub_self,zero_sub]
  ring

theorem upperTime_exponential (s a r₀ : ℝ) (u : ℂ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hK : koenigsValue s a u≠0) (hK₀ : koenigsValue s a (r₀:ℂ)≠0) :
    Complex.exp ((Real.log (multiplier s a):ℂ)*upperTime s a r₀ u)=
      koenigsValue s a u/koenigsValue s a (r₀:ℂ) := by
  have hlog : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  have he : (Real.log (multiplier s a):ℂ)*upperTime s a r₀ u=
    Complex.log (koenigsValue s a u)-Complex.log (-koenigsValue s a (r₀:ℂ))-(Real.pi:ℂ)*I := by
    unfold upperTime
    field_simp
  rw [he,Complex.exp_sub,Complex.exp_sub,Complex.exp_log hK,
    Complex.exp_log (neg_ne_zero.mpr hK₀),Complex.exp_pi_mul_I]
  field_simp

theorem upperTime_abel (s a r₀ : ℝ) (u : ℂ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hsum : Summable (fun k => ‖increment s a u k‖)) (hK : koenigsValue s a u≠0) :
    upperTime s a r₀ (unfolding s u)=upperTime s a r₀ u+1 := by
  have hlog : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  unfold upperTime
  rw [koenigsValue_functional_eq s a u (ne_of_gt hμ) hsum,Complex.log_ofReal_mul hμ hK]
  field_simp
  ring

/-- A holomorphic actual upper branch, exact true normalization and exact
half-height for every real point between the actual split roots. -/
theorem exists_actual_analytic_upper_real_phase
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        a<0 ∧ 0<b ∧ 0<θ ∧ unfolding s a=(a:ℂ) ∧ unfolding s b=(b:ℂ) ∧
        θ=-Real.log (multiplier s a) ∧ θ*Y≤Real.pi/2 ∧
        ∀ r r₀ : ℝ, a<r → r<b → r₀<a →
          AnalyticAt ℂ (upperTime s a r₀) (r:ℂ) ∧
          (upperTime s a r₀ r).im=Real.pi/θ ∧
          Complex.exp ((Real.log (multiplier s a):ℂ)*upperTime s a r₀ r)=
            koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ) ∧
          upperTime s a r₀ (unfolding s r)=upperTime s a r₀ r+1 := by
  obtain ⟨Y,s₀,hY,hs₀,hs₀h,hphase⟩ := exists_actual_growing_lens_real_phase U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,ha0,hb,hθ,hfa,hfb,hθeq,hθY,hrdata⟩ := hphase s hs hss
  have hs1 : s<1 := by linarith [hss.trans_le hs₀h]
  have ha := real_root_gt_neg_one s a hfa
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith
  refine ⟨a,b,θ,ha0,hb,hθ,hfa,hfb,hθeq,hθY,?_⟩
  intro r r₀ har hrb hr₀
  obtain ⟨hSr,_hS₀,him,hpos,him₀,hneg,_hphase,_hexp,_habel⟩ := hrdata r r₀ har hrb hr₀
  have hLr := orbit_limit_of_koenigs_sum s a r hμ hμ1 hSr
  have hslit : koenigsValue s a (r:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hpos)
  have hKr : koenigsValue s a (r:ℂ)≠0 := by intro he; rw [he] at hpos; simpa using hpos
  have hK₀ : koenigsValue s a (r₀:ℂ)≠0 := by intro he; rw [he] at hneg; simpa using hneg
  refine ⟨upperTime_analyticAt s a r₀ r hs.le hs1 ha ha0.le hfa hμ hμ1 hLr hslit,?_,
    upperTime_exponential s a r₀ r hμ hμ1 hKr hK₀,upperTime_abel s a r₀ r hμ hμ1 hSr hKr⟩
  rw [hθeq]
  exact upperTime_half_height s a r r₀ ⟨him,hpos⟩ ⟨him₀,hneg⟩

end Kneser.ActualKoenigsUpperBranch
end
