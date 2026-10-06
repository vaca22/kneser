import Kneser.ActualKoenigsEntryRealPhase
import Kneser.ActualBilateralGrowingLens
import Kneser.GrowingLensEntry

/-! The exact half-period phase for the actual growing lens and any real
normalization anchor to the left of the attracting root. All orbit limits
and Koenigs sums are derived from the genuine dynamics. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Kneser.ActualKoenigsGlobalRealPhase
open Set Metric Complex Filter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualKoenigsRealPhase Kneser.ActualKoenigsEntryRealPhase
open Kneser.RealLensMidline Kneser.RealExponentialPetal Kneser.ActualLensGeometry
open Kneser.GrowingBandGeometry Kneser.GrowingLensEntry
open Kneser.PreparedActualFirstOrder Kneser.ActualBilateralGrowingLens
open Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

theorem real_root_gt_neg_one (s a : ℝ) (hfa : unfolding s a=(a:ℂ)) : -1<a := by
  have hr : realStep s a=a := by
    exact_mod_cast ((unfolding_ofReal s a).symm.trans hfa)
  have hp := Real.exp_pos (-s+(1-s)*a)
  unfold realStep at hr
  linarith

theorem real_left_step (s a r : ℝ) (hs1 : s<1) (ha : -1<a)
    (hfa : unfolding s a=(a:ℂ)) (hr : r<a) :
    realStep s r<a ∧ a-realStep s r≤multiplier s a*(a-r) := by
  have hra : realStep s a=a := by exact_mod_cast ((unfolding_ofReal s a).symm.trans hfa)
  have hh : realStep s r<realStep s a := by
    unfold realStep
    exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by nlinarith)) _
  have he : Real.exp (-s+(1-s)*r)=(a+1)*Real.exp ((1-s)*(r-a)) := by
    have harg : -s+(1-s)*r=(-s+(1-s)*a)+(1-s)*(r-a) := by ring
    rw [harg,Real.exp_add]
    have hroot : Real.exp (-s+(1-s)*a)=a+1 := by unfold realStep at hra; linarith
    rw [hroot]
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((1-s)*(r-a))) (by linarith : 0≤a+1)
  rw [←he] at ht
  refine ⟨by rwa [hra] at hh,?_⟩
  unfold multiplier realStep
  nlinarith

theorem real_left_orbit_distance (s a r : ℝ) (hs1 : s<1) (ha : -1<a)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0≤multiplier s a) (hr : r<a) :
    ∀ k : ℕ, (orbit (r:ℂ) s k).im=0 ∧ (orbit (r:ℂ) s k).re<a ∧
      ‖orbit (r:ℂ) s k-(a:ℂ)‖≤(a-r)*multiplier s a^k := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp,by simpa using hr,?_⟩
    simp only [orbit_zero,pow_zero,mul_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_neg (by linarith)]
    linarith
  | succ k ih =>
    have hre : orbit (r:ℂ) s k=((orbit (r:ℂ) s k).re:ℂ) := by apply Complex.ext <;> simp [ih.1]
    have hn : ‖orbit (r:ℂ) s k-(a:ℂ)‖=a-(orbit (r:ℂ) s k).re := by
      rw [hre,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith [ih.2.1])]
      simp
    have hstep := real_left_step s a (orbit (r:ℂ) s k).re hs1 ha hfa ih.2.1
    rw [orbit_succ,hre,unfolding_ofReal]
    refine ⟨by simp,by simpa using hstep.1,?_⟩
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith [hstep.1])]
    have hm := mul_le_mul_of_nonneg_left ih.2.2 hμ
    rw [hn] at hm
    rw [pow_succ]
    nlinarith

theorem real_left_orbit_limit (s a r : ℝ) (hs1 : s<1) (ha : -1<a)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0≤multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r<a) : Tendsto (fun k => orbit (r:ℂ) s k) atTop (𝓝 (a:ℂ)) := by
  have hb := real_left_orbit_distance s a r hs1 ha hfa hμ hr
  have ht : Tendsto (fun k : ℕ => (a-r)*multiplier s a^k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ hμ1).const_mul (a-r)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hb k).2.2) ht)

/-- No Koenigs summability, convergence, reality or phase premise is
needed. The witnesses are the actual bilateral growing lens roots. -/
theorem exists_actual_growing_lens_real_phase
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        a<0 ∧ 0<b ∧ 0<θ ∧ unfolding s a=(a:ℂ) ∧ unfolding s b=(b:ℂ) ∧
        θ=-Real.log (multiplier s a) ∧ θ*Y≤Real.pi/2 ∧
        ∀ r r₀ : ℝ, a<r → r<b → r₀<a →
          Summable (fun k => ‖increment s a (r:ℂ) k‖) ∧
          Summable (fun k => ‖increment s a (r₀:ℂ) k‖) ∧
          (koenigsValue s a (r:ℂ)).im=0 ∧ 0<(koenigsValue s a (r:ℂ)).re ∧
          (koenigsValue s a (r₀:ℂ)).im=0 ∧ (koenigsValue s a (r₀:ℂ)).re<0 ∧
          (normalizedUpperTime s a r r₀).im=Real.pi/θ ∧
          Complex.exp ((Real.log (multiplier s a):ℂ)*normalizedUpperTime s a r r₀)=
            koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ) ∧
          normalizedUpperTime s a (realStep s r) r₀=normalizedUpperTime s a r r₀+1 := by
  obtain ⟨Y,s₀,hY,hs₀,hs₀h,hlens⟩ := exists_actual_bilateral_growing_lens U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,ha0,hb,hθ,hfa,hfb,hθeq,hθY,hstates⟩ := hlens s hs hss
  have hs1 : s<1 := by linarith [hss.trans_le hs₀h]
  have ha := real_root_gt_neg_one s a hfa
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith
  refine ⟨a,b,θ,ha0,hb,hθ,hfa,hfb,hθeq,hθY,?_⟩
  intro r r₀ har hrb hr₀
  let Z := bandTime a b θ (r:ℂ)
  have hZim : Z.im=Real.pi/θ := bandTime_real_between a b θ r har hrb
  have hl : Y<Real.pi/θ := (lt_div_iff₀ hθ).mpr (by nlinarith [Real.pi_pos])
  have hZ : Z∈strip θ Y := by
    change Y<Z.im ∧ Z.im<height θ-Y
    rw [hZim]
    unfold height
    constructor
    · exact hl
    · have hp : 2*Real.pi/θ=2*(Real.pi/θ) := by ring
      rw [hp]
      linarith
  have hchart : bandChart a b θ Z=(r:ℂ) := bandChart_bandTime a b θ r
    (by linarith) (ne_of_gt hθ) (by exact_mod_cast ne_of_gt har) (by exact_mod_cast ne_of_lt hrb)
  have hsdata := hstates Z hZ
  have hroots : ∀ k, orbit (r:ℂ) s k≠(a:ℂ) ∧ orbit (r:ℂ) s k≠(b:ℂ) := by
    intro k
    obtain ⟨hfka,hfkb,_hgka,_hgkb,_htf,_htg,_hstep,_hgstep⟩ := hsdata.2.2.2.2 k
    rw [hchart] at hfka hfkb
    exact ⟨hfka,hfkb⟩
  have hstep : ∀ k, (bandTime a b θ (orbit (r:ℂ) s k)).re+3/4≤
      (bandTime a b θ (orbit (r:ℂ) s (k+1))).re := by
    intro k
    obtain ⟨_hfka,_hfkb,_hgka,_hgkb,_htf,_htg,hstep,_hgstep⟩ := hsdata.2.2.2.2 k
    rwa [hchart] at hstep
  have hLr := true_forward_orbit_tendsto_root (r:ℂ) s a b θ (by linarith) hθ hroots hstep
  have hL₀ := real_left_orbit_limit s a r₀ hs1 ha hfa hμ.le hμ1 hr₀
  have hSr := actual_koenigs_sum_of_orbit_limit s a r hs.le hs1 ha ha0.le hfa hμ hμ1 hLr
  have hS₀ := actual_koenigs_sum_of_orbit_limit s a r₀ hs.le hs1 ha ha0.le hfa hμ hμ1 hL₀
  have hrK := koenigsValue_positive_between s a b r hs.le hs1 ha ha0.le hfa hfb hμ hμ1 hSr hLr har hrb
  have h₀K := koenigsValue_negative_left s a r₀ hs.le hs1 ha ha0.le hfa hμ hμ1 hS₀ hL₀ hr₀
  have hKr : koenigsValue s a (r:ℂ)≠0 := by intro he; rw [he] at hrK; simpa using hrK.2
  have hK₀ : koenigsValue s a (r₀:ℂ)≠0 := by intro he; rw [he] at h₀K; simpa using h₀K.2
  refine ⟨hSr,hS₀,hrK.1,hrK.2,h₀K.1,h₀K.2,?_,
    normalizedUpperTime_exponential s a r r₀ hμ hμ1 hKr hK₀,
    normalizedUpperTime_real_step_abel s a r r₀ hμ hμ1 hSr hKr hK₀⟩
  rw [hθeq]
  exact normalizedUpperTime_half_height s a r r₀ hμ hμ1 hrK h₀K

end Kneser.ActualKoenigsGlobalRealPhase
end
