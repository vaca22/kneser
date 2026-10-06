import Kneser.PositiveKoenigsPetal
import Kneser.RealLensMidline

/-! Real signs and the exact half-period branch follow from the actual
normalized Koenigs orbit. Polynomial preparation reality is unnecessary. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualKoenigsRealPhase
open Set Metric Complex Filter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.PositiveKoenigsAbel Kneser.RealLensMidline Kneser.RealExponentialPetal
open Kneser.ApolloniusGeometry
open scoped Topology

theorem real_orbit_im_zero (s r : ℝ) (n : ℕ) : (orbit (r:ℂ) (s:ℂ) n).im=0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : orbit (r:ℂ) (s:ℂ) n=((orbit (r:ℂ) (s:ℂ) n).re:ℂ) := by
      apply Complex.ext <;> simp [ih]
    rw [orbit_succ,he,unfolding_ofReal]
    simp

theorem koenigsValue_real (s a r : ℝ)
    (hsum : Summable (fun n => ‖increment s a (r:ℂ) n‖)) :
    (koenigsValue s a (r:ℂ)).im=0 := by
  have hap := (Complex.continuous_im.continuousAt.tendsto).comp (tendsto_approximation s a (r:ℂ) hsum)
  have he : ∀ n : ℕ, (approximation s a (r:ℂ) n).im=0 := by
    intro n
    unfold approximation
    have ht : ((multiplier s a:ℂ)^n)⁻¹=(((multiplier s a^n)⁻¹:ℝ):ℂ) := by norm_cast
    rw [ht]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_im,
      real_orbit_im_zero,sub_zero,mul_zero,zero_mul,add_zero]
  exact tendsto_nhds_unique hap ((tendsto_const_nhds (x:=(0:ℝ))).congr' (Eventually.of_forall fun n => (he n).symm))

theorem koenigsValue_positive_between (s a b r : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hsum : Summable (fun n => ‖increment s a (r:ℂ) n‖))
    (horbit : Tendsto (fun n => orbit (r:ℂ) (s:ℂ) n) atTop (𝓝 (a:ℂ)))
    (har : a<r) (hrb : r<b) :
    (koenigsValue s a (r:ℂ)).im=0 ∧ 0<(koenigsValue s a (r:ℂ)).re := by
  obtain ⟨_δ,_hδ,_hhol,_hzero,hder,_hrest⟩ := exists_actual_local_koenigs s a hs hs1 ha ha0 hfa hμ hμ1
  have hnear : ∀ᶠ v : ℂ in 𝓝 (a:ℂ), v≠(a:ℂ) → koenigsValue s a v≠0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using
      eventually_nhdsWithin_iff.mp (hder.eventually_ne (c:=(0:ℂ)) (by norm_num))
  have hbetween := real_between_orbit s a b r hs1 hfa hfb har hrb
  obtain ⟨N,hN⟩ := (horbit.eventually hnear).exists
  have hentry : koenigsValue s a (orbit (r:ℂ) (s:ℂ) N)≠0 := hN (by
    intro he
    have hh := (hbetween N).2.1
    rw [he] at hh
    simp at hh)
  have hK : koenigsValue s a (r:ℂ)≠0 := by
    intro he
    rw [koenigsValue_iterate s a (r:ℂ) (ne_of_gt hμ) hsum N,he,mul_zero] at hentry
    exact hentry rfl
  have hnonneg : 0≤(koenigsValue s a (r:ℂ)).re := by
    apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_approximation s a (r:ℂ) hsum))
    apply Eventually.of_forall
    intro n
    change 0≤(approximation s a (r:ℂ) n).re
    have he : (approximation s a (r:ℂ) n).re=(multiplier s a^n)⁻¹*((orbit (r:ℂ) (s:ℂ) n).re-a) := by
      unfold approximation
      have ht : ((multiplier s a:ℂ)^n)⁻¹=(((multiplier s a^n)⁻¹:ℝ):ℂ) := by norm_cast
      rw [ht]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Complex.sub_re]
      simp
    rw [he]
    exact mul_nonneg (by positivity) (by linarith [(hbetween n).2.1])
  have hreal := koenigsValue_real s a r hsum
  refine ⟨hreal,lt_of_le_of_ne hnonneg ?_⟩
  intro he
  exact hK (Complex.ext he.symm hreal)

theorem koenigsValue_negative_left (s a r : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hsum : Summable (fun n => ‖increment s a (r:ℂ) n‖))
    (horbit : Tendsto (fun n => orbit (r:ℂ) (s:ℂ) n) atTop (𝓝 (a:ℂ)))
    (hr : r<a) : (koenigsValue s a (r:ℂ)).im=0 ∧ (koenigsValue s a (r:ℂ)).re<0 := by
  have hreal := koenigsValue_real s a r hsum
  have hb := (actual_koenigs_branch s a (r:ℂ) hs hs1 ha ha0 hfa hμ hμ1 hsum horbit (by simpa using hr)).2
  have hh := Complex.mem_slitPlane_iff.mp hb
  have hpos : 0<(-koenigsValue s a (r:ℂ)).re := hh.resolve_right (by simpa only [Complex.neg_im,hreal,neg_zero] using (not_ne_iff.mpr rfl : ¬(0:ℝ)≠0))
  exact ⟨hreal,by simpa only [Complex.neg_re] using neg_pos.mp hpos⟩

def normalizedUpperTime (s a r r₀ : ℝ) : ℂ :=
  (Complex.log (koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ))-2*(Real.pi:ℂ)*I)/(Real.log (multiplier s a):ℂ)

theorem normalizedUpperTime_half_height (s a r r₀ : ℝ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : (koenigsValue s a (r:ℂ)).im=0 ∧ 0<(koenigsValue s a (r:ℂ)).re)
    (hr₀ : (koenigsValue s a (r₀:ℂ)).im=0 ∧ (koenigsValue s a (r₀:ℂ)).re<0) :
    (normalizedUpperTime s a r r₀).im=Real.pi/(-Real.log (multiplier s a)) := by
  have he : koenigsValue s a (r:ℂ)=((koenigsValue s a (r:ℂ)).re:ℂ) := by apply Complex.ext <;> simp [hr.1]
  have he₀ : koenigsValue s a (r₀:ℂ)=((koenigsValue s a (r₀:ℂ)).re:ℂ) := by apply Complex.ext <;> simp [hr₀.1]
  have harg : Complex.arg (koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ))=Real.pi := by
    rw [he,he₀,←Complex.ofReal_div]
    exact Complex.arg_ofReal_of_neg (div_neg_of_pos_of_neg hr.2 hr₀.2)
  simp only [normalizedUpperTime,Complex.div_ofReal_im,Complex.sub_im,Complex.log_im,harg,
    Complex.mul_im,Complex.ofReal_im,zero_mul,Complex.ofReal_re,Complex.I_re,mul_zero,Complex.I_im,mul_one,zero_add]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num
  ring

/-- Exact phase from genuine orbit sums and limits, with no real
polynomial coefficient or half-period assumption. -/
theorem normalizedUpperTime_actual_phase (s a b r r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hSr : Summable (fun n => ‖increment s a (r:ℂ) n‖))
    (hS₀ : Summable (fun n => ‖increment s a (r₀:ℂ) n‖))
    (hLr : Tendsto (fun n => orbit (r:ℂ) (s:ℂ) n) atTop (𝓝 (a:ℂ)))
    (hL₀ : Tendsto (fun n => orbit (r₀:ℂ) (s:ℂ) n) atTop (𝓝 (a:ℂ)))
    (har : a<r) (hrb : r<b) (hr₀ : r₀<a) :
    (normalizedUpperTime s a r r₀).im=Real.pi/(-Real.log (multiplier s a)) :=
  normalizedUpperTime_half_height s a r r₀ hμ hμ1
    (koenigsValue_positive_between s a b r hs hs1 ha ha0 hfa hfb hμ hμ1 hSr hLr har hrb)
    (koenigsValue_negative_left s a r₀ hs hs1 ha ha0 hfa hμ hμ1 hS₀ hL₀ hr₀)

theorem normalizedUpperTime_exponential (s a r r₀ : ℝ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : koenigsValue s a (r:ℂ)≠0) (hr₀ : koenigsValue s a (r₀:ℂ)≠0) :
    Complex.exp ((Real.log (multiplier s a):ℂ)*normalizedUpperTime s a r r₀)=
      koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ) := by
  have hn : (Real.log (multiplier s a):ℂ)≠0 := by
    exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  have he : (Real.log (multiplier s a):ℂ)*normalizedUpperTime s a r r₀=
      Complex.log (koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ))-2*(Real.pi:ℂ)*I := by
    dsimp [normalizedUpperTime]
    field_simp
  rw [he,Complex.exp_sub,Complex.exp_log (div_ne_zero hr hr₀)]
  have hexp : Complex.exp (2*(Real.pi:ℂ)*I)=1 := Complex.exp_two_pi_mul_I
  rw [hexp,div_one]

theorem normalizedUpperTime_real_step_abel (s a r r₀ : ℝ)
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hsum : Summable (fun n => ‖increment s a (r:ℂ) n‖))
    (hr : koenigsValue s a (r:ℂ)≠0) (hr₀ : koenigsValue s a (r₀:ℂ)≠0) :
    normalizedUpperTime s a (realStep s r) r₀=normalizedUpperTime s a r r₀+1 := by
  have hn : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  have hfunc := koenigsValue_functional_eq s a (r:ℂ) (ne_of_gt hμ) hsum
  rw [unfolding_ofReal] at hfunc
  have hlog : Complex.log (koenigsValue s a (realStep s r:ℂ)/koenigsValue s a (r₀:ℂ))=
      (Real.log (multiplier s a):ℂ)+Complex.log (koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ)) := by
    rw [hfunc,mul_div_assoc]
    exact Complex.log_ofReal_mul hμ (div_ne_zero hr hr₀)
  dsimp [normalizedUpperTime]
  rw [hlog]
  field_simp
  ring

end Kneser.ActualKoenigsRealPhase
end
