import Kneser.ActualRegularTimeHalfPlane
import Kneser.GateFourierHeight

/-! The principal logarithmic lift of the genuine physical superfunction
on an entire actual horizontal period line. Its integral is exactly the
Fourier integral of the same constructed sewing coordinate; the integer
translation is proved from actual periodicity. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Kneser.ActualRegularTimeLift
open Filter Set Metric Complex MeasureTheory
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualRegularKoenigsInverse Kneser.ActualRegularTimeHalfPlane
open Kneser.HolomorphicInjectiveInverse Kneser.ActualHolomorphicGrowingLens
open Kneser.WeightedFourier Kneser.FourierSewing Kneser.GateFourierDerivative
open Kneser.GateFourierHeight Kneser.GrowingBandGeometry
open scoped Topology Interval

def principalKoenigsLift (s a r₀ : ℝ) (u : ℂ) : ℂ :=
  Complex.log (koenigsValue s a u/koenigsValue s a r₀)/(Real.log (multiplier s a):ℂ)

theorem real_anchor_koenigs_ne_zero (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r₀<a) (hd : a-r₀<1) : koenigsValue s a r₀≠0 := by
  obtain ⟨hi,_⟩ := koenigs_unit_basin_data s a hs hs1 ha ha0 hfa hμ hμ1
  have hb := real_left_mem_unit_basin s a r₀ hs1 ha hfa hμ hμ1 hr hd
  intro he
  have hh := hi hb (unit_basin_root s a hfa)
    (by simpa only [koenigsValue_at_root s a hfa] using he)
  have hrr : r₀=a := by exact_mod_cast hh
  linarith

theorem principal_lift_regular_inverse (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r₀<a) (hd : a-r₀<1) (w : ℂ) (hw : w∈regularTimeDomain s a r₀)
    (him : |Real.log (multiplier s a)*w.im|<Real.pi) :
    principalKoenigsLift s a r₀ (regularSuperfunction s a r₀ w)=w := by
  have hK := real_anchor_koenigs_ne_zero s a r₀ hs hs1 ha ha0 hfa hμ hμ1 hr hd
  have he := ((regular_domain_holomorphic s a r₀ hs hs1 ha ha0 hfa hμ hμ1).2.2 w hw).2
  have hlog : (Real.log (multiplier s a):ℂ)≠0 := by exact_mod_cast ne_of_lt (Real.log_neg hμ hμ1)
  have hratio : koenigsValue s a (regularSuperfunction s a r₀ w)/koenigsValue s a r₀=
      Complex.exp ((Real.log (multiplier s a):ℂ)*w) := by
    rw [he,koenigsArgument]
    field_simp
  have him₀ : ((Real.log (multiplier s a):ℂ)*w).im=Real.log (multiplier s a)*w.im := by simp
  unfold principalKoenigsLift
  rw [hratio,Complex.log_exp (by rw [him₀]; exact (abs_lt.mp him).1)
    (by rw [him₀]; exact (abs_lt.mp him).2.le)]
  field_simp

theorem sewn_real_im_bound (H h : ℝ) (P : Space) (t₀ ζ : ℂ)
    (hP : ∀n : ℤ, n<0 → P n=0) (hPn : ‖P‖≤1) (hζ : ‖ζ‖≤1)
    (hgap : 0≤H+(normalizingCentre h t₀+ζ).im) (x : ℝ) :
    |(sewnCoordinate H h P t₀ ζ (x:ℂ)).im|≤2 := by
  have hg : 0≤H+(normalizingCentre h t₀+ζ+(x:ℂ)).im := by simpa using hgap
  have he := sewnDisplacement_eq H h P t₀ ζ (x:ℂ)
  have hn : ‖ζ+evaluate H P (normalizingCentre h t₀+ζ+(x:ℂ))‖≤2 :=
    (norm_add_le _ _).trans (by linarith [(norm_evaluate_positive_le H P hP _ hg).trans hPn])
  have hh := (Complex.abs_im_le_norm (ζ+evaluate H P (normalizingCentre h t₀+ζ+(x:ℂ)))).trans hn
  have heim := congrArg Complex.im he
  simp only [sewnDisplacement,Complex.sub_im,Complex.ofReal_im,sub_zero] at heim
  rwa [←heim] at hh

theorem weighted_sewn_nat_translation (H h : ℝ) (P : Space) (t₀ ζ z : ℂ) (n : ℤ) (N : ℕ) :
    weightedDifference n (sewnCoordinate H h P t₀ ζ) ((N:ℂ)+z)=
      weightedDifference n (sewnCoordinate H h P t₀ ζ) z := by
  have hp : Function.Periodic (weightedDifference n (sewnCoordinate H h P t₀ ζ)) 1 :=
    weightedDifference_periodic n _ (sewnCoordinate_translation H h P t₀ ζ)
  simpa only [mul_one,add_comm] using hp.nat_mul N z

theorem exists_genuine_physical_lift_integral (s a r₀ H h : ℝ) (P : Space) (t₀ ζ : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r₀<a) (hd : a-r₀<1) (hlog : |Real.log (multiplier s a)|≤1)
    (hP : ∀n : ℤ, n<0 → P n=0) (hPn : ‖P‖≤1) (hζ : ‖ζ‖≤1)
    (hgap : 0≤H+(normalizingCentre h t₀+ζ).im) :
    ∃N : ℕ,
      (∀x : ℝ, 0≤x → x≤1 →
        sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))∈regularTimeDomain s a r₀ ∧
        principalKoenigsLift s a r₀
          (regularSuperfunction s a r₀ (sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))))=
            sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))) ∧
      ∀n : ℤ,
        (∫x : ℝ in (0:ℝ)..1,
          (principalKoenigsLift s a r₀
            (regularSuperfunction s a r₀ (sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))))-
              ((N:ℂ)+(x:ℂ))) * Complex.exp (-Kneser.fourierFrequency n*((N:ℂ)+(x:ℂ))))=
          gateFourierCoefficient n 0 (sewnCoordinate H h P t₀ ζ) := by
  obtain ⟨N,hN⟩ := exists_genuine_physical_period_line s a r₀ H h P t₀ ζ
    hs hs1 ha ha0 hfa hμ hμ1 hP hPn hζ hgap
  have hident : ∀x : ℝ, 0≤x → x≤1 →
      principalKoenigsLift s a r₀
        (regularSuperfunction s a r₀ (sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))))=
          sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ)) := by
    intro x hx hx1
    have him : |(sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))).im|≤2 := by
      simpa only [Complex.ofReal_add,Complex.ofReal_natCast] using sewn_real_im_bound H h P t₀ ζ hP hPn hζ hgap ((N:ℝ)+x)
    apply principal_lift_regular_inverse s a r₀ hs hs1 ha ha0 hfa hμ hμ1 hr hd _ (hN x hx hx1).1
    rw [abs_mul]
    calc
      _ ≤ 1*2 := mul_le_mul hlog him (abs_nonneg _) (by norm_num)
      _ < Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨N,(fun x hx hx1 => ⟨(hN x hx hx1).1,hident x hx hx1⟩),?_⟩
  intro n
  unfold gateFourierCoefficient gatePoint gateWeight
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Set.Icc (0:ℝ) 1 := by simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
  dsimp only [gatePoint,gateWeight]
  rw [hident x hx'.1 hx'.2]
  have hh := weighted_sewn_nat_translation H h P t₀ ζ (x:ℂ) n N
  simpa only [weightedDifference,Complex.ofReal_zero,mul_zero,add_zero] using hh

theorem actual_log_multiplier_bound
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    |Real.log (multiplier s a)|≤1 := by
  have hθ : θ≤1 := by nlinarith [hc.very_strong_width,hc.height_large,Real.pi_lt_four]
  rw [←abs_neg,←hc.theta_actual,abs_of_pos hc.theta_pos]
  exact hθ

theorem exists_actual_physical_lift_integral
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P₀ H : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P₀)
    (P : Space) (t₀ ζ : ℂ) (hH : 1≤H) (ht₀ : t₀.im=height θ/2)
    (hP : ∀n : ℤ, n<0 → P n=0) (hPn : ‖P‖≤1) (hζ : ‖ζ‖≤1) :
    ∃N : ℕ,
      (∀x : ℝ, 0≤x → x≤1 →
        sewnCoordinate H (height θ) P t₀ ζ ((N:ℂ)+(x:ℂ))∈regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor ∧
        principalKoenigsLift s a Kneser.RealNormalizationAnchor.realAnchor
          (regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor
            (sewnCoordinate H (height θ) P t₀ ζ ((N:ℂ)+(x:ℂ))))=
              sewnCoordinate H (height θ) P t₀ ζ ((N:ℂ)+(x:ℂ))) ∧
      ∀n : ℤ,
        (∫x : ℝ in (0:ℝ)..1,
          (principalKoenigsLift s a Kneser.RealNormalizationAnchor.realAnchor
            (regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor
              (sewnCoordinate H (height θ) P t₀ ζ ((N:ℂ)+(x:ℂ))))-
                ((N:ℂ)+(x:ℂ))) * Complex.exp (-Kneser.fourierFrequency n*((N:ℂ)+(x:ℂ))))=
          gateFourierCoefficient n 0 (sewnCoordinate H (height θ) P t₀ ζ) := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hr := Kneser.NormalizedGrowingFourier.actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P₀ hc
  have hanchor : -1<Kneser.RealNormalizationAnchor.realAnchor := by
    unfold Kneser.RealNormalizationAnchor.realAnchor
    linarith [Real.exp_pos (-1)]
  have hd : a-Kneser.RealNormalizationAnchor.realAnchor<1 := by linarith [hc.left_neg]
  have hh : 0<height θ := by unfold height; exact div_pos (by positivity) hc.theta_pos
  have hzi := (Complex.abs_im_le_norm ζ).trans hζ
  have hgap : 0≤H+(normalizingCentre (height θ) t₀+ζ).im := by
    simp only [normalizingCentre,Complex.add_im,Complex.sub_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    rw [ht₀]
    linarith [neg_le_abs ζ.im]
  exact exists_genuine_physical_lift_integral s a _ H (height θ) P t₀ ζ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1
    hr hd (actual_log_multiplier_bound e₁ e₂ A B Γ s a b θ Y η M P₀ hc) hP hPn hζ hgap

end Kneser.ActualRegularTimeLift
end
