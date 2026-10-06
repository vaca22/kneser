import Kneser.ActualKoenigsIdentification
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
The normalized actual Koenigs function is analytic and injective on a
genuine complex Apollonius petal. This domain has no bound on the argument
of the cross ratio and includes the attracting root itself.
-/

noncomputable section

namespace Kneser.PositiveKoenigsPetal

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.RealExponentialPetal Kneser.ApolloniusGeometry
open scoped Topology

def petal (Q : QuotientControl) (s a b R : ℝ) : Set ℂ :=
  {u | u ≠ (b : ℂ) ∧ ‖crossRatio a b u‖ < Real.exp (-(timeScale Q ((1 - s) * (b - a)) * R))}

theorem analyticAt_koenigsValue_of_actual_limit (s a : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a)
    (hμ1 : multiplier s a < 1)
    (horbit : Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)))
    (hsum : ∀ᶠ v : ℂ in 𝓝 u, Summable (fun n => ‖increment s a v n‖)) :
    AnalyticAt ℂ (koenigsValue s a) u := by
  obtain ⟨δ, hδ, hhol, _hzero, _hder, _hrest⟩ :=
    exists_actual_local_koenigs s a hs hs1 ha ha0 hroot hμ hμ1
  obtain ⟨N, hN⟩ := (horbit.eventually (ball_mem_nhds (a : ℂ) hδ)).exists
  have hfinite : AnalyticAt ℂ (fun v => orbit v s N) u :=
    (Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s N).differentiableOn.analyticAt
      (show (Set.univ : Set ℂ) ∈ 𝓝 u from Filter.univ_mem)
  have hcomp : AnalyticAt ℂ (fun v => koenigsValue s a (orbit v s N)) u :=
    (hhol _ hN).comp (f := fun v : ℂ => orbit v s N) hfinite
  have hpne : (multiplier s a : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hμ)
  apply ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((multiplier s a : ℂ) ^ N)⁻¹) u).mul hcomp).congr
  filter_upwards [hsum] with v hv
  change ((multiplier s a : ℂ) ^ N)⁻¹ * koenigsValue s a (orbit v s N) = koenigsValue s a v
  rw [koenigsValue_iterate s a v (ne_of_gt hμ) hv N, ← mul_assoc, inv_mul_cancel₀ hpne, one_mul]

theorem analyticAt_koenigsValue_on_petal (Q : QuotientControl) (s a b R : ℝ)
    (hs : 0 < s) (hs1 : s < 1 / 2) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hRQ : 80 / Q.radius ≤ R) (hR5 : 5 ≤ R) :
    AnalyticOnNhd ℂ (koenigsValue s a) (petal Q s a b R) := by
  intro u hu
  obtain ⟨_D, _r, _hD, _hD1, _hr, _hr1, _hrμ, _hnorm, hlim, _hsum, _hap⟩ :=
    actual_koenigs_limit Q s a b R u hs hs1 ha ha0 hb hfa hfb hgap hRQ hR5 hu.1 hu.2.le
  have hcross : ContinuousAt (fun v : ℂ => crossRatio a b v) u :=
    (continuousAt_id.sub_const (a : ℂ)).div (continuousAt_id.sub_const (b : ℂ))
      (sub_ne_zero.mpr hu.1)
  have hqnear := hcross.norm.eventually (gt_mem_nhds hu.2)
  have hne : ∀ᶠ v : ℂ in 𝓝 u, v ≠ (b : ℂ) := continuousAt_id.eventually_ne hu.1
  have hsum : ∀ᶠ v : ℂ in 𝓝 u, Summable (fun n => ‖increment s a v n‖) := by
    filter_upwards [hqnear, hne] with v hv hvb
    obtain ⟨_D, _r, _hD, _hD1, _hr, _hr1, _hrμ, _hnorm, _hlim, hsum, _hap⟩ :=
      actual_koenigs_limit Q s a b R v hs hs1 ha ha0 hb hfa hfb hgap hRQ hR5 hvb hv.le
    exact hsum
  have hμ : 0 < multiplier s a := by dsimp [multiplier]; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by dsimp [multiplier]; nlinarith
  exact analyticAt_koenigsValue_of_actual_limit s a u hs.le (by linarith) ha ha0.le hfa hμ hμ1 hlim hsum

theorem exists_local_koenigs_injective (s a : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ InjOn (koenigsValue s a) (ball (a : ℂ) δ) := by
  obtain ⟨δ, hδ, hhol, _hzero, hder, _hrest⟩ :=
    exists_actual_local_koenigs s a hs hs1 ha ha0 hroot hμ hμ1
  have haA := hhol (a : ℂ) (mem_ball_self hδ)
  have hd : HasStrictDerivAt (koenigsValue s a) 1 (a : ℂ) := by
    simpa only [hder.deriv] using haA.hasStrictDerivAt
  obtain ⟨ε, hε, hleft⟩ := Metric.eventually_nhds_iff.mp (hd.eventually_left_inverse (by norm_num))
  refine ⟨ε, hε, ?_⟩
  intro u hu v hv heq
  rw [← hleft hu, ← hleft hv, heq]

theorem unfolding_injective_on_unit_root_ball (s a : ℝ) (u v : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1)
    (hu : ‖u - (a : ℂ)‖ ≤ 1) (hv : ‖v - (a : ℂ)‖ ≤ 1)
    (heq : unfolding s u = unfolding s v) : u = v := by
  have himu : |u.im| ≤ 1 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (u - (a : ℂ))).trans hu
  have himv : |v.im| ≤ 1 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (v - (a : ℂ))).trans hv
  have him (w : ℂ) (hw : |w.im| ≤ 1) :
      |(-(s : ℂ) + (1 - (s : ℂ)) * w).im| ≤ 1 := by
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
      Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, sub_zero, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos (by linarith : 0 < 1 - s)]
    nlinarith
  have he : Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * u) =
      Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * v) := by
    unfold unfolding at heq
    exact sub_left_injective heq
  have hx := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (show -Real.pi < (-(s : ℂ) + (1 - (s : ℂ)) * u).im by
      have hh := (abs_le.mp (him u himu)).1; linarith [Real.two_le_pi])
    (show (-(s : ℂ) + (1 - (s : ℂ)) * u).im ≤ Real.pi by
      have hh := (abs_le.mp (him u himu)).2; linarith [Real.two_le_pi])
    (show -Real.pi < (-(s : ℂ) + (1 - (s : ℂ)) * v).im by
      have hh := (abs_le.mp (him v himv)).1; linarith [Real.two_le_pi])
    (show (-(s : ℂ) + (1 - (s : ℂ)) * v).im ≤ Real.pi by
      have hh := (abs_le.mp (him v himv)).2; linarith [Real.two_le_pi]) he
  have hcoef : 1 - (s : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast (by linarith : 1 - s ≠ 0)
  exact mul_left_cancel₀ hcoef (add_left_cancel hx)

/-- Injectivity is pulled back from the normalized local Koenigs germ
through true finite exponential orbits. -/
theorem injOn_koenigsValue_on_petal (Q : QuotientControl) (s a b R : ℝ)
    (hs : 0 < s) (hs1 : s < 1 / 2) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hRQ : 80 / Q.radius ≤ R) (hR5 : 5 ≤ R) :
    InjOn (koenigsValue s a) (petal Q s a b R) := by
  have hμ : 0 < multiplier s a := by dsimp [multiplier]; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a < 1 := by dsimp [multiplier]; nlinarith
  obtain ⟨δ, hδ, hinj⟩ := exists_local_koenigs_injective s a hs.le (by linarith)
    ha ha0.le hfa hμ hμ1
  intro u hu v hv heq
  obtain ⟨Du, ru, hDu, hDu1, hru, hru1, _hruμ, hnu, hlu, hsu, _hau⟩ :=
    actual_koenigs_limit Q s a b R u hs hs1 ha ha0 hb hfa hfb hgap hRQ hR5 hu.1 hu.2.le
  obtain ⟨Dv, rv, hDv, hDv1, hrv, hrv1, _hrvμ, hnv, hlv, hsv, _hav⟩ :=
    actual_koenigs_limit Q s a b R v hs hs1 ha ha0 hb hfa hfb hgap hRQ hR5 hv.1 hv.2.le
  have hnormu (n : ℕ) : ‖orbit u s n - (a : ℂ)‖ ≤ 1 :=
    (hnu n).trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ hru.le hru1.le) hDu).trans
      (by simpa using hDu1))
  have hnormv (n : ℕ) : ‖orbit v s n - (a : ℂ)‖ ≤ 1 :=
    (hnv n).trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ hrv.le hrv1.le) hDv).trans
      (by simpa using hDv1))
  obtain ⟨N, huN, hvN⟩ := ((hlu.eventually (ball_mem_nhds (a : ℂ) hδ)).and
    (hlv.eventually (ball_mem_nhds (a : ℂ) hδ))).exists
  have hKN : koenigsValue s a (orbit u s N) = koenigsValue s a (orbit v s N) := by
    rw [koenigsValue_iterate s a u (ne_of_gt hμ) hsu N,
      koenigsValue_iterate s a v (ne_of_gt hμ) hsv N, heq]
  have hN : orbit u s N = orbit v s N := hinj huN hvN hKN
  have hpull : ∀ n : ℕ, orbit u s n = orbit v s n → u = v := by
    intro n
    induction n with
    | zero => simpa only [orbit_zero] using (fun h : orbit u s 0 = orbit v s 0 => h)
    | succ n ih =>
      intro he
      rw [orbit_succ, orbit_succ] at he
      exact ih (unfolding_injective_on_unit_root_ball s a (orbit u s n) (orbit v s n)
        hs.le (by linarith) (hnormu n) (hnormv n) he)
  exact hpull N hN

theorem koenigsValue_ne_zero_on_petal (Q : QuotientControl) (s a b R : ℝ)
    (hs : 0 < s) (hs1 : s < 1 / 2) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hRQ : 80 / Q.radius ≤ R) (hR5 : 5 ≤ R)
    (u : ℂ) (hu : u ∈ petal Q s a b R) (hua : u ≠ (a : ℂ)) :
    koenigsValue s a u ≠ 0 := by
  have hab : (a : ℂ) ≠ (b : ℂ) := by exact_mod_cast (by linarith : a ≠ b)
  have hap : (a : ℂ) ∈ petal Q s a b R := by
    refine ⟨hab, ?_⟩
    simp only [crossRatio, sub_self, zero_div, norm_zero]
    exact Real.exp_pos _
  intro he
  apply hua
  exact injOn_koenigsValue_on_petal Q s a b R hs hs1 ha ha0 hb hfa hfb hgap hRQ hR5
    hu hap (he.trans (koenigsValue_at_root s a hfa).symm)

end Kneser.PositiveKoenigsPetal

end
