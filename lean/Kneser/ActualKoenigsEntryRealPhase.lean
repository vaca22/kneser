import Kneser.ActualKoenigsRealPhase

/-! Genuine finite entry into the proved attracting petal gives the actual
Koenigs sum, its orbit limit, and the exact normalized real phase. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualKoenigsEntryRealPhase
open Set Metric Complex Filter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualKoenigsRealPhase Kneser.RealExponentialPetal
open Kneser.ApolloniusGeometry
open scoped Topology

theorem actual_orbit_add (u s : ℂ) (N k : ℕ) :
    orbit (orbit u s N) s k=orbit u s (k+N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [orbit_succ,ih]
    simpa only [Nat.succ_add] using (orbit_succ u s (k+N)).symm

theorem summable_increment_backward (s a : ℝ) (u : ℂ)
    (hμ : multiplier s a≠0)
    (hsum : Summable (fun n => ‖increment s a (unfolding s u) n‖)) :
    Summable (fun n => ‖increment s a u n‖) := by
  have hnorm : ‖(multiplier s a:ℂ)‖≠0 := norm_ne_zero_iff.mpr (by exact_mod_cast hμ)
  have hm : Summable (fun n => ‖(multiplier s a:ℂ)‖*‖increment s a u (n+1)‖) := by
    simpa only [increment_forward s a u _ hμ,norm_mul] using hsum
  have hshift : Summable (fun n => ‖increment s a u (n+1)‖) :=
    (summable_mul_left_iff hnorm).mp hm
  exact (summable_nat_add_iff 1).mp hshift

theorem summable_increment_from_entry (s a : ℝ) (u : ℂ) (N : ℕ)
    (hμ : multiplier s a≠0)
    (hsum : Summable (fun n => ‖increment s a (orbit u s N) n‖)) :
    Summable (fun n => ‖increment s a u n‖) := by
  induction N with
  | zero => simpa using hsum
  | succ N ih =>
    apply ih
    apply summable_increment_backward s a (orbit u s N) hμ
    simpa only [orbit_succ] using hsum

theorem orbit_limit_from_entry (s a : ℝ) (u : ℂ) (N : ℕ)
    (hlim : Tendsto (fun k => orbit (orbit u s N) s k) atTop (𝓝 (a:ℂ))) :
    Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ)) := by
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [actual_orbit_add] using hlim

/-- Actual convergence gives finite entry into the genuine local Koenigs
construction, and hence absolute convergence of the original orbit sum. -/
theorem actual_koenigs_sum_of_orbit_limit (s a : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ))) :
    Summable (fun k => ‖increment s a u k‖) := by
  obtain ⟨δ,hδ,_hhol,_hz,_hd,hlocal⟩ :=
    Kneser.PositiveLocalKoenigs.exists_actual_local_koenigs s a hs hs1 ha ha0 hfa hμ hμ1
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds (a:ℂ) hδ)).exists
  exact summable_increment_from_entry s a u N (ne_of_gt hμ) (hlocal _ hN).1

/-- The only entrance condition is an actual finite iterate satisfying the
already proved quantitative petal inequality. Neither summability nor a
Koenigs limit is imposed. -/
theorem actual_koenigs_from_petal_entry (Q : QuotientControl) (s a b R : ℝ)
    (u : ℂ) (N : ℕ)
    (hs : 0<s) (hs1 : s<1/2) (ha : -1<a) (ha0 : a<0) (hb : 0<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hgap : b-a<Q.radius/8) (hR : 80/Q.radius≤R) (hR5 : 5≤R)
    (hne : orbit u s N≠(b:ℂ))
    (hq : ‖crossRatio a b (orbit u s N)‖≤
      Real.exp (-(timeScale Q ((1-s)*(b-a))*R))) :
    Summable (fun k => ‖increment s a u k‖) ∧
    Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ)) ∧
    Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) := by
  obtain ⟨D,r,_hD,_hD1,_hr,_hr1,_hrμ,_hb,hlim,hsum,_happrox⟩ :=
    actual_koenigs_limit Q s a b R (orbit u s N) hs hs1 ha ha0 hb hfa hfb
      hgap hR hR5 hne hq
  have hμ : multiplier s a≠0 := by
    unfold multiplier
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  have hsum0 := summable_increment_from_entry s a u N hμ hsum
  exact ⟨hsum0,orbit_limit_from_entry s a u N hlim,tendsto_approximation s a u hsum0⟩

/-- Exact upper half-period for a real interval point and a real anchor,
both obtained by genuine finite orbit entry. -/
theorem normalizedUpperTime_from_true_entries (Q : QuotientControl)
    (s a b R r r₀ : ℝ) (N N₀ : ℕ)
    (hs : 0<s) (hs1 : s<1/2) (ha : -1<a) (ha0 : a<0) (hb : 0<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hgap : b-a<Q.radius/8) (hR : 80/Q.radius≤R) (hR5 : 5≤R)
    (hne : orbit (r:ℂ) s N≠(b:ℂ))
    (hq : ‖crossRatio a b (orbit (r:ℂ) s N)‖≤
      Real.exp (-(timeScale Q ((1-s)*(b-a))*R)))
    (hne₀ : orbit (r₀:ℂ) s N₀≠(b:ℂ))
    (hq₀ : ‖crossRatio a b (orbit (r₀:ℂ) s N₀)‖≤
      Real.exp (-(timeScale Q ((1-s)*(b-a))*R)))
    (har : a<r) (hrb : r<b) (hr₀ : r₀<a) :
    (normalizedUpperTime s a r r₀).im=Real.pi/(-Real.log (multiplier s a)) ∧
    Complex.exp ((Real.log (multiplier s a):ℂ)*normalizedUpperTime s a r r₀)=
      koenigsValue s a (r:ℂ)/koenigsValue s a (r₀:ℂ) ∧
    normalizedUpperTime s a (Kneser.RealLensMidline.realStep s r) r₀=
      normalizedUpperTime s a r r₀+1 := by
  obtain ⟨hSr,hLr,_hAr⟩ := actual_koenigs_from_petal_entry Q s a b R r N
    hs hs1 ha ha0 hb hfa hfb hgap hR hR5 hne hq
  obtain ⟨hS₀,hL₀,_hA₀⟩ := actual_koenigs_from_petal_entry Q s a b R r₀ N₀
    hs hs1 ha ha0 hb hfa hfb hgap hR hR5 hne₀ hq₀
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by
    unfold multiplier
    nlinarith
  have hr := koenigsValue_positive_between s a b r hs.le (by linarith) ha ha0.le
    hfa hfb hμ hμ1 hSr hLr har hrb
  have hr₀s := koenigsValue_negative_left s a r₀ hs.le (by linarith) ha ha0.le
    hfa hμ hμ1 hS₀ hL₀ hr₀
  have hKr : koenigsValue s a (r:ℂ)≠0 := by intro he; rw [he] at hr; simpa using hr.2
  have hK₀ : koenigsValue s a (r₀:ℂ)≠0 := by intro he; rw [he] at hr₀s; simpa using hr₀s.2
  exact ⟨normalizedUpperTime_half_height s a r r₀ hμ hμ1 hr hr₀s,
    normalizedUpperTime_exponential s a r r₀ hμ hμ1 hKr hK₀,
    normalizedUpperTime_real_step_abel s a r r₀ hμ hμ1 hSr hKr hK₀⟩

end Kneser.ActualKoenigsEntryRealPhase
end
