import Kneser.ParabolicInitialPetal
import Kneser.PreparedLocalAbel
import Mathlib.Analysis.SpecificLimits.Normed

/-!
The Koenigs approximation is the actual normalized exponential orbit.
Its convergence is proved from the genuine exponential quadratic remainder;
the positive-parameter petal supplies the required geometric orbit rate.
-/

noncomputable section

namespace Kneser.PositiveKoenigsOrbit

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ParabolicExponentialOrbit Kneser.RealExponentialPetal
open Kneser.ApolloniusGeometry
open scoped Topology BigOperators

def multiplier (s a : ℝ) : ℝ := (1 - s) * (1 + a)

def approximation (s a : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  ((multiplier s a : ℂ) ^ n)⁻¹ * (orbit u s n - (a : ℂ))

def increment (s a : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  approximation s a u (n + 1) - approximation s a u n

def koenigsValue (s a : ℝ) (u : ℂ) : ℂ :=
  u - (a : ℂ) + ∑' n : ℕ, increment s a u n

/-- This bound is for the actual family and its actual fixed point. -/
theorem actual_quadratic_remainder (s a : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hu : ‖u - (a : ℂ)‖ ≤ 1) :
    ‖unfolding s u - (a : ℂ) - (multiplier s a : ℂ) * (u - (a : ℂ))‖ ≤
      ‖u - (a : ℂ)‖ ^ 2 := by
  have he : Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * (a : ℂ)) = 1 + (a : ℂ) := by
    change Complex.exp _ - 1 = _ at hroot
    linear_combination hroot
  have hn : ‖1 - (s : ℂ)‖ = 1 - s := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  have hz : ‖(1 - (s : ℂ)) * (u - (a : ℂ))‖ ≤ 1 := by
    rw [norm_mul, hn]
    nlinarith [norm_nonneg (u - (a : ℂ))]
  have hb := Complex.norm_exp_sub_one_sub_id_le hz
  have hf : unfolding s u - (a : ℂ) - (multiplier s a : ℂ) * (u - (a : ℂ)) =
      (1 + (a : ℂ)) * (Complex.exp ((1 - (s : ℂ)) * (u - (a : ℂ))) - 1 -
        (1 - (s : ℂ)) * (u - (a : ℂ))) := by
    unfold unfolding multiplier
    push_cast
    have hex : -(s : ℂ) + (1 - (s : ℂ)) * u =
        (-(s : ℂ) + (1 - (s : ℂ)) * (a : ℂ)) +
          (1 - (s : ℂ)) * (u - (a : ℂ)) := by ring
    rw [hex, Complex.exp_add, he]
    ring
  rw [hf, norm_mul]
  have hna : ‖1 + (a : ℂ)‖ = 1 + a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_of_nonneg (by linarith)]
  rw [hna]
  calc
    _ ≤ (1 + a) * ‖(1 - (s : ℂ)) * (u - (a : ℂ))‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    _ ≤ ‖(1 - (s : ℂ)) * (u - (a : ℂ))‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by linarith)
    _ ≤ ‖u - (a : ℂ)‖ ^ 2 := by
      rw [norm_mul, hn]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [norm_nonneg (u - (a : ℂ))]

theorem approximation_increment (s a : ℝ) (u : ℂ) (n : ℕ)
    (hμ : multiplier s a ≠ 0) :
    increment s a u n = ((multiplier s a : ℂ) ^ (n + 1))⁻¹ *
      (orbit u s (n + 1) - (a : ℂ) -
        (multiplier s a : ℂ) * (orbit u s n - (a : ℂ))) := by
  have hμc : (multiplier s a : ℂ) ≠ 0 := by exact_mod_cast hμ
  unfold increment approximation
  rw [pow_succ]
  field_simp

theorem increment_norm_bound (s a D r : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a)
    (hD : 0 ≤ D) (hD1 : D ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (horbit : ∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ D * r ^ n) (n : ℕ) :
    ‖increment s a u n‖ ≤ D ^ 2 / multiplier s a *
      (r ^ 2 / multiplier s a) ^ n := by
  have hu : ‖orbit u s n - (a : ℂ)‖ ≤ 1 :=
    (horbit n).trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) hD).trans (by simpa using hD1))
  have hb := actual_quadratic_remainder s a (orbit u s n) hs hs1 ha ha0 hroot hu
  rw [← orbit_succ] at hb
  have hsq : ‖orbit u s n - (a : ℂ)‖ ^ 2 ≤ (D * r ^ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (horbit n) 2
  rw [approximation_increment s a u n (ne_of_gt hμ), norm_mul, norm_inv, norm_pow,
    Complex.norm_of_nonneg hμ.le]
  calc
    _ ≤ (multiplier s a ^ (n + 1))⁻¹ * (D * r ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_left (hb.trans hsq) (by positivity)
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, div_pow, pow_succ]
      field_simp

theorem summable_norm_increment (s a D r : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a)
    (hD : 0 ≤ D) (hD1 : D ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrμ : r ^ 2 < multiplier s a)
    (horbit : ∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ D * r ^ n) :
    Summable (fun n => ‖increment s a u n‖) := by
  have hp : 0 ≤ r ^ 2 / multiplier s a := by positivity
  have hp1 : r ^ 2 / multiplier s a < 1 := (div_lt_one hμ).mpr hrμ
  exact ((summable_geometric_of_lt_one hp hp1).mul_left (D ^ 2 / multiplier s a)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (increment_norm_bound s a D r u hs hs1 ha ha0 hroot hμ hD hD1 hr hr1 horbit)

theorem approximation_eq_partial_sum (s a : ℝ) (u : ℂ) (n : ℕ) :
    approximation s a u n = u - (a : ℂ) + ∑ k ∈ Finset.range n, increment s a u k := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih]; unfold increment; ring

/-- The displayed orbit, not an arbitrary auxiliary sequence, converges
to the constructed absolutely convergent correction series. -/
theorem tendsto_approximation (s a : ℝ) (u : ℂ)
    (hsum : Summable (fun n => ‖increment s a u n‖)) :
    Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) := by
  have ht : Tendsto (fun n : ℕ => u - (a : ℂ) +
      ∑ k ∈ Finset.range n, increment s a u k) atTop (𝓝 (koenigsValue s a u)) :=
    tendsto_const_nhds.add hsum.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall fun n => (approximation_eq_partial_sum s a u n).symm)

theorem distance_bound_from_crossRatio (a b u : ℂ) (q₀ q : ℝ)
    (_hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1) (hq : 0 ≤ q) (hqq₀ : q ≤ q₀)
    (hub : u ≠ b) (hcross : ‖crossRatio a b u‖ ≤ q) :
    ‖u - a‖ ≤ ‖b - a‖ / (1 - q₀) * q := by
  have hun : u - b ≠ 0 := sub_ne_zero.mpr hub
  have hmul : crossRatio a b u * (u - b) = u - a := by
    dsimp [crossRatio]
    exact div_mul_cancel₀ _ hun
  have hgap : (1 - crossRatio a b u) * (u - b) = a - b := by
    rw [sub_mul, hmul]
    ring
  have hlower : 1 - q₀ ≤ ‖1 - crossRatio a b u‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (crossRatio a b u)
    rw [norm_one] at ht
    linarith
  have hnormb : ‖u - b‖ ≤ ‖b - a‖ / (1 - q₀) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - q₀)).mpr
    have hm := mul_le_mul_of_nonneg_right hlower (norm_nonneg (u - b))
    have hgn : ‖1 - crossRatio a b u‖ * ‖u - b‖ = ‖b - a‖ := by
      rw [← norm_mul, hgap, norm_sub_rev]
    rw [hgn] at hm
    nlinarith
  rw [← hmul, norm_mul]
  exact (mul_le_mul hcross hnormb (norm_nonneg _) hq).trans (by ring_nf; rfl)

/-- Genuine exponential convergence to the attracting root.  The rate is
strong enough to make normalized Koenigs increments absolutely summable. -/
theorem actual_koenigs_limit (Q : QuotientControl) (s a b R : ℝ) (u : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hR : 80 / Q.radius ≤ R) (hR5 : 5 ≤ R)
    (hub : u ≠ (b : ℂ))
    (hq : ‖crossRatio a b u‖ ≤ Real.exp (-(timeScale Q ((1 - s) * (b - a)) * R))) :
    ∃ D r : ℝ, 0 ≤ D ∧ D ≤ 1 ∧ 0 < r ∧ r < 1 ∧ r ^ 2 < multiplier s a ∧
      (∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ D * r ^ n) ∧
      Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)) ∧
      Summable (fun n => ‖increment s a u n‖) ∧
      Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)) := by
  have hab : a < b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs' hab hκr
  let θ := timeScale Q ((1 - s) * (b - a))
  let q₀ := Real.exp (-(θ * R))
  let r := Real.exp (-(3 / 4) * θ)
  let D := (b - a) / (1 - q₀) * q₀
  have hRpos : 0 < R := by linarith
  have hq₀ : 0 < q₀ := Real.exp_pos _
  have hq₀1 : q₀ < 1 := Real.exp_lt_one_iff.mpr (by dsimp [θ]; nlinarith)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by dsimp [θ]; linarith)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hD1 : D ≤ 1 := by
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (θ * R)) hq₀.le
    have hunit : Real.exp (θ * R) * q₀ = 1 := by
      dsimp [q₀]
      rw [← Real.exp_add]
      simp
    rw [hunit] at he
    have hsmall : q₀ / (1 - q₀) ≤ 1 / (θ * R) := by
      apply (div_le_div_iff₀ (by linarith) (mul_pos hθ hRpos)).mpr
      nlinarith
    have hDr : D ≤ ((b - a) / θ) / R := by
      calc
        D = (b - a) * (q₀ / (1 - q₀)) := by dsimp [D]; ring
        _ ≤ (b - a) * (1 / (θ * R)) := mul_le_mul_of_nonneg_left hsmall hd.le
        _ = _ := by ring
    exact hDr.trans ((div_le_div_of_nonneg_right hratio hRpos.le).trans
      ((div_le_one hRpos).mpr hR5))
  have hnorm : ∀ n : ℕ, ‖orbit u s n - (a : ℂ)‖ ≤ D * r ^ n := by
    intro n
    obtain ⟨hne, hn⟩ := infinite_orbit_crossRatio_bound Q s a b R u
      hs hs' hab hb hroota hrootb hgap hR hub hq n
    have hex : Real.exp (-(θ * (R + (3 / 4) * (n : ℝ)))) = q₀ * r ^ n := by
      dsimp [q₀, r]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    change ‖crossRatio a b (orbit u s n)‖ ≤ Real.exp (-(θ * (R + (3 / 4) * (n : ℝ)))) at hn
    rw [hex] at hn
    have hnq : q₀ * r ^ n ≤ q₀ := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1.le) hq₀.le).trans (by simp)
    have hh := distance_bound_from_crossRatio (a : ℂ) b (orbit u s n) q₀ (q₀ * r ^ n)
      hq₀.le hq₀1 (by positivity) hnq hne hn
    have hgapnorm : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
      rw [← Complex.ofReal_sub, Complex.norm_of_nonneg hd.le]
    rw [hgapnorm] at hh
    exact hh.trans (by dsimp [D]; ring_nf; rfl)
  have hμ : 0 < multiplier s a := by
    dsimp [multiplier]
    exact mul_pos (by linarith) (by linarith)
  have hθeq := timeScale_eq_neg_log_multiplier Q s a b (by linarith) ha hab hroota hrootb
  have hμexp : multiplier s a = Real.exp (-θ) := by
    dsimp [θ]
    rw [hθeq, neg_neg]
    simpa only [multiplier] using (Real.exp_log hμ).symm
  have hrμ : r ^ 2 < multiplier s a := by
    rw [hμexp]
    dsimp [r]
    rw [pow_two, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by dsimp [θ]; linarith)
  have hsum := summable_norm_increment s a D r u hs.le (by linarith) ha ha0.le
    hroota hμ hD hD1 hr.le hr1.le hrμ hnorm
  have hzero : Tendsto (fun n : ℕ => D * r ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul D
  have hnormzero : Tendsto (fun n : ℕ => ‖orbit u s n - (a : ℂ)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hnorm hzero
  have horbit : Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnormzero
  exact ⟨D, r, hD, hD1, hr, hr1, hrμ, hnorm, horbit, hsum,
    tendsto_approximation s a u hsum⟩

theorem approximation_forward (s a : ℝ) (u : ℂ) (n : ℕ)
    (hμ : multiplier s a ≠ 0) :
    approximation s a (unfolding s u) n =
      (multiplier s a : ℂ) * approximation s a u (n + 1) := by
  have hμc : (multiplier s a : ℂ) ≠ 0 := by exact_mod_cast hμ
  unfold approximation
  rw [Kneser.PreparedLocalAbel.orbit_shift, pow_succ]
  field_simp

theorem increment_forward (s a : ℝ) (u : ℂ) (n : ℕ)
    (hμ : multiplier s a ≠ 0) :
    increment s a (unfolding s u) n = (multiplier s a : ℂ) * increment s a u (n + 1) := by
  unfold increment
  rw [approximation_forward s a u (n + 1) hμ, approximation_forward s a u n hμ]
  ring

theorem summable_norm_increment_forward (s a : ℝ) (u : ℂ)
    (hμ : multiplier s a ≠ 0) (hsum : Summable (fun n => ‖increment s a u n‖)) :
    Summable (fun n => ‖increment s a (unfolding s u) n‖) := by
  have hshift : Summable (fun n => ‖increment s a u (n + 1)‖) :=
    hsum.comp_injective (fun n m h => by omega)
  simpa only [increment_forward s a u _ hμ, norm_mul] using
    hshift.mul_left ‖(multiplier s a : ℂ)‖

/-- The linearizing identity is obtained by uniqueness of limits of the
actual normalized forward orbits. -/
theorem koenigsValue_functional_eq (s a : ℝ) (u : ℂ)
    (hμ : multiplier s a ≠ 0) (hsum : Summable (fun n => ‖increment s a u n‖)) :
    koenigsValue s a (unfolding s u) = (multiplier s a : ℂ) * koenigsValue s a u := by
  have hsumf := summable_norm_increment_forward s a u hμ hsum
  have ht := ((tendsto_approximation s a u hsum).comp (tendsto_add_atTop_nat 1)).const_mul
    (multiplier s a : ℂ)
  exact tendsto_nhds_unique (tendsto_approximation s a (unfolding s u) hsumf)
    (ht.congr' (Eventually.of_forall fun n => (approximation_forward s a u n hμ).symm))

theorem koenigsValue_iterate (s a : ℝ) (u : ℂ)
    (hμ : multiplier s a ≠ 0) (hsum : Summable (fun n => ‖increment s a u n‖)) :
    ∀ n : ℕ, koenigsValue s a (orbit u s n) =
      (multiplier s a : ℂ) ^ n * koenigsValue s a u := by
  have hsumN : ∀ n : ℕ, Summable (fun k => ‖increment s a (orbit u s n) k‖) := by
    intro n
    induction n with
    | zero => exact hsum
    | succ n ih => exact summable_norm_increment_forward s a (orbit u s n) hμ ih
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, koenigsValue_functional_eq s a _ hμ (hsumN n), ih, pow_succ]
    ring

end Kneser.PositiveKoenigsOrbit

end
