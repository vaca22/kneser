import Kneser.PositiveLocalKoenigs
import Kneser.PreparedParabolicAbel

/-!
The normalized logarithm of the genuine Koenigs orbit limit is an Abel
time. The paired prepared model has the same actual orbit limit up to an
explicit constant at the second root and the polynomial correction.
-/

noncomputable section

namespace Kneser.PositiveKoenigsAbel

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.PositiveLocalKoenigs Kneser.ExponentialModelTime
open Kneser.ExponentialPreparedModel Kneser.PreparedActualFirstOrder
open Kneser.EvenPreparedOrbitDiscs
open scoped Topology BigOperators

def koenigsTime (s a : ℝ) (u : ℂ) : ℂ :=
  Complex.log (-koenigsValue s a u) / (Real.log (multiplier s a) : ℂ)

def pairedModel (s a b : ℝ) (e₁ e₂ : ℂ) (u : ℂ) : ℂ :=
  Complex.log ((a : ℂ) - u) / (Real.log (multiplier s a) : ℂ) +
    Complex.log ((b : ℂ) - u) / (Real.log (multiplier s b) : ℂ) + e₁ * u + e₂ * u ^ 2

def modelConstant (s a b : ℝ) (e₁ e₂ : ℂ) : ℂ :=
  Complex.log ((b : ℂ) - (a : ℂ)) / (Real.log (multiplier s b) : ℂ) +
    e₁ * (a : ℂ) + e₂ * (a : ℂ) ^ 2

theorem unfolding_left_of_root (s a : ℝ) (u : ℂ)
    (hs : s < 1) (hroot : unfolding s a = (a : ℂ)) (hu : u.re < a) :
    (unfolding s u).re < a := by
  have he : Real.exp (-s + (1 - s) * a) - 1 = a := by
    have h := congrArg Complex.re hroot
    have hc : -(s : ℂ) + (1 - (s : ℂ)) * (a : ℂ) = ((-s + (1 - s) * a : ℝ) : ℂ) := by
      push_cast
      ring
    simpa only [unfolding, hc, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.exp_ofReal_re] using h
  have harg : (-s + (1 - s) * u).re < -s + (1 - s) * a := by
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im,
      sub_zero, zero_mul, sub_self]
    nlinarith
  have hn : (Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * u)).re < 1 + a :=
    (Complex.re_le_norm _).trans_lt (by
      rw [Complex.norm_exp]
      have hh := Real.exp_lt_exp.mpr harg
      linarith)
  simpa only [unfolding, Complex.sub_re, Complex.one_re] using (show
    (Complex.exp (-(s : ℂ) + (1 - (s : ℂ)) * u)).re - 1 < a by linarith)

theorem orbit_left_of_root (s a : ℝ) (u : ℂ)
    (hs : s < 1) (hroot : unfolding s a = (a : ℂ)) (hu : u.re < a) :
    ∀ n : ℕ, (orbit u s n).re < a := by
  intro n
  induction n with
  | zero => exact hu
  | succ n ih => exact unfolding_left_of_root s a (orbit u s n) hs hroot ih

/-- The branch condition for the logarithm is a conclusion of the actual
left-half-plane dynamics and the normalized local Koenigs derivative. -/
theorem actual_koenigs_branch (s a : ℝ) (u : ℂ)
    (hs : 0 ≤ s) (hs1 : s < 1) (ha : -1 < a) (ha0 : a ≤ 0)
    (hroot : unfolding s a = (a : ℂ)) (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1)
    (hsum : Summable (fun n => ‖increment s a u n‖))
    (horbit : Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)))
    (hu : u.re < a) : koenigsValue s a u ≠ 0 ∧ -koenigsValue s a u ∈ Complex.slitPlane := by
  obtain ⟨δ, hδ, _hhol, _hzero, hder, _hrest⟩ :=
    exists_actual_local_koenigs s a hs hs1 ha ha0 hroot hμ hμ1
  have hnear : ∀ᶠ v : ℂ in 𝓝 (a : ℂ), v ≠ (a : ℂ) → koenigsValue s a v ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp (hder.eventually_ne (c := (0 : ℂ)) (by norm_num)))
  have hleft := orbit_left_of_root s a u hs1 hroot hu
  obtain ⟨N, hN⟩ := (horbit.eventually hnear).exists
  have hentry : koenigsValue s a (orbit u s N) ≠ 0 := hN (by
    intro he
    have hh := hleft N
    rw [he] at hh
    simp at hh)
  have hK : koenigsValue s a u ≠ 0 := by
    intro he
    rw [koenigsValue_iterate s a u (ne_of_gt hμ) hsum N, he, mul_zero] at hentry
    exact hentry rfl
  have happrox := tendsto_approximation s a u hsum
  have hreal : ∀ n : ℕ, 0 ≤ (-approximation s a u n).re := by
    intro n
    have heq : -approximation s a u n =
        (((multiplier s a ^ n)⁻¹ : ℝ) : ℂ) * ((a : ℂ) - orbit u s n) := by
      simp only [approximation, Complex.ofReal_inv, Complex.ofReal_pow]
      ring
    rw [heq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re]
    exact mul_nonneg (by positivity) (by
      linarith [hleft n])
  have hnonneg : 0 ≤ (-koenigsValue s a u).re :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp happrox.neg)
      (Eventually.of_forall hreal)
  refine ⟨hK, Complex.mem_slitPlane_iff.mpr ?_⟩
  by_cases him : (-koenigsValue s a u).im = 0
  · left
    apply lt_of_le_of_ne hnonneg
    intro hre
    have hzero : -koenigsValue s a u = 0 := Complex.ext hre.symm him
    exact hK (neg_eq_zero.mp hzero)
  · exact Or.inr him

theorem koenigsTime_abel (s a : ℝ) (u : ℂ)
    (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1)
    (hsum : Summable (fun n => ‖increment s a u n‖)) (hK : koenigsValue s a u ≠ 0) :
    koenigsTime s a (unfolding s u) = koenigsTime s a u + 1 := by
  have hl : Real.log (multiplier s a) ≠ 0 := ne_of_lt (Real.log_neg hμ hμ1)
  have hlc : (Real.log (multiplier s a) : ℂ) ≠ 0 := by exact_mod_cast hl
  unfold koenigsTime
  rw [koenigsValue_functional_eq s a u (ne_of_gt hμ) hsum]
  rw [show -((multiplier s a : ℂ) * koenigsValue s a u) =
      (multiplier s a : ℂ) * -koenigsValue s a u by ring,
    Complex.log_ofReal_mul hμ (neg_ne_zero.mpr hK)]
  field_simp
  ring

theorem pairedModel_orbit_limit (s a b : ℝ) (e₁ e₂ : ℂ) (u : ℂ)
    (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1) (hab : a < b)
    (horbit : Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)))
    (happrox : Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)))
    (hslit : -koenigsValue s a u ∈ Complex.slitPlane) :
    Tendsto (fun n : ℕ => pairedModel s a b e₁ e₂ (orbit u s n) - (n : ℂ))
      atTop (𝓝 (koenigsTime s a u + modelConstant s a b e₁ e₂)) := by
  have hμc : (multiplier s a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hμ
  have hl : Real.log (multiplier s a) ≠ 0 := ne_of_lt (Real.log_neg hμ hμ1)
  have hlc : (Real.log (multiplier s a) : ℂ) ≠ 0 := by exact_mod_cast hl
  have hKne : -koenigsValue s a u ≠ 0 := Complex.slitPlane_ne_zero hslit
  have haLog := happrox.neg.clog hslit
  have hbslit : (b : ℂ) - (a : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hbLog := (tendsto_const_nhds.sub horbit).clog hbslit
  have ht := ((haLog.div_const (Real.log (multiplier s a) : ℂ)).add
    (hbLog.div_const (Real.log (multiplier s b) : ℂ))).add
      ((horbit.const_mul e₁).add ((horbit.pow 2).const_mul e₂))
  have ht' : Tendsto (fun n : ℕ =>
      Complex.log (-approximation s a u n) / (Real.log (multiplier s a) : ℂ) +
        Complex.log ((b : ℂ) - orbit u s n) / (Real.log (multiplier s b) : ℂ) +
          (e₁ * orbit u s n + e₂ * orbit u s n ^ 2)) atTop
      (𝓝 (koenigsTime s a u + modelConstant s a b e₁ e₂)) := by
    convert ht using 1
    dsimp [koenigsTime, modelConstant]
    congr 1
    ring
  apply ht'.congr'
  filter_upwards [happrox.neg.eventually_ne hKne] with n hn
  have hp : (a : ℂ) - orbit u s n = (multiplier s a : ℂ) ^ n * -approximation s a u n := by
    unfold approximation
    field_simp
    ring
  have hpReal : (multiplier s a : ℂ) ^ n = (multiplier s a ^ n : ℝ) := by simp
  have hlog : Complex.log ((a : ℂ) - orbit u s n) =
      (n : ℂ) * (Real.log (multiplier s a) : ℂ) + Complex.log (-approximation s a u n) := by
    rw [hp, hpReal, Complex.log_ofReal_mul (pow_pos hμ n) hn, Real.log_pow]
    push_cast
    rfl
  unfold pairedModel
  rw [hlog]
  field_simp
  ring

theorem prepared_positive_telescoping (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s : ℝ) (u : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ s (orbit u s (k + 1)) -
        preparedModelTime U H e₁ e₂ s (orbit u s k) - 1 = descendedTerm A B Γ 2 u s k)
    (n : ℕ) :
    preparedModelTime U H e₁ e₂ s u + ∑ k ∈ Finset.range n, descendedTerm A B Γ 2 u s k =
      preparedModelTime U H e₁ e₂ s (orbit u s n) - (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h := hdefect n
    push_cast
    linear_combination -h

theorem actualPreparedCoordinate_positive_limit (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (s : ℝ) (u : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ s (orbit u s (k + 1)) -
        preparedModelTime U H e₁ e₂ s (orbit u s k) - 1 = descendedTerm A B Γ 2 u s k)
    (hs : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖)) :
    Tendsto (fun n : ℕ => preparedModelTime U H e₁ e₂ s (orbit u s n) - (n : ℂ))
      atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u s)) := by
  have ht : Tendsto
      (fun n : ℕ => preparedModelTime U H e₁ e₂ s u + ∑ k ∈ Finset.range n, descendedTerm A B Γ 2 u s k)
      atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u s)) :=
    tendsto_const_nhds.add hs.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall (prepared_positive_telescoping U H e₁ e₂ A B Γ s u hdefect))

/-- The residue pair and one-step residual identity are preparation inputs;
no identity with a Koenigs coordinate is an assumption. -/
theorem prepared_eq_koenigs_of_residue_pair (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (s a b : ℝ) (u : ℂ)
    (hμ : 0 < multiplier s a) (hμ1 : multiplier s a < 1) (hab : a < b)
    (horbit : Tendsto (fun n : ℕ => orbit u s n) atTop (𝓝 (a : ℂ)))
    (happrox : Tendsto (approximation s a u) atTop (𝓝 (koenigsValue s a u)))
    (hslit : -koenigsValue s a u ∈ Complex.slitPlane)
    (hpair : ∀ v : ℂ, preparedModelTime U H e₁ e₂ s v =
      pairedModel s a b (e₁ s) (e₂ s) v)
    (hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ s (orbit u s (k + 1)) -
        preparedModelTime U H e₁ e₂ s (orbit u s k) - 1 = descendedTerm A B Γ 2 u s k)
    (hs : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖)) :
    actualPreparedCoordinate U H e₁ e₂ A B Γ u s =
      koenigsTime s a u + modelConstant s a b (e₁ s) (e₂ s) := by
  have hlim := pairedModel_orbit_limit s a b (e₁ s) (e₂ s) u hμ hμ1 hab horbit happrox hslit
  exact tendsto_nhds_unique (actualPreparedCoordinate_positive_limit U H e₁ e₂ A B Γ s u hdefect hs)
    (hlim.congr' (Eventually.of_forall fun n => by simp only [hpair]))

end Kneser.PositiveKoenigsAbel

end
